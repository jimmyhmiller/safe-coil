#lang racket
;; The static rules of safe Coil, as a PLT Redex model.
;;
;; Storable types (σ) are what memory can hold: plain data, owners (a box is a
;; heap allocation freed when its owner goes out of scope; a pool owns its
;; elements), structs and sums of those, raw pointers, handles, type parameters.
;; Second-class types are references and views (a struct with reference
;; fields): a local, an argument or a result, never stored.
;;
;; The judgment is algorithmic:   (chk Σ Γ Λ e τ L Γ′)
;;   Σ   where we are: the declarations, the function's type parameters, whether
;;       inside `unsafe`, whether inside a loop
;;   Γ   each variable in scope, its type, and whether it has been moved
;;   Λ   the loans alive here: who holds each, on which place, shared or exclusive
;;   τ   the type of e
;;   L   the loans the VALUE of e carries (empty unless τ is second-class)
;;   Γ′  Γ after e's moves
;; Λ is an input only: a loan lives exactly as long as the scope of its holder.
(require redex/reduction-semantics)
(provide Safe chk check-program check-fn mutant mutants
         make-Σ fields-of variants-of subst copy? second-class? exclusive?)

;; Testing the tests: with one part of one rule left out, the random search must
;; find a program that goes wrong. Never set in a real check. The value is also
;; the first element of Σ, so an answer Redex remembers is never given under a
;; different setting.
(define mutant (make-parameter #f))
(define mutants
  '((no-exclusive "nothing is checked against the loans alive")
    (no-escape "a reference may leave the scope of what it refers to")
    (no-moves "a moved variable can still be used")
    (no-call-loans "a returned reference carries no loans from the call's arguments")
    (no-arg-loans "an argument's loans are not alive while later arguments are evaluated")
    (no-return-check "a function may return a reference to its own storage")
    (no-let-loans "a let-bound reference holds no loans")
    (write-through-shared "a place behind a shared reference can be written")
    (copy-mut "an exclusive reference is copied, not moved")
    (no-join "a move in a later branch is forgotten")
    (no-union "the loans of a later branch are forgotten")
    (no-subplace "a loan on part of a place does not protect the whole")
    (copy-struct "a struct or sum holding an owner is copied, not moved")
    (copy-typevar "a value of a type parameter is copied, not moved")
    (loop-moves "a loop may move a variable from outside it")
    (match-no-loans "a match arm's reference holds no loan on the matched place")
    (no-elem-loans "a reference to a pool element does not lock the pool")
    (view-no-loans "a view carries no loans from the references it was built from")
    (view-field-escape "a reference to a view's own field may outlive the view")
    (global-escape "a reference to a global may leave its `with`")
    (par-split "the two calls of a par are checked apart")
    (spawn-ref "a thread is given a reference")
    (dead-source "a reference lent again is forgotten once its own name is no longer used")
    (raw-anywhere "a raw pointer is read outside unsafe")))
(define (mutant? m) (eq? (mutant) m))

(define-language Safe
  (prog ::= (program (decl ...) e))
  (decl ::= (struct S (T ...) ((fld σ) ...))
            (sum S (T ...) ((K σ) (K σ) ...))
            (view V ((fld ρ) ...))
            (global g σ e)
            (defn f (T ...) ((x τ) ...) τ e))
  ;; storable types; what a view's field can be; all types
  (σ ::= int unit (box σ) (ptr σ) (pool σ) (handle σ) (task σ) (S σ ...) T)
  (ρ ::= σ (ref σ) (mut σ))
  (τ ::= ρ (view V))
  (e ::= n unit p
         (let ([x e]) e) (seq e e) (if0 e e e) (+ e e)
         (while e e) (break)
         (box e) (unbox e) (ref p) (mut p) (set! p e) (take p e)
         (new τ e ...) (inj σ K e)
         (match e ((K x) e) ...) (match-ref p ((K x) e) ...) (match-mut p ((K x) e) ...)
         (pool-new σ) (insert p e) (remove p x)
         (call f (σ ...) e ...)
         (par (call f (σ ...) e ...) (call f (σ ...) e ...))
         (spawn (call f (σ ...) e ...)) (join e)
         (with w g x e)
         (unsafe e) (addr p) (load e) (store e e) (alloc e) (free e))
  ;; a variable, what a box or reference points at, a field, a pool element
  (p ::= x (* p) (: p fld) (at p x))
  (n ::= integer)
  (w ::= ref mut)
  (k ::= shr mut)
  (s ::= live moved)
  (Γ ::= ((x τ s) ...))
  ;; a loan's place is rooted at a local, at what a reference parameter refers
  ;; to, or at a global; every element of a pool is one place
  (q ::= x (ext x) (glob g) (* q) (: q fld) (elem q))
  (L ::= ((q k) ...))
  (h ::= x tmp)
  (Λ ::= ((h q k) ...))
  (Σ ::= any)
  (x f g S T V K fld ::= variable-not-otherwise-mentioned))

;; ---------------------------------------------------------------- Σ

;; The declarations ride in Σ inside a struct, which Redex compares and hashes
;; by identity: it looks Σ up in a table on every step, and hashing the whole
;; program each time was most of the cost of a check.
(struct program-decls (list))
(define (make-Σ decls [Ts '()]) (list (mutant) 'safe 'noloop Ts (program-decls decls) '()))
(define (in-unsafe? Σ) (eq? (second Σ) 'unsafe))
(define (in-loop? Σ) (eq? (third Σ) 'loop))
(define (tparams Σ) (fourth Σ))
(define (decls-of Σ) (program-decls-list (fifth Σ)))
(define (Σ-unsafe Σ) (list (first Σ) 'unsafe (third Σ) (fourth Σ) (fifth Σ) (sixth Σ)))
(define (Σ-loop Σ) (list (first Σ) (second Σ) 'loop (fourth Σ) (fifth Σ) (sixth Σ)))
;; The variables that what runs after the expression being checked still names.
(define (Σ-live Σ) (sixth Σ))
;; Σ for an expression that the expressions `later` run after.
(define (Σ+ Σ . later)
  (list (first Σ) (second Σ) (third Σ) (fourth Σ) (fifth Σ)
        (remove-duplicates (append (append-map uses later) (sixth Σ)))))

;; Σ for an expression that each of the expressions `laters` runs after. A list
;; of expressions is not an expression: `(x y)` is two variables, where a form
;; headed by a name is that form.
(define (Σ+* Σ laters) (apply Σ+ Σ laters))

;; The variables an expression or a place names. A binder is
;; named too, which is harmless: no two variables of a function share a name.
(define (uses t)
  (match t
    [(? symbol? x) (if (memq x '(unit)) '() (list x))]
    [(? number?) '()]
    [`(: ,p ,_) (uses p)]
    [`(at ,p ,x) (cons x (uses p))]
    [`(let ([,x ,e1]) ,e2) (cons x (append (uses e1) (uses e2)))]
    [`(new ,_ ,es ...) (append-map uses es)]
    [`(inj ,_ ,_ ,e) (uses e)]
    [`(,(or 'match 'match-ref 'match-mut) ,e ((,_ ,xs) ,es) ...)
     (append (uses e) xs (append-map uses es))]
    [`(pool-new ,_) '()]
    [`(remove ,p ,x) (cons x (uses p))]
    [`(call ,_ ,_ ,es ...) (append-map uses es)]
    [`(with ,_ ,_ ,x ,e) (cons x (uses e))]
    [`(break) '()]
    [(cons (? symbol?) rest) (append-map uses rest)]
    [_ (error 'uses "not an expression: ~a" t)]))
(define (find-decl Σ kind name)
  (for/first ([d (decls-of Σ)] #:when (and (eq? (car d) kind) (eq? (cadr d) name))) d))

;; ---------------------------------------------------------------- types

(define (subst τ Ts σs)
  (match τ
    [(? symbol? t) (let ([i (index-of Ts t)]) (if i (list-ref σs i) t))]
    [`(view ,_) τ]
    [(cons head args) (cons head (for/list ([a args]) (subst a Ts σs)))]))

;; -> ((fld τ) ...) for a struct or view type, else #f
(define (fields-of Σ τ)
  (match τ
    [`(view ,V) (match (find-decl Σ 'view V) [`(view ,_ ,fields) fields] [_ #f])]
    [(cons (? symbol? S) args)
     (match (find-decl Σ 'struct S)
       [`(struct ,_ ,Ts ((,fs ,ts) ...))
        (and (= (length Ts) (length args))
             (for/list ([f fs] [t ts]) (list f (subst t Ts args))))]
       [_ #f])]
    [_ #f]))

;; -> ((K σ) ...) for a sum type, else #f
(define (variants-of Σ τ)
  (match τ
    [(cons (? symbol? S) args)
     (match (find-decl Σ 'sum S)
       [`(sum ,_ ,Ts ((,Ks ,ts) ...))
        (and (= (length Ts) (length args))
             (for/list ([K Ks] [t ts]) (list K (subst t Ts args))))]
       [_ #f])]
    [_ #f]))
(define (variant-type Σ τ K)
  (match (assq K (or (variants-of Σ τ) '())) [(list _ t) t] [_ #f]))

;; every name in the type is declared, with the right number of arguments
(define (wf? Σ τ)
  (match τ
    [(or 'int 'unit) #t]
    [(? symbol? t) (and (memq t (tparams Σ)) #t)]
    [`(,(or 'box 'ptr 'pool 'handle 'task 'ref 'mut) ,σ) (wf? Σ σ)]
    [`(view ,V) (and (find-decl Σ 'view V) #t)]
    [(cons (? symbol? S) args)
     (let ([d (or (find-decl Σ 'struct S) (find-decl Σ 'sum S))])
       (and d (= (length (caddr d)) (length args)) (andmap (λ (a) (wf? Σ a)) args)))]
    [_ #f]))

(define (second-class? τ) (match τ [`(,(or 'ref 'mut 'view) ,_) #t] [_ #f]))
;; a second-class value that cannot be copied: it gives exclusive access
(define (exclusive? Σ τ)
  (match τ
    [`(mut ,_) #t]
    [`(view ,_) (for/or ([f (fields-of Σ τ)]) (match (cadr f) [`(mut ,_) #t] [_ #f]))]
    [_ #f]))
(define (kind-of Σ τ) (if (exclusive? Σ τ) 'mut 'shr))

;; a storable type whose values own nothing. A type parameter may stand for an owner.
(define (copy? Σ σ [seen '()])
  (match σ
    [(or 'int 'unit) #t]
    [(? symbol?) (mutant? 'copy-typevar)]
    [`(,(or 'ptr 'handle) ,_) #t]
    [`(,(or 'box 'pool 'task) ,_) #f]
    [_ (let ([parts (or (fields-of Σ σ) (variants-of Σ σ))])
         (and parts
              (not (member σ seen))
              (or (mutant? 'copy-struct)
                  (for/and ([part parts]) (copy? Σ (cadr part) (cons σ seen))))))]))

;; ---------------------------------------------------------------- places

(define (lookup Γ x)
  (match (assq x Γ)
    [(list _ τ 'live) τ]
    [(list _ τ 'moved) (if (mutant? 'no-moves) τ #f)]
    [_ #f]))

(define (place-type Σ Γ p)
  (match p
    [(? symbol? x) (lookup Γ x)]
    [`(* ,p2) (match (place-type Σ Γ p2)
                [`(,(or 'box 'ref 'mut) ,σ) σ]
                [_ #f])]
    [`(: ,p2 ,fld) (let* ([t (place-type Σ Γ p2)]
                          [fs (and t (fields-of Σ t))])
                     (match (and fs (assq fld fs)) [(list _ ft) ft] [_ #f]))]
    [`(at ,p2 ,x) (match (place-type Σ Γ p2)
                    [`(pool ,σ) (and (equal? (lookup Γ x) `(handle ,σ)) σ)]
                    [_ #f])]))

;; the place a loan names: which element of a pool is not known
(define (norm p)
  (match p
    [(? symbol?) p]
    [`(* ,p2) `(* ,(norm p2))]
    [`(: ,p2 ,fld) `(: ,(norm p2) ,fld)]
    [`(at ,p2 ,_) `(elem ,(norm p2))]))
(define (index-vars p)
  (match p
    [(? symbol?) '()]
    [`(at ,p2 ,x) (cons x (index-vars p2))]
    [`(,_ ,p2 . ,_) (index-vars p2)]))
(define (has-at? p) (pair? (index-vars p)))
(define (place-root q)
  (match q
    [`(,(or '* 'elem) ,q2) (place-root q2)]
    [`(,(or ': 'at) ,q2 ,_) (place-root q2)]
    [_ q]))
(define (through-deref? q)
  (match q
    [`(* ,_) #t]
    [`(elem ,q2) (through-deref? q2)]
    [`(: ,q2 ,_) (through-deref? q2)]
    [_ #f]))

;; a place can be written when no step of its path goes through a shared reference
(define (writable? Σ Γ p)
  (match p
    [(? symbol?) #t]
    [`(* ,p2) (and (or (mutant? 'write-through-shared)
                       (match (place-type Σ Γ p2) [`(,(or 'box 'mut) ,_) #t] [_ #f]))
                   (writable? Σ Γ p2))]
    [`(,_ ,p2 ,_) (writable? Σ Γ p2)]))
(define (through-shared? Σ Γ p)
  (match p
    [(? symbol?) #f]
    [`(* ,p2) (or (match (place-type Σ Γ p2) [`(ref ,_) #t] [_ #f]) (through-shared? Σ Γ p2))]
    [`(,_ ,p2 ,_) (through-shared? Σ Γ p2)]))

;; ---------------------------------------------------------------- loans

;; a is b or a place b is inside
(define (prefix? a b)
  (or (equal? a b)
      (match b
        [`(,(or '* 'elem) ,b2) (prefix? a b2)]
        [`(: ,b2 ,_) (prefix? a b2)]
        [_ #f])))
;; does a loan on `lent` concern a use of `used`?
(define (overlap? lent used)
  (or (prefix? lent used) (and (not (mutant? 'no-subplace)) (prefix? used lent))))

;; A loan counts for as long as its holder is still named by what runs later.
;; A view that is moved holds its loans until its scope ends: dropping it may
;; use what it borrowed. A reference lent again keeps its source's loans alive,
;; since the new reference reaches what the source did.
(define (active Σ Γ Λ)
  (define later (Σ-live Σ))
  (define (kept? h)
    (or (memq h later)
        (match (assq h Γ)
          [(list _ τ _) (or (not (second-class? τ))
                            (match τ [`(view ,_) (exclusive? Σ τ)] [_ #f]))]
          [_ #t])))
  (define holders (remove-duplicates (map car Λ)))
  (define live
    (let grow ([live (filter kept? holders)])
      (define more
        (if (mutant? 'dead-source)
            '()
            (for/list ([l Λ]
                       #:when (and (memq (car l) live)
                                   (symbol? (place-root (cadr l)))
                                   (memq (place-root (cadr l)) holders)
                                   (not (memq (place-root (cadr l)) live))))
              (place-root (cadr l)))))
      (if (null? more) live (grow (remove-duplicates (append more live))))))
  (filter (λ (l) (memq (car l) live)) Λ))

(define (free-of? Λ q kinds)
  (or (mutant? 'no-exclusive)
      (for/and ([l Λ]) (match l [(list _ q2 k) (not (and (memq k kinds) (overlap? q2 q)))]))))
;; reading p: nobody holds an exclusive loan on any part of it, nor on a handle
;; used to find it
(define (read-ok? Λ p)
  (and (free-of? Λ (norm p) '(mut))
       (for/and ([x (index-vars p)]) (free-of? Λ x '(mut)))))
;; writing, moving or exclusively borrowing p: nobody holds any loan on any part of it
(define (write-ok? Λ p)
  (and (free-of? Λ (norm p) '(shr mut))
       (for/and ([x (index-vars p)]) (free-of? Λ x '(mut)))))

(define (loans-of Λ x)
  (remove-duplicates (for/list ([l Λ] #:when (eq? (car l) x)) (cdr l))))
(define (add-loans Λ h L)
  (append (for/list ([l L]) (cons h l)) Λ))
(define (union L1 L2) (remove-duplicates (append L1 L2)))

;; the loans a shared borrow of p carries: through a shared reference, the loans
;; of whoever holds that reference; otherwise a shared loan on p itself
(define (shared-loans Σ Γ Λ p)
  (cond [(and (mutant? 'no-elem-loans) (has-at? p)) '()]
        [(through-shared? Σ Γ p) (loans-of Λ (place-root p))]
        [else `((,(norm p) shr))]))
(define (exclusive-loans p)
  (if (and (mutant? 'no-elem-loans) (has-at? p)) '() `((,(norm p) mut))))

;; x of type τ leaves scope while a value carrying L leaves with it. A loan on
;; x's own storage cannot leave (#f). A loan on something x refers to becomes
;; x's loans.
(define (exit-scope x τ Λ L)
  (let loop ([L L] [acc '()])
    (match L
      ['() (remove-duplicates (reverse acc))]
      [(cons (list q k) rest)
       (cond [(not (eq? (place-root q) x)) (loop rest (cons (list q k) acc))]
             [(and (second-class? τ) (or (through-deref? q) (mutant? 'view-field-escape)))
              (loop rest (append (reverse (loans-of Λ x)) acc))]
             [(mutant? 'no-escape) (loop rest acc)]
             [else #f])])))

;; a global is lent for the body of a `with` and no longer
(define (exit-global x g L)
  (define (bad? l) (member (place-root (car l)) (list x `(glob ,g))))
  (cond [(not (ormap bad? L)) L]
        [(or (mutant? 'global-escape) (mutant? 'no-escape)) (filter (negate bad?) L)]
        [else #f]))

(define (mark-moved Γ x)
  (if (mutant? 'no-moves)
      Γ
      (for/list ([b Γ]) (if (eq? (car b) x) (list x (cadr b) 'moved) b))))
;; the type of x when it is a variable that was moved out of, else #f
(define (moved-type Γ x)
  (match (assq x Γ)
    [(list _ τ 'moved) (and (not (second-class? τ)) τ)]
    [_ #f]))
(define (mark-live Γ x)
  (for/list ([b Γ]) (if (eq? (car b) x) (list x (cadr b) 'live) b)))
(define (remove-var Γ x) (filter (λ (b) (not (eq? (car b) x))) Γ))
(define (join Γ1 Γ2)
  (for/list ([a Γ1] [b Γ2])
    (list (car a) (cadr a) (if (and (eq? (caddr a) 'live) (eq? (caddr b) 'live)) 'live 'moved))))

;; what naming a place as a value does
;;   copy   plain data is copied             move   an owner is moved (variables only)
;;   copy2  a shared reference or view is copied, loans and all
;;   move2  an exclusive one is moved
(define (read-kind Σ Γ p)
  (define τ (place-type Σ Γ p))
  (cond [(not τ) #f]
        [(second-class? τ) (if (exclusive? Σ τ) (and (symbol? p) 'move2) 'copy2)]
        [(copy? Σ τ) 'copy]
        [(symbol? p) 'move]
        [else #f]))

;; ---------------------------------------------------------------- the rules

(define-judgment-form Safe
  #:mode (chk I I I I O O O)
  #:contract (chk Σ Γ Λ e τ L Γ)

  [-------------------------------------------- "int"
   (chk Σ Γ Λ n int () Γ)]

  [-------------------------------------------- "unit"
   (chk Σ Γ Λ unit unit () Γ)]

  [(chk ,(Σ+ (term Σ) (term e_2)) Γ Λ e_1 int L_1 Γ_1)
   (chk Σ Γ_1 Λ e_2 int L_2 Γ_2)
   -------------------------------------------- "add"
   (chk Σ Γ Λ (+ e_1 e_2) int () Γ_2)]

  [(side-condition ,(eq? 'copy (read-kind (term Σ) (term Γ) (term p))))
   (where σ ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   -------------------------------------------- "copy"
   (chk Σ Γ Λ p σ () Γ)]

  ;; only a whole variable can be moved; `take` gets an owner out of anywhere else
  [(side-condition ,(eq? 'move (read-kind (term Σ) (term Γ) (term x))))
   (where σ ,(place-type (term Σ) (term Γ) (term x)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term x)))
   (where Γ_1 ,(mark-moved (term Γ) (term x)))
   -------------------------------------------- "move"
   (chk Σ Γ Λ x σ () Γ_1)]

  [(side-condition ,(eq? 'copy2 (read-kind (term Σ) (term Γ) (term p))))
   (where τ ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where L ,(loans-of (term Λ) (place-root (term p))))
   -------------------------------------------- "copy-ref"
   (chk Σ Γ Λ p τ L Γ)]

  ;; an exclusive reference is moved, and must not be reborrowed at the time
  [(side-condition ,(eq? 'move2 (read-kind (term Σ) (term Γ) (term x))))
   (where τ ,(place-type (term Σ) (term Γ) (term x)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term x)))
   (where L ,(loans-of (term Λ) (term x)))
   (where Γ_1 ,(if (mutant? 'copy-mut) (term Γ) (mark-moved (term Γ) (term x))))
   -------------------------------------------- "move-mut"
   (chk Σ Γ Λ x τ L Γ_1)]

  [(where σ ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where L ,(shared-loans (term Σ) (term Γ) (term Λ) (term p)))
   -------------------------------------------- "borrow"
   (chk Σ Γ Λ (ref p) (ref σ) L Γ)]

  [(where σ ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where L ,(exclusive-loans (term p)))
   -------------------------------------------- "borrow-mut"
   (chk Σ Γ Λ (mut p) (mut σ) L Γ)]

  [(chk Σ Γ Λ e σ () Γ_1)
   -------------------------------------------- "box"
   (chk Σ Γ Λ (box e) (box σ) () Γ_1)]

  [(chk Σ Γ Λ e (box σ) () Γ_1)
   -------------------------------------------- "unbox"
   (chk Σ Γ Λ (unbox e) σ () Γ_1)]

  ;; the loans of e_1's value belong to x, and count while x is still named
  [(chk ,(Σ+ (term Σ) (term e_2)) Γ Λ e_1 τ_1 L_1 Γ_1)
   (side-condition ,(not (assq (term x) (term Γ_1))))
   (where Λ_2 ,(add-loans (term Λ) (term x) (if (mutant? 'no-let-loans) '() (term L_1))))
   (where Γ_b ,(cons (term (x τ_1 live)) (term Γ_1)))
   (chk Σ Γ_b Λ_2 e_2 τ_2 L_2 Γ_2)
   (where L_3 ,(exit-scope (term x) (term τ_1) (term Λ_2) (term L_2)))
   (where Γ_3 ,(remove-var (term Γ_2) (term x)))
   -------------------------------------------- "let"
   (chk Σ Γ Λ (let ([x e_1]) e_2) τ_2 L_3 Γ_3)]

  [(chk ,(Σ+ (term Σ) (term e_2)) Γ Λ e_1 τ_1 L_1 Γ_1)
   (chk Σ Γ_1 Λ e_2 τ_2 L_2 Γ_2)
   -------------------------------------------- "seq"
   (chk Σ Γ Λ (seq e_1 e_2) τ_2 L_2 Γ_2)]

  ;; the new value is computed first; then the place must be whole, reachable
  ;; for writing, and free of loans, because its old value is dropped
  [(chk ,(Σ+ (term Σ) (term p)) Γ Λ e σ () Γ_1)
   (where σ ,(place-type (term Σ) (term Γ_1) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ_1) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ_1) (term Λ)) (term p)))
   -------------------------------------------- "set"
   (chk Σ Γ Λ (set! p e) unit () Γ_1)]

  ;; a variable that was moved out of holds nothing to drop, so nothing can be
  ;; lent from it: giving it a value makes it whole again
  [(chk ,(Σ+ (term Σ) (term x)) Γ Λ e σ () Γ_1)
   (where σ ,(moved-type (term Γ_1) (term x)))
   (where Γ_2 ,(mark-live (term Γ_1) (term x)))
   -------------------------------------------- "set-moved"
   (chk Σ Γ Λ (set! x e) unit () Γ_2)]

  ;; the same, and the old value is the result instead of being dropped
  [(chk ,(Σ+ (term Σ) (term p)) Γ Λ e σ () Γ_1)
   (where σ ,(place-type (term Σ) (term Γ_1) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ_1) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ_1) (term Λ)) (term p)))
   -------------------------------------------- "take"
   (chk Σ Γ Λ (take p e) σ () Γ_1)]

  [(chk ,(Σ+ (term Σ) (term e_2) (term e_3)) Γ Λ e_1 int L_1 Γ_1)
   (chk Σ Γ_1 Λ e_2 τ L_2 Γ_2)
   (chk Σ Γ_1 Λ e_3 τ L_3 Γ_3)
   (where L ,(if (mutant? 'no-union) (term L_2) (union (term L_2) (term L_3))))
   (where Γ_4 ,(if (mutant? 'no-join) (term Γ_2) (join (term Γ_2) (term Γ_3))))
   -------------------------------------------- "if0"
   (chk Σ Γ Λ (if0 e_1 e_2 e_3) τ L Γ_4)]

  ;; A loop's body may run again, so it leaves every outer variable as it found
  ;; it. A break then needs no state of its own.
  ;; What the loop names is named again by its next turn.
  [(chk ,(Σ+ (term Σ) (term e_c) (term e_b)) Γ Λ e_c int L_c Γ_1)
   (chk ,(Σ-loop (Σ+ (term Σ) (term e_c) (term e_b))) Γ_1 Λ e_b τ_b L_b Γ_2)
   (side-condition ,(or (mutant? 'loop-moves) (equal? (term Γ_2) (term Γ))))
   -------------------------------------------- "while"
   (chk Σ Γ Λ (while e_c e_b) unit () Γ_2)]

  [(side-condition ,(in-loop? (term Σ)))
   -------------------------------------------- "break"
   (chk Σ Γ Λ (break) unit () Γ)]

  ;; ---- structs, views, sums

  [(side-condition ,(wf? (term Σ) (term σ)))
   (where ((fld τ_f) ...) ,(fields-of (term Σ) (term σ)))
   (chk-args Σ Γ Λ (e ...) (τ_f ...) L Γ_1)
   -------------------------------------------- "new"
   (chk Σ Γ Λ (new σ e ...) σ () Γ_1)]

  ;; a view borrows from every reference it is built from
  [(where ((fld τ_f) ...) ,(fields-of (term Σ) (term (view V))))
   (chk-args Σ Γ Λ (e ...) (τ_f ...) L Γ_1)
   (where L_v ,(if (mutant? 'view-no-loans) '() (term L)))
   -------------------------------------------- "new-view"
   (chk Σ Γ Λ (new (view V) e ...) (view V) L_v Γ_1)]

  [(side-condition ,(wf? (term Σ) (term σ)))
   (where σ_K ,(variant-type (term Σ) (term σ) (term K)))
   (chk Σ Γ Λ e σ_K () Γ_1)
   -------------------------------------------- "inj"
   (chk Σ Γ Λ (inj σ K e) σ () Γ_1)]

  ;; by value: the sum is consumed and each arm owns its payload
  [(chk ,(Σ+* (term Σ) (term (e_a ...))) Γ Λ e_s σ_s () Γ_1)
   (where ((K σ_K) ...) ,(variants-of (term Σ) (term σ_s)))
   (chk-arms Σ Γ_1 Λ (((K x) e_a) ...) (σ_K ...) () τ L Γ_2)
   -------------------------------------------- "match"
   (chk Σ Γ Λ (match e_s ((K x) e_a) ...) τ L Γ_2)]

  ;; by reference: the arm's reference keeps the matched place lent, so the
  ;; variant cannot be replaced under it. The arms run after the place is
  ;; looked at, so what they name is still named then.
  [(where σ_s ,(place-type (term Σ) (term Γ) (term p)))
   (where ((K σ_K) ...) ,(variants-of (term Σ) (term σ_s)))
   (side-condition ,(read-ok? (active (Σ+* (term Σ) (term (e_a ...))) (term Γ) (term Λ)) (term p)))
   (where L_x ,(shared-loans (term Σ) (term Γ) (term Λ) (term p)))
   (chk-arms Σ Γ Λ (((K x) e_a) ...) ((ref σ_K) ...) L_x τ L Γ_1)
   -------------------------------------------- "match-ref"
   (chk Σ Γ Λ (match-ref p ((K x) e_a) ...) τ L Γ_1)]

  [(where σ_s ,(place-type (term Σ) (term Γ) (term p)))
   (where ((K σ_K) ...) ,(variants-of (term Σ) (term σ_s)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(write-ok? (active (Σ+* (term Σ) (term (e_a ...))) (term Γ) (term Λ)) (term p)))
   (where L_x ,(exclusive-loans (term p)))
   (chk-arms Σ Γ Λ (((K x) e_a) ...) ((mut σ_K) ...) L_x τ L Γ_1)
   -------------------------------------------- "match-mut"
   (chk Σ Γ Λ (match-mut p ((K x) e_a) ...) τ L Γ_1)]

  ;; ---- pools and handles: a handle is plain data, checked when it is used

  [(side-condition ,(wf? (term Σ) (term σ)))
   -------------------------------------------- "pool-new"
   (chk Σ Γ Λ (pool-new σ) (pool σ) () Γ)]

  [(chk ,(Σ+ (term Σ) (term p)) Γ Λ e σ () Γ_1)
   (where (pool σ) ,(place-type (term Σ) (term Γ_1) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ_1) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ_1) (term Λ)) (term p)))
   -------------------------------------------- "insert"
   (chk Σ Γ Λ (insert p e) (handle σ) () Γ_1)]

  [(where (pool σ) ,(place-type (term Σ) (term Γ) (term p)))
   (where (handle σ) ,(lookup (term Γ) (term x)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term x)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   -------------------------------------------- "remove"
   (chk Σ Γ Λ (remove p x) σ () Γ)]

  ;; ---- calls

  ;; a returned reference borrows from every reference argument of the call
  [(where (defn f (T ...) ((x_p τ_p) ...) τ_r any_b) ,(find-decl (term Σ) 'defn (term f)))
   (side-condition ,(and (= (length (term (T ...))) (length (term (σ ...))))
                         (andmap (λ (t) (wf? (term Σ) t)) (term (σ ...)))))
   (where (τ_a ...) ,(for/list ([t (term (τ_p ...))]) (subst t (term (T ...)) (term (σ ...)))))
   (where τ_ra ,(subst (term τ_r) (term (T ...)) (term (σ ...))))
   (chk-args Σ Γ Λ (e ...) (τ_a ...) L Γ_1)
   (where L_r ,(if (and (second-class? (term τ_ra)) (not (mutant? 'no-call-loans))) (term L) '()))
   -------------------------------------------- "call"
   (chk Σ Γ Λ (call f (σ ...) e ...) τ_ra L_r Γ_1)]

  ;; two calls run at the same time: their arguments are checked as the
  ;; arguments of one call, so nothing lent exclusively to one reaches the other
  [(where (defn f_1 (T_1 ...) ((x_1 τ_1) ...) σ_r1 any_1) ,(find-decl (term Σ) 'defn (term f_1)))
   (where (defn f_2 (T_2 ...) ((x_2 τ_2) ...) σ_r2 any_2) ,(find-decl (term Σ) 'defn (term f_2)))
   (side-condition ,(and (= (length (term (T_1 ...))) (length (term (σ_1 ...))))
                         (= (length (term (T_2 ...))) (length (term (σ_2 ...))))
                         (andmap (λ (t) (wf? (term Σ) t)) (term (σ_1 ... σ_2 ...)))))
   (where (τ_a1 ...) ,(for/list ([t (term (τ_1 ...))]) (subst t (term (T_1 ...)) (term (σ_1 ...)))))
   (where (τ_a2 ...) ,(for/list ([t (term (τ_2 ...))]) (subst t (term (T_2 ...)) (term (σ_2 ...)))))
   (chk-args ,(Σ+* (term Σ) (term (e_2 ...))) Γ Λ (e_1 ...) (τ_a1 ...) L_1 Γ_1)
   (where Λ_2 ,(if (mutant? 'par-split) (term Λ) (add-loans (term Λ) (term tmp) (term L_1))))
   (chk-args Σ Γ_1 Λ_2 (e_2 ...) (τ_a2 ...) L_2 Γ_2)
   -------------------------------------------- "par"
   (chk Σ Γ Λ (par (call f_1 (σ_1 ...) e_1 ...) (call f_2 (σ_2 ...) e_2 ...)) unit () Γ_2)]

  ;; a call on a thread of its own, which runs on after this one goes on. It
  ;; owns what it is given: no argument is a reference or a view. The task is
  ;; an owner; joining it gives what the call returned.
  [(where (defn f (T ...) ((x_p τ_p) ...) σ_r any_b) ,(find-decl (term Σ) 'defn (term f)))
   (side-condition ,(and (= (length (term (T ...))) (length (term (σ ...))))
                         (andmap (λ (t) (wf? (term Σ) t)) (term (σ ...)))))
   (where (τ_a ...) ,(for/list ([t (term (τ_p ...))]) (subst t (term (T ...)) (term (σ ...)))))
   (side-condition ,(or (mutant? 'spawn-ref) (not (ormap second-class? (term (τ_a ...))))))
   (where σ_ra ,(subst (term σ_r) (term (T ...)) (term (σ ...))))
   (chk-args Σ Γ Λ (e ...) (τ_a ...) L Γ_1)
   -------------------------------------------- "spawn"
   (chk Σ Γ Λ (spawn (call f (σ ...) e ...)) (task σ_ra) () Γ_1)]

  [(chk Σ Γ Λ e (task σ) () Γ_1)
   -------------------------------------------- "join"
   (chk Σ Γ Λ (join e) σ () Γ_1)]

  ;; ---- globals: lent for a scope, with exclusivity checked when it is entered

  [(where (global g σ any_i) ,(find-decl (term Σ) 'global (term g)))
   (side-condition ,(not (assq (term x) (term Γ))))
   (where Λ_1 ,(cons (list (term x) (term (glob g)) (if (eq? (term w) 'mut) 'mut 'shr)) (term Λ)))
   (where Γ_b ,(cons (term (x (w σ) live)) (term Γ)))
   (chk Σ Γ_b Λ_1 e τ L Γ_1)
   (where L_2 ,(exit-global (term x) (term g) (term L)))
   (where Γ_2 ,(remove-var (term Γ_1) (term x)))
   -------------------------------------------- "with"
   (chk Σ Γ Λ (with w g x e) τ L_2 Γ_2)]

  ;; ---- raw memory: a raw pointer is plain data anywhere, and is followed only
  ;; inside `unsafe`. Every other rule still applies there.

  [(chk ,(Σ-unsafe (term Σ)) Γ Λ e τ L Γ_1)
   -------------------------------------------- "unsafe"
   (chk Σ Γ Λ (unsafe e) τ L Γ_1)]

  [(where σ ,(place-type (term Σ) (term Γ) (term p)))
   -------------------------------------------- "addr"
   (chk Σ Γ Λ (addr p) (ptr σ) () Γ)]

  [(side-condition ,(or (in-unsafe? (term Σ)) (mutant? 'raw-anywhere)))
   (chk Σ Γ Λ e (ptr σ) () Γ_1)
   -------------------------------------------- "load"
   (chk Σ Γ Λ (load e) σ () Γ_1)]

  [(side-condition ,(in-unsafe? (term Σ)))
   (chk ,(Σ+ (term Σ) (term e_2)) Γ Λ e_1 (ptr σ) () Γ_1)
   (chk Σ Γ_1 Λ e_2 σ () Γ_2)
   -------------------------------------------- "store"
   (chk Σ Γ Λ (store e_1 e_2) unit () Γ_2)]

  [(side-condition ,(in-unsafe? (term Σ)))
   (chk Σ Γ Λ e σ () Γ_1)
   -------------------------------------------- "alloc"
   (chk Σ Γ Λ (alloc e) (ptr σ) () Γ_1)]

  [(side-condition ,(in-unsafe? (term Σ)))
   (chk Σ Γ Λ e (ptr σ) () Γ_1)
   -------------------------------------------- "free"
   (chk Σ Γ Λ (free e) unit () Γ_1)])

;; arguments, left to right: each one's loans are alive while the rest are evaluated
(define-judgment-form Safe
  #:mode (chk-args I I I I I O O)
  #:contract (chk-args Σ Γ Λ (e ...) (τ ...) L Γ)

  [-------------------------------------------- "no-args"
   (chk-args Σ Γ Λ () () () Γ)]

  [(chk ,(Σ+* (term Σ) (term (e_r ...))) Γ Λ e_1 τ_1 L_1 Γ_1)
   (where Λ_1 ,(add-loans (term Λ) (term tmp) (if (mutant? 'no-arg-loans) '() (term L_1))))
   (chk-args Σ Γ_1 Λ_1 (e_r ...) (τ_r ...) L_2 Γ_2)
   (where L ,(union (term L_1) (term L_2)))
   -------------------------------------------- "arg"
   (chk-args Σ Γ Λ (e_1 e_r ...) (τ_1 τ_r ...) L Γ_2)])

;; one arm: x holds the payload (or a reference to it, carrying L_x)
(define-judgment-form Safe
  #:mode (chk-arm I I I I I I I O O O)
  #:contract (chk-arm Σ Γ Λ x τ L e τ L Γ)

  [(side-condition ,(not (assq (term x) (term Γ))))
   (where Λ_1 ,(add-loans (term Λ) (term x) (if (mutant? 'match-no-loans) '() (term L_x))))
   (where Γ_b ,(cons (term (x τ_x live)) (term Γ)))
   (chk Σ Γ_b Λ_1 e τ L_2 Γ_2)
   (where L_3 ,(exit-scope (term x) (term τ_x) (term Λ_1) (term L_2)))
   (where Γ_3 ,(remove-var (term Γ_2) (term x)))
   -------------------------------------------- "arm"
   (chk-arm Σ Γ Λ x τ_x L_x e τ L_3 Γ_3)])

;; every arm starts from the same state and gives the same type
(define-judgment-form Safe
  #:mode (chk-arms I I I I I I O O O)
  #:contract (chk-arms Σ Γ Λ (((K x) e) ...) (τ ...) L τ L Γ)

  [(chk-arm Σ Γ Λ x τ_x L_x e τ L Γ_1)
   -------------------------------------------- "last-arm"
   (chk-arms Σ Γ Λ (((K x) e)) (τ_x) L_x τ L Γ_1)]

  [(chk-arm Σ Γ Λ x τ_x L_x e τ L_1 Γ_1)
   (chk-arms Σ Γ Λ (any_a any_r ...) (τ_y τ_r ...) L_x τ L_2 Γ_2)
   (where L ,(if (mutant? 'no-union) (term L_1) (union (term L_1) (term L_2))))
   (where Γ_3 ,(if (mutant? 'no-join) (term Γ_1) (join (term Γ_1) (term Γ_2))))
   -------------------------------------------- "arms"
   (chk-arms Σ Γ Λ (((K x) e) any_a any_r ...) (τ_x τ_y τ_r ...) L_x τ L Γ_3)])

;; ---------------------------------------------------------------- programs

(define (distinct? xs) (not (check-duplicates xs)))
(define (one-answer who rs)
  (match rs
    ['() #f]
    [(list r) r]
    [_ (error who "the rules gave more than one answer: ~a" rs)]))

;; A function's second-class parameters hold loans on what the caller lent. Its
;; result may carry only those: nothing rooted at the function's own storage.
(define (check-fn decls fn)
  (match fn
    [`(defn ,_ ,Ts ,params ,τr ,body)
     (define Σ (make-Σ decls Ts))
     (and (distinct? (map car params))
          (distinct? (append Ts (map cadr decls)))
          (andmap (λ (p) (wf? Σ (cadr p))) params)
          (wf? Σ τr)
          (let* ([Γ (for/list ([p params]) (list (car p) (cadr p) 'live))]
                 [Λ (for/list ([p params] #:when (second-class? (cadr p)))
                      (list (car p) `(ext ,(car p)) (kind-of Σ (cadr p))))])
            (match (one-answer 'check-fn (judgment-holds (chk ,Σ ,Γ ,Λ ,body τ L Γ) (τ L)))
              [(list τ L)
               (and (equal? τ τr)
                    (or (mutant? 'no-return-check)
                        (for/fold ([L L]) ([p params])
                          (and L (exit-scope (car p) (cadr p) Λ L))))
                    #t)]
              [#f #f])))]))

;; a global's first value is built without running any of the program
(define (constant? e)
  (not (let loop ([t e])
         (and (pair? t)
              (or (memq (car t) '(call par spawn join with unsafe while load store alloc free))
                  (ormap loop t))))))

(define (check-decl decls d)
  (match d
    [`(,(or 'struct 'sum) ,_ ,Ts ((,names ,ts) ...))
     (and (distinct? Ts) (distinct? names)
          (distinct? (append Ts (map cadr decls)))
          (andmap (λ (t) (wf? (make-Σ decls Ts) t)) ts))]
    [`(view ,_ ((,names ,ts) ...))
     (and (distinct? names) (andmap (λ (t) (wf? (make-Σ decls) t)) ts))]
    [`(global ,_ ,σ ,e)
     (and (wf? (make-Σ decls) σ)
          (constant? e)
          (equal? (one-answer 'check-decl (judgment-holds (chk ,(make-Σ decls) () () ,e τ L Γ) τ)) σ))]
    [`(defn . ,_) (check-fn decls d)]))

(define (check-program prog)
  (match prog
    [`(program ,decls ,main)
     (and (redex-match? Safe prog prog)
          (distinct? (map cadr decls))
          (andmap (λ (d) (check-decl decls d)) decls)
          (match (one-answer 'check-program (judgment-holds (chk ,(make-Σ decls) () () ,main τ L Γ) (τ L)))
            [(list τ '()) (not (second-class? τ))]
            [_ #f]))]
    [_ #f]))
