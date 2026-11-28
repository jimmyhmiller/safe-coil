#lang racket
;; The static rules of safe Coil, as a PLT Redex model.
;;
;; Storable types (σ) are what memory can hold: plain data, owners (a box is a
;; heap allocation freed when its owner goes out of scope; a pool owns its
;; elements), structs and sums of those, raw pointers, handles, type parameters.
;; Second-class types are references, views (a struct with reference
;; fields) and closures that borrow what they capture: a local, an argument or a
;; result, never stored. A closure that owns what it captures is storable.
;;
;; The judgment is algorithmic:   (chk Σ Γ Λ e τ L Γ′)
;;   Σ   where we are: the declarations, the function's type parameters, whether
;;       inside `unsafe`, whether inside a loop
;;   Γ   each variable in scope, its type, which parts of it have been moved, and
;;       what was moved on the way to each `break` of the loop being checked
;;   Λ   the loans alive here: who holds each, on which place, shared or exclusive
;;   τ   the type of e
;;   L   the loans the VALUE of e carries (empty unless τ is second-class)
;;   Γ′  Γ after e's moves
;; Λ is an input only: a loan lives exactly as long as the scope of its holder.
(require redex/reduction-semantics)
(provide Safe chk check-program check-fn mutant mutants
         make-Σ fields-of variants-of subst copy? copy-shape? second-class? exclusive? view-drop
         droppable-of)

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
    (raw-anywhere "a raw pointer is read outside unsafe")
    (clo-no-loans "a closure carries no loans from what it captures")
    (clo-shared-call "calling a closure that captured exclusively does not lend it exclusively")
    (clo-moves "an owning closure's body may move what it captured")
    (clo-own-ref "an owning closure may capture a reference")
    (drop-view-unpinned "a view that is dropped lets its loans go at its last use")
    (part-unmarked "moving part of a variable is not remembered")
    (set-inside-moved "a part of something moved away can be assigned")
    (no-restore "a function may leave part of what an exclusive parameter refers to moved")
    (break-forgets "what a loop moved before a break is forgotten after the loop")
    (return-escape "a value returned early may hold a loan on the function's own storage")
    (out-unfilled "a function may leave its out parameter unfilled")
    (borrows-unchecked "a function may return a loan from a parameter its borrows declaration leaves out")
    (two-phase-unchecked "an argument lent exclusively may be lent again by a later argument of the call")
    (abox-no-loan "a box in an arena carries no loan on the arena")
    (abox-unpinned "a box in an arena gives up its loan on the arena at its last use, though its drop uses the arena")
    (reset-unchecked "an arena is reset while what is in it is used")
    (par-arena-shared "an arena may be lent shared to both of two calls at once")
    (abox-view-loans "a box in an arena that holds a view does not hold the view's loans")
    (arena-owner "an owner may be put in an arena, which drops nothing it holds")
    (linear-scope "a linear value may be dropped when its variable's scope ends")
    (linear-discard "a linear value may be thrown away by a seq or a loop")
    (linear-overwrite "a linear value may be dropped by set! over it")
    (linear-some-ways "a linear value may be moved on some ways to a join and dropped on the others")
    (linear-generic "a linear type may be given to a type parameter its function may drop")
    (set-ref-widens "a reference or view local may be given one with loans it does not hold")))
(define (mutant? m) (eq? (mutant) m))

(define-language Safe
  (prog ::= (program (decl ...) e))
  ;; A view may name a function its drop runs: one that takes the view, as a
  ;; subscript's code after its `yield` does.
  (decl ::= (struct S (T ...) ((fld σ) ...))
            (sum S (T ...) ((K σ) (K σ) ...))
            (view V ((fld ρ) ...))
            (view V ((fld ρ) ...) f)
            (global g σ e)
            (defn f (T ...) ((x τ) ...) τ e)
            ;; what f's result may borrow from: the parameters named, and no
            ;; others; without one, any reference parameter
            (borrows f (x ...))
            ;; S's values are linear: never dropped, only destroyed or taken apart
            (linear S)
            ;; f may drop values of its type parameters T, which then stand for
            ;; no linear type; any other type parameter may stand for one
            (droppable f (T ...)))
  ;; storable types; what a view's field can be; all types. A closure that owns
  ;; what it captured is storable; one that borrows is second-class, exclusive
  ;; when it captured something exclusively. An out parameter refers to a place
  ;; that holds nothing yet, which the callee must fill.
  ;; An arena owns the memory of what is allocated in it, all of it given back
  ;; at once; a box in an arena, `(abox α)`, holds a shared loan on the arena.
  ;; It may hold a view, whose loans it then holds too: what an arena holds can
  ;; borrow what else is in it, so a tree can be built there.
  (σ ::= int unit (box σ) (ptr σ) (pool σ) (handle σ) (task σ) (S σ ...) T
         (fno (τ ...) τ) arena)
  (ρ ::= σ (ref σ) (mut σ) (view V) (abox α))
  ;; a reference to a view: a view lent where it lies, as `(mut (SliceMut T))`
  (τ ::= ρ (ref (view V)) (mut (view V)) (fnb k (τ ...) τ) (out σ))
  (α ::= σ (view V))
  (e ::= n unit p
         (let ([x e]) e) (seq e e) (if0 e e e) (+ e e)
         (while e e) (break) (return e τ)
         (box e) (unbox e) (ref p) (mut p) (out p) (set! p e) (take p e) (uninit σ)
         (arena-new) (abox p e) (reset! p)
         (destroy e)
         (new τ e ...) (inj σ K e)
         (match e ((K x) e) ...) (match-ref p ((K x) e) ...) (match-mut p ((K x) e) ...)
         (pool-new σ) (insert p e) (remove p x)
         (call f (σ ...) e ...)
         (lam ([x τ e] ...) ((x τ) ...) τ e) (lamo ([x τ e] ...) ((x τ) ...) τ e)
         (apply p e ...)
         (par (call f (σ ...) e ...) (call f (σ ...) e ...))
         (spawn (call f (σ ...) e ...)) (spawn-fn e) (join e)
         (with w g x e)
         (unsafe e) (addr p) (load e) (store e e) (alloc e) (free e))
  ;; a variable, what a box or reference points at, a field, a pool element
  (p ::= x (* p) (: p fld) (at p x))
  (n ::= integer)
  (w ::= ref mut)
  (k ::= shr mut)
  ;; what of a variable is still there: all of it, none of it, all but the
  ;; parts at these paths (a path is fields and `*`s from the variable), or
  ;; none of it on some of the ways that led here (`maybe`), the rest of it
  ;; still there on the others
  (s ::= live moved maybe (gone π ...))
  (π ::= (step ...))
  (step ::= * fld)
  ;; the same, joined over every `break` of the loop being checked; none when
  ;; no break has been seen
  (b ::= none s)
  ;; An unreachable point (after a break or a return) has `%dead` first.
  (Γ ::= ((x τ s b) ...))
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
;; The seventh element says what a `return` must give back: the function's
;; result type, its parameters (a closure's captures count as parameters) and
;; those its result may borrow from (`all` without a `borrows`), or #f outside
;; any function.
(define (make-Σ decls [Ts '()] [fn #f] [lin-Ts '()]) (list (mutant) 'safe 'noloop Ts (program-decls decls) '() fn lin-Ts))
;; the type parameters of the function being checked that may stand for linear
;; types: those it does not say it may drop
(define (Σ-lin-Ts Σ) (eighth Σ))
(define (in-unsafe? Σ) (eq? (second Σ) 'unsafe))
(define (in-loop? Σ) (eq? (third Σ) 'loop))
(define (tparams Σ) (fourth Σ))
(define (decls-of Σ) (program-decls-list (fifth Σ)))
(define (fn-of Σ) (seventh Σ))
(define (Σ-set Σ i v) (list-set Σ i v))
(define (Σ-unsafe Σ) (Σ-set Σ 1 'unsafe))
(define (Σ-loop Σ) (Σ-set Σ 2 'loop))
;; The variables that what runs after the expression being checked still names.
(define (Σ-live Σ) (sixth Σ))
;; Σ for an expression that the expressions `later` run after.
(define (Σ+ Σ . later)
  (Σ-set Σ 5 (remove-duplicates (append (append-map uses later) (sixth Σ)))))

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
    [`(return ,e ,_) (uses e)]
    [`(uninit ,_) '()]
    ;; a closure's body is a function of its own: what it names is not ours
    [`(,(or 'lam 'lamo) ([,_ ,_ ,es] ...) ,_ ,_ ,_) (append-map uses es)]
    [(cons (? symbol?) rest) (append-map uses rest)]
    [_ (error 'uses "not an expression: ~a" t)]))
(define (find-decl Σ kind name)
  (for/first ([d (decls-of Σ)] #:when (and (eq? (car d) kind) (eq? (cadr d) name))) d))

;; ---------------------------------------------------------------- types

(define (subst τ Ts σs)
  (match τ
    [(? symbol? t) (let ([i (index-of Ts t)]) (if i (list-ref σs i) t))]
    [`(view ,_) τ]
    ['() '()]
    [`(fnb ,k ,τs ,τr) `(fnb ,k ,(subst τs Ts σs) ,(subst τr Ts σs))]
    [`(fno ,τs ,τr) `(fno ,(subst τs Ts σs) ,(subst τr Ts σs))]
    [(cons head args) (cons (if (pair? head) (subst head Ts σs) head)
                            (for/list ([a args]) (subst a Ts σs)))]))

;; -> ((fld τ) ...) for a struct or view type, else #f
(define (fields-of Σ τ)
  (match τ
    [`(view ,V) (match (find-decl Σ 'view V) [`(view ,_ ,fields . ,_) fields] [_ #f])]
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
    [(or 'int 'unit 'arena) #t]
    [(? symbol? t) (and (memq t (tparams Σ)) #t)]
    [`(,(or 'box 'ptr 'pool 'handle 'task 'ref 'mut 'out 'abox) ,σ) (wf? Σ σ)]
    [`(view ,V) (and (find-decl Σ 'view V) #t)]
    [`(fnb ,k (,τs ...) ,τr) (and (memq k '(shr mut)) (andmap (λ (t) (wf? Σ t)) (cons τr τs)))]
    [`(fno (,τs ...) ,τr) (andmap (λ (t) (wf? Σ t)) (cons τr τs))]
    [(cons (? symbol? S) args)
     (let ([d (or (find-decl Σ 'struct S) (find-decl Σ 'sum S))])
       (and d (= (length (caddr d)) (length args)) (andmap (λ (a) (wf? Σ a)) args)))]
    [_ #f]))

(define (second-class? τ)
  (match τ [`(,(or 'ref 'mut 'view 'out 'abox) ,_) #t] [`(fnb . ,_) #t] [_ #f]))
;; a second-class value that cannot be copied: it gives exclusive access
(define (exclusive? Σ τ [seen '()])
  (match τ
    [`(,(or 'mut 'out 'abox) ,_) #t]
    [`(fnb mut . ,_) #t]
    [`(view ,V) (and (not (memq V seen))
                     (for/or ([f (fields-of Σ τ)]) (exclusive? Σ (cadr f) (cons V seen))))]
    [_ #f]))
(define (kind-of Σ τ) (if (exclusive? Σ τ) 'mut 'shr))
;; the function a view's drop runs, or #f
(define (view-drop Σ τ)
  (match τ
    [`(view ,V) (match (find-decl Σ 'view V) [`(view ,_ ,_ ,f) f] [_ #f])]
    [_ #f]))
;; A view that is dropped: one that gives exclusive access, or one whose drop
;; runs code. Naming one moves it, and it keeps its loans until its scope ends,
;; since its drop may use what it borrowed.
(define (dropped-view? Σ τ)
  (match τ
    [`(view ,_) (and (or (exclusive? Σ τ)
                         (and (view-drop Σ τ) #t)
                         (for/or ([f (fields-of Σ τ)]) (dropped-view? Σ (cadr f))))
                     #t)]
    [_ #f]))
;; a second-class value that is moved when it is named
(define (moved-second? Σ τ) (or (exclusive? Σ τ) (dropped-view? Σ τ)))

;; a storable type whose values own nothing. A type parameter may stand for an owner.
;; ---------------------------------------------------------------- linear values

;; Is a value of type τ linear: one never dropped, only destroyed or taken
;; apart? A struct the program declares linear is, and so is what holds one: a
;; struct or sum with a part that is, a box, a pool or a task of one. A type
;; parameter is when the function says it may be.
(define (lin? Σ τ [seen '()])
  (match τ
    [(? symbol? T) (and (memq T (Σ-lin-Ts Σ)) #t)]
    [`(,(or 'box 'pool 'task) ,σ) (lin? Σ σ seen)]
    [(cons (? symbol? S) _)
     #:when (find-decl Σ 'linear S)
     #t]
    [_ (and (pair? τ) (not (member τ seen)) (not (second-class? τ))
            (let ([parts (or (fields-of Σ τ) (variants-of Σ τ) '())])
              (for/or ([part parts]) (lin? Σ (cadr part) (cons τ seen)))))]))

;; Does a variable of type τ in state s still hold something linear, which
;; leaving its scope would drop? A part moved out is gone; a struct declared
;; linear is taken apart when every one of its fields is.
(define (lin-left? Σ τ s)
  (match s
    ['moved #f]
    ['live (lin? Σ τ)]
    ;; moved on some ways: still there on the others
    ['maybe (and (not (mutant? 'linear-some-ways)) (lin? Σ τ))]
    [`(gone ,πs ...)
     (define fs (or (fields-of Σ τ) '()))
     (cond [(member '() πs) #f]
           ;; one declared linear is taken apart only when every field is gone
           [(and (pair? τ) (symbol? (car τ)) (find-decl Σ 'linear (car τ)))
            (not (for/and ([f fs]) (member (list (car f)) πs)))]
           [else
            (for/or ([f fs])
              (define in (for/list ([π πs] #:when (and (pair? π) (eq? (car π) (car f)))) (cdr π)))
              (lin-left? Σ (cadr f) (if (null? in) 'live `(gone ,@in))))])]
    [_ (lin? Σ τ)]))

;; The type parameters f says it may drop.
(define (droppable-of decls f)
  (or (for/first ([d decls] #:when (and (eq? (car d) 'droppable) (eq? (cadr d) f))) (caddr d))
      '()))

;; The type parameters Ts of f that may stand for linear types: those it does
;; not say it may drop.
(define (lin-Ts-of decls f Ts)
  (let ([drops (droppable-of decls f)])
    (filter (λ (T) (not (memq T drops))) Ts)))

;; Is a linear type given to none of the type parameters f may drop?
(define (admits-linear? Σ f Ts σs)
  (or (mutant? 'linear-generic)
      (let ([drops (droppable-of (decls-of Σ) f)])
        (for/and ([T Ts] [σ σs]) (or (not (memq T drops)) (not (lin? Σ σ)))))))

;; Does x leave its scope still holding something linear: at the end, or at a
;; break that left it? Where the end cannot be reached (after a return or a
;; break) only the breaks count: a return checks what it leaves itself.
(define (lin-dropped? Σ x Γ)
  (and (not (mutant? 'linear-scope))
       (match (assq x Γ)
         [(list _ τ s b)
          (or (and (not (dead? Γ)) (lin-left? Σ τ s))
              (and (not (eq? b 'none)) (lin-left? Σ τ b)))]
         [_ #f])))

(define (copy? Σ σ [seen '()])
  (and (not (lin? Σ σ)) (copy-shape? Σ σ seen)))
(define (copy-shape? Σ σ [seen '()])
  (match σ
    [(or 'int 'unit) #t]
    [(? symbol?) (mutant? 'copy-typevar)]
    [`(,(or 'ptr 'handle) ,_) #t]
    [`(,(or 'box 'pool 'task) ,_) #f]
    ['arena #f]
    [`(fno . ,_) #f]
    [_ (let ([parts (or (fields-of Σ σ) (variants-of Σ σ))])
         (and parts
              (not (member σ seen))
              (or (mutant? 'copy-struct)
                  (for/and ([part parts]) (copy? Σ (cadr part) (cons σ seen))))))]))

;; ---------------------------------------------------------------- places

(define (lookup Γ x)
  (match (assq x Γ)
    [(list _ τ (or 'moved 'maybe) _) (if (mutant? 'no-moves) τ #f)]
    [(list _ τ _ _) τ]
    [_ #f]))

(define (place-type Σ Γ p)
  (match p
    [(? symbol? x) (lookup Γ x)]
    [`(* ,p2) (match (place-type Σ Γ p2)
                [`(,(or 'box 'ref 'mut 'out 'abox) ,σ) σ]
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
                       (match (place-type Σ Γ p2) [`(,(or 'box 'mut 'out 'abox) ,_) #t] [_ #f]))
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
          [(list _ τ _ _) (or (not (second-class? τ))
                              (match τ
                                [`(view ,_) (if (mutant? 'drop-view-unpinned)
                                                (exclusive? Σ τ)
                                                (dropped-view? Σ τ))]
                                ;; its drop runs in the arena's memory
                                [`(abox ,_) (not (mutant? 'abox-unpinned))]
                                [_ #f]))]
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

;; Is each loan of L covered by one HELD: on the same place or one it is part
;; of, and exclusive when it is?
(define (loans-covered? L held)
  (for/and ([l L])
    (match-define (list q k) l)
    (for/or ([h held])
      (match-define (list q2 k2) h)
      (and (place-within? q q2) (or (eq? k 'shr) (eq? k2 'mut))))))
(define (place-within? q outer)
  (or (equal? q outer)
      (match q
        [`(* ,q1) (place-within? q1 outer)]
        [`(: ,q1 ,_) (place-within? q1 outer)]
        [`(elem ,q1) (place-within? q1 outer)]
        [_ #f])))

;; the loans a shared borrow of p carries: through a shared reference, the loans
;; of whoever holds that reference; otherwise a shared loan on p itself
(define (shared-loans Σ Γ Λ p)
  (cond [(and (mutant? 'no-elem-loans) (has-at? p)) '()]
        [(through-shared? Σ Γ p) (loans-of Λ (place-root p))]
        [else `((,(norm p) shr))]))
;; Does a value of type τ own nothing an arena would have to drop? What is in
;; an arena is never dropped: its memory comes back when the arena is reset.
;; So it holds plain data, references, boxes in an arena (whose contents were
;; asked this when they were made) and views made of those, none with a drop of
;; its own to run.
(define (arena-safe? Σ τ [seen '()])
  (match τ
    [(or 'int 'unit) #t]
    [`(,(or 'ptr 'handle 'ref 'mut 'abox) ,_) #t]
    [`(view ,_) (and (not (view-drop Σ τ))
                     (for/and ([f (fields-of Σ τ)]) (arena-safe? Σ (cadr f) seen)))]
    [(? symbol?) #f]
    [`(,(or 'box 'pool 'task 'out 'fnb 'fno) . ,_) #f]
    ['arena #f]
    [_ (or (member τ seen)
           (let ([parts (or (fields-of Σ τ) (variants-of Σ τ))])
             (and parts (for/and ([part parts]) (arena-safe? Σ (cadr part) (cons τ seen))))))]))

;; Can a value of type τ reach an arena? An arena changes when something is
;; allocated in it, though it is lent only shared, so it is never lent to two
;; threads at once.
(define (holds-arena? Σ τ [seen '()])
  (match τ
    ['arena #t]
    [(? symbol?) #f]
    [`(,(or 'box 'ref 'mut 'out 'abox 'pool 'ptr 'task) ,σ) (holds-arena? Σ σ seen)]
    [`(,(or 'fnb 'fno) . ,_) #f]
    [_ (and (not (member τ seen))
            (let ([parts (or (fields-of Σ τ) (variants-of Σ τ) '())])
              (for/or ([part parts]) (holds-arena? Σ (cadr part) (cons τ seen)))))]))
;; the loans one of two calls at once holds, as the other sees them: a shared
;; loan on something that reaches an arena is an exclusive one. What it
;; borrows reaches what that holds borrowed, so those loans count too.
(define (par-loans Σ Γ Λ L0)
  (define L
    (let grow ([L L0])
      (define more (union L (append* (for/list ([l L]) (loans-of Λ (place-root (car l)))))))
      (if (= (length more) (length L)) L (grow more))))
  (for/list ([l L])
    (match l
      [`(,q shr)
       #:when (and (not (mutant? 'par-arena-shared))
                   (let* ([r (place-root q)]
                          [τ (match (assq r Γ)
                               [(list _ τ _ _) τ]
                               [_ (match (find-decl Σ 'global r) [`(global ,_ ,σ ,_) σ] [_ #f])])])
                     (or (not τ) (holds-arena? Σ τ))))
       `(,q mut)]
      [_ l])))
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

;; ---- what of each variable is still there

;; The path of a place from its variable: (x step ...), or #f when the place is
;; an element of a pool, which only the whole pool is known about.
(define (path-of p)
  (match p
    [(? symbol? x) (list x)]
    [`(* ,p2) (let ([r (path-of p2)]) (and r (append r '(*))))]
    [`(: ,p2 ,fld) (let ([r (path-of p2)]) (and r (append r (list fld))))]
    [`(at ,_ ,_) #f]))
;; the path of the part of p a moved part could be in: up to its first pool element
(define (reach-of p)
  (match p
    [(? symbol? x) (list x)]
    [`(* ,p2) (append (reach-of p2) '(*))]
    [`(: ,p2 ,fld) (append (reach-of p2) (list fld))]
    [`(at ,p2 ,_) (reach-of p2)]))
(define (list-prefix? a b) (and (<= (length a) (length b)) (equal? a (take b (length a)))))
(define (paths-overlap? a b) (or (list-prefix? a b) (list-prefix? b a)))

(define (state-of Γ x) (match (assq x Γ) [(list _ _ s _) s] [_ #f]))
(define (set-state Γ x s2)
  (for/list ([e Γ]) (if (eq? (car e) x) (list x (cadr e) s2 (cadddr e)) e)))

;; is every part of the place p there to be read, lent or moved?
(define (available? Γ p)
  (match-define (cons x π) (reach-of p))
  (match (state-of Γ x)
    ['live #t]
    [(or 'moved 'maybe) (mutant? 'no-moves)]
    [`(gone ,πs ...) (not (for/or ([g πs]) (paths-overlap? g π)))]
    [#f #f]))

;; part π of a variable in state s is moved
(define (state-minus s π)
  (cond [(null? π) 'moved]
        [else (match s
                [(or 'moved 'maybe) s]
                ['live `(gone ,π)]
                [`(gone ,πs ...) `(gone ,@(filter (λ (g) (not (list-prefix? π g))) πs) ,π)])]))
;; part π is given a value again
(define (state-plus s π)
  (cond [(null? π) 'live]
        [else (match s
                ['live 'live]
                [(or 'moved 'maybe) s]
                [`(gone ,πs ...)
                 (define left (filter (λ (g) (not (list-prefix? π g))) πs))
                 (if (null? left) 'live `(gone ,@left))])]))
;; can the place p be assigned? Its variable and every part above it must be
;; there; p itself, or parts of it, may have been moved.
(define (assignable? Γ p)
  ;; an element of a pool is never moved out: its pool must be there
  (match-define (cons x π) (or (path-of p) (reach-of p)))
  (match (state-of Γ x)
    ['live #t]
    [(or 'moved 'maybe) (or (null? π) (mutant? 'set-inside-moved))]
    [`(gone ,πs ...) (or (mutant? 'set-inside-moved)
                         (not (for/or ([g πs]) (and (list-prefix? g π) (not (equal? g π))))))]
    [#f #f]))
(define (mark-moved Γ p)
  (match-define (cons x π) (path-of p))
  (if (or (mutant? 'no-moves) (and (pair? π) (mutant? 'part-unmarked)))
      Γ
      (set-state Γ x (state-minus (state-of Γ x) π))))
(define (mark-filled Γ p)
  (match (path-of p)
    [(cons x π) (set-state Γ x (state-plus (state-of Γ x) π))]
    [#f Γ]))
;; Γ as if nothing had been moved: for the type of a place that holds nothing
(define (all-live Γ) (for/list ([e Γ]) (list (car e) (cadr e) 'live (cadddr e))))
;; is the place p exactly a part that has been moved, to be filled through an
;; out parameter?
(define (empty-place? Γ p)
  (define path (path-of p))
  (and path
       (match (state-of Γ (car path))
         [(or 'moved 'maybe) (null? (cdr path))]
         [`(gone ,πs ...) (and (member (cdr path) πs) #t)]
         [_ #f])))

;; Does a variable of type τ in state s hold nothing at all: moved, or a struct
;; every field of which is?
(define (emptied? Σ τ s)
  (match s
    ['moved #t]
    [`(gone ,πs ...)
     (define fs (or (fields-of Σ τ) '()))
     (and (pair? fs)
          (for/and ([f fs])
            (define in (for/list ([π πs] #:when (and (pair? π) (eq? (car π) (car f)))) (cdr π)))
            (or (and (member '() in) #t)
                (and (pair? in) (emptied? Σ (cadr f) `(gone ,@in))))))]
    [_ #f]))

;; Moved on one way and not the other is `maybe`: as moved, except that what is
;; still there on the other way is dropped there, which a linear value never is.
;; Where the other way left nothing in it either, it is moved.
(define (state-join Σ τ a b)
  (match* (a b)
    [('live 'live) 'live]
    [('moved 'moved) 'moved]
    [('maybe _) 'maybe]
    [(_ 'maybe) 'maybe]
    [('moved s) (if (emptied? Σ τ s) 'moved 'maybe)]
    [(s 'moved) (if (emptied? Σ τ s) 'moved 'maybe)]
    [('live s) s]
    [(s 'live) s]
    [(`(gone ,xs ...) `(gone ,ys ...))
     (define all (remove-duplicates (append xs ys)))
     `(gone ,@(filter (λ (g) (not (for/or ([h all]) (and (list-prefix? h g) (not (equal? h g)))))) all))]))
(define (break-join Σ τ a b)
  (cond [(eq? a 'none) b] [(eq? b 'none) a] [else (state-join Σ τ a b)]))

;; An unreachable point: after a break or a return.
(define dead-mark '(%dead unit live none))
(define (dead? Γ) (and (pair? Γ) (eq? (caar Γ) '%dead)))
(define (vars-of Γ) (if (dead? Γ) (cdr Γ) Γ))
(define (make-dead Γ) (if (dead? Γ) Γ (cons dead-mark Γ)))

(define (remove-var Γ x) (filter (λ (b) (not (eq? (car b) x))) Γ))
(define (bind-var Γ x τ) (let ([vs (vars-of Γ)])
                           (define bound (cons (list x τ 'live 'none) vs))
                           (if (dead? Γ) (make-dead bound) bound)))
;; Two ways the program may have come: a variable is moved after it if it was
;; on either way, and an unreachable way does not count.
(define (join Σ Γ1 Γ2)
  (define d1 (dead? Γ1))
  (define d2 (dead? Γ2))
  (define body
    (for/list ([a (vars-of Γ1)] [b (vars-of Γ2)])
      (list (car a) (cadr a)
            (cond [d1 (caddr b)] [d2 (caddr a)] [else (state-join Σ (cadr a) (caddr a) (caddr b))])
            (break-join Σ (cadr a) (cadddr a) (cadddr b)))))
  (if (and d1 d2) (make-dead body) body))
;; A break: what each variable is here joins what it is at the loop's other breaks.
(define (record-break Σ Γ)
  (make-dead (for/list ([e (vars-of Γ)]) (list (car e) (cadr e) (caddr e) (break-join Σ (cadr e) (cadddr e) (caddr e))))))
(define (same-states? Γ1 Γ2)
  (equal? (map caddr (vars-of Γ1)) (map caddr (vars-of Γ2))))
;; A loop is left when its condition is 0 (the state after the condition) or by
;; a break; the breaks seen outside it are the outer loop's again.
(define (clear-breaks Γ)
  (define vs (for/list ([e (vars-of Γ)]) (list (car e) (cadr e) (caddr e) 'none)))
  (if (dead? Γ) (make-dead vs) vs))
(define (loop-exit Σ Γ-outer Γ-cond Γ-body)
  (for/list ([o (vars-of Γ-outer)] [c (vars-of Γ-cond)] [e (vars-of Γ-body)])
    (list (car o) (cadr o)
          (if (mutant? 'break-forgets) (caddr c) (break-join Σ (cadr o) (caddr c) (cadddr e)))
          (cadddr o))))

;; Can the part of an exclusive or out parameter's referent be left as it is
;; when the function returns? It must all be there.
(define (restored? Σ x τ s)
  (match τ
    [`(,(or 'mut 'out) ,_)
     (match s
       [`(gone ,πs ...) (or (mutant? (if (eq? (car τ) 'out) 'out-unfilled 'no-restore))
                            (not (for/or ([g πs]) (and (pair? g) (eq? (car g) '*)))))]
       [_ #t])]
    [`(fnb . ,_) #t]
    [`(view ,_) #t]
    [`(ref ,_) #t]
    [_ #t]))

;; Can the owner at p be moved out of it? A variable can, and so can a field of
;; a struct and what a box or an exclusive reference holds, along a path of
;; those. An element of a pool, a view's field and anything behind a shared
;; reference cannot: `take` gets an owner out of those.
(define (movable? Σ Γ p)
  (match p
    [(? symbol?) #t]
    ;; through an exclusive reference only when it is a parameter (a closure's
    ;; capture counts): the function's every way out checks it is given back
    [`(* ,p2) (and (match (place-type Σ Γ p2)
                     ['(box . ,_) #t]
                     [`(box ,_) #t]
                     [`(,(or 'mut 'out) ,_)
                      (match (fn-of Σ)
                        [(list _ params _) (and (memq (place-root (norm p2)) params) #t)]
                        [_ #f])]
                     [_ #f])
                   (movable? Σ Γ p2))]
    [`(: ,p2 ,_) (and (match (place-type Σ Γ p2) [`(view ,_) #f] [_ #t])
                      (movable? Σ Γ p2))]
    [_ #f]))

;; can a value of type GOT be given where WANT is asked for?
;; With `coil-closures` (not a weakening: what Coil's closures are), one that
;; captured exclusively goes where one that captured only shared is asked for
;; too: Coil never copies a closure, and runs one only through an exclusive
;; reference to it, so the model's shared kind is no more than its exclusive one.
(define (fits? got want)
  (or (equal? got want)
      (match* (got want)
        [(`(fnb shr ,τs ,τr) `(fnb mut ,τs2 ,τr2)) (and (equal? τs τs2) (equal? τr τr2))]
        [(`(fnb mut ,τs ,τr) `(fnb shr ,τs2 ,τr2))
         (and (mutant? 'coil-closures) (equal? τs τs2) (equal? τr τr2))]
        [(_ _) #f])))

;; what naming a place as a value does
;;   copy   plain data is copied             move   an owner is moved
;;   copy2  a shared reference or view is copied, loans and all
;;   move2  an exclusive one is moved (variables only)
(define (read-kind Σ Γ p)
  (define τ (place-type Σ Γ p))
  (cond [(not τ) #f]
        [(match τ [`(out ,_) #t] [_ #f]) #f]
        [(second-class? τ) (if (moved-second? Σ τ) (and (symbol? p) 'move2) 'copy2)]
        [(copy? Σ τ) 'copy]
        [(movable? Σ Γ p) 'move]
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
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   -------------------------------------------- "copy"
   (chk Σ Γ Λ p σ () Γ)]

  ;; a variable, a field of a struct, or what a box or exclusive reference holds;
  ;; the part moved is gone until it is given a value again
  [(side-condition ,(eq? 'move (read-kind (term Σ) (term Γ) (term p))))
   (where σ ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where Γ_1 ,(mark-moved (term Γ) (term p)))
   -------------------------------------------- "move"
   (chk Σ Γ Λ p σ () Γ_1)]

  [(side-condition ,(eq? 'copy2 (read-kind (term Σ) (term Γ) (term p))))
   (where τ ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where L ,(loans-of (term Λ) (place-root (term p))))
   -------------------------------------------- "copy-ref"
   (chk Σ Γ Λ p τ L Γ)]

  ;; an exclusive reference, or a view that is dropped, is moved, and must not
  ;; be reborrowed at the time
  [(side-condition ,(eq? 'move2 (read-kind (term Σ) (term Γ) (term x))))
   (where τ ,(place-type (term Σ) (term Γ) (term x)))
   (side-condition ,(available? (term Γ) (term x)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term x)))
   (where L ,(loans-of (term Λ) (term x)))
   (where Γ_1 ,(if (mutant? 'copy-mut) (term Γ) (mark-moved (term Γ) (term x))))
   -------------------------------------------- "move-mut"
   (chk Σ Γ Λ x τ L Γ_1)]

  ;; what is lent may be a view: the reference keeps it, and through it what it
  ;; borrowed, lent for as long as the reference is used
  [(where any_t ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(or (redex-match? Safe σ (term any_t)) (redex-match? Safe (view V) (term any_t))))
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where L ,(shared-loans (term Σ) (term Γ) (term Λ) (term p)))
   -------------------------------------------- "borrow"
   (chk Σ Γ Λ (ref p) (ref any_t) L Γ)]

  [(where any_t ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(or (redex-match? Safe σ (term any_t)) (redex-match? Safe (view V) (term any_t))))
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where L ,(exclusive-loans (term p)))
   -------------------------------------------- "borrow-mut"
   (chk Σ Γ Λ (mut p) (mut any_t) L Γ)]

  ;; a place that holds nothing, lent to be filled: a call it is passed to fills it
  [(where σ ,(place-type (term Σ) (all-live (term Γ)) (term p)))
   (side-condition ,(empty-place? (term Γ) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   (where L ,(exclusive-loans (term p)))
   -------------------------------------------- "out"
   (chk Σ Γ Λ (out p) (out σ) L Γ)]

  [(side-condition ,(wf? (term Σ) (term σ)))
   -------------------------------------------- "uninit"
   (chk Σ Γ Λ (uninit σ) σ () Γ)]

  [(chk Σ Γ Λ e σ () Γ_1)
   -------------------------------------------- "box"
   (chk Σ Γ Λ (box e) (box σ) () Γ_1)]

  [(chk Σ Γ Λ e (box σ) () Γ_1)
   -------------------------------------------- "unbox"
   (chk Σ Γ Λ (unbox e) σ () Γ_1)]

;; ---- linear values

  ;; a struct declared linear, taken apart: what it holds is dropped, so none
  ;; of it is linear itself
  [(chk Σ Γ Λ e (S σ ...) () Γ_1)
   (side-condition ,(find-decl (term Σ) 'linear (term S)))
   (side-condition ,(for/and ([f (fields-of (term Σ) (term (S σ ...)))]) (not (lin? (term Σ) (cadr f)))))
   -------------------------------------------- "destroy"
   (chk Σ Γ Λ (destroy e) unit () Γ_1)]

  ;; ---- arenas

  [-------------------------------------------- "arena-new"
   (chk Σ Γ Λ (arena-new) arena () Γ)]

  ;; what is put in an arena keeps the arena lent, shared: many boxes share it,
  ;; and none outlives it or is in it when it is reset
  [(chk ,(Σ+ (term Σ) (term p)) Γ Λ e α L_e Γ_1)
   (side-condition ,(equal? (place-type (term Σ) (term Γ_1) (term p)) 'arena))
   (side-condition ,(available? (term Γ_1) (term p)))
   (side-condition ,(or (mutant? 'arena-owner) (arena-safe? (term Σ) (term α))))
   ;; what the value holds is alive while the arena is lent
   (side-condition ,(read-ok? (active (term Σ) (term Γ_1) (add-loans (term Λ) (term tmp) (term L_e))) (term p)))
   (where L ,(union (if (mutant? 'abox-no-loan) '() (shared-loans (term Σ) (term Γ_1) (term Λ) (term p)))
                    (if (mutant? 'abox-view-loans) '() (term L_e))))
   -------------------------------------------- "abox"
   (chk Σ Γ Λ (abox p e) (abox α) L Γ_1)]

  ;; giving back all of an arena's memory needs it exclusively
  [(side-condition ,(equal? (place-type (term Σ) (term Γ) (term p)) 'arena))
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(or (mutant? 'reset-unchecked)
                        (write-ok? (active (term Σ) (term Γ) (term Λ)) (term p))))
   -------------------------------------------- "reset"
   (chk Σ Γ Λ (reset! p) unit () Γ)]

  ;; what a box in an arena holds, moved out of it
  ;; a view moved out keeps everything the box held lent
  [(chk Σ Γ Λ e (abox α) L Γ_1)
   (where L_r ,(if (second-class? (term α)) (term L) '()))
   -------------------------------------------- "unbox-arena"
   (chk Σ Γ Λ (unbox e) α L_r Γ_1)]

  ;; The loans of e_1's value belong to x, and count while x is still named. A
  ;; `let` of `(uninit σ)` makes a variable with nothing in it yet.
  [(chk ,(Σ+ (term Σ) (term e_2)) Γ Λ e_1 τ_1 L_1 Γ_1)
   (side-condition ,(not (assq (term x) (term Γ_1))))
   (where Λ_2 ,(add-loans (term Λ) (term x) (if (mutant? 'no-let-loans) '() (term L_1))))
   (where Γ_b ,(let ([g (bind-var (term Γ_1) (term x) (term τ_1))])
                 (match (term e_1) [`(uninit ,_) (set-state g (term x) 'moved)] [_ g])))
   (chk Σ Γ_b Λ_2 e_2 τ_2 L_2 Γ_2)
   (side-condition ,(not (lin-dropped? (term Σ) (term x) (term Γ_2))))
   (where L_3 ,(exit-scope (term x) (term τ_1) (term Λ_2) (term L_2)))
   (where Γ_3 ,(remove-var (term Γ_2) (term x)))
   -------------------------------------------- "let"
   (chk Σ Γ Λ (let ([x e_1]) e_2) τ_2 L_3 Γ_3)]

  [(chk ,(Σ+ (term Σ) (term e_2)) Γ Λ e_1 τ_1 L_1 Γ_1)
   (side-condition ,(or (mutant? 'linear-discard) (not (lin? (term Σ) (term τ_1)))))
   (chk Σ Γ_1 Λ e_2 τ_2 L_2 Γ_2)
   -------------------------------------------- "seq"
   (chk Σ Γ Λ (seq e_1 e_2) τ_2 L_2 Γ_2)]

  ;; The new value is computed first. Then the place must be reachable for
  ;; writing and free of loans, because its old value is dropped. A part that
  ;; was moved away, or holds parts that were, is whole again after it; a part
  ;; inside one that was moved away is not there to be written.
  [(chk ,(Σ+ (term Σ) (term p)) Γ Λ e σ () Γ_1)
   (where σ ,(place-type (term Σ) (term Γ_1) (term p)))
   (side-condition ,(assignable? (term Γ_1) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ_1) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ_1) (term Λ)) (term p)))
   ;; the old value is dropped: never a linear one
   (side-condition ,(or (mutant? 'linear-overwrite) (not (lin? (term Σ) (term σ)))))
   (where Γ_2 ,(mark-filled (term Γ_1) (term p)))
   -------------------------------------------- "set"
   (chk Σ Γ Λ (set! p e) unit () Γ_2)]

  ;; A reference or view local is given another value: one that carries only
  ;; loans the local already holds, which stay alive as long as it does, so what
  ;; either value refers to stays lent. A cursor walking a structure borrows
  ;; through itself, `(set! c (ref (: (* c) next)))`; a local made on several
  ;; ways holds what each way lent.
  [(where τ ,(lookup (term Γ) (term x)))
   (side-condition ,(second-class? (term τ)))
   (chk ,(Σ+ (term Σ) (term x)) Γ Λ e τ L Γ_1)
   (side-condition ,(available? (term Γ_1) (term x)))
   (side-condition ,(or (mutant? 'set-ref-widens) (loans-covered? (term L) (loans-of (term Λ) (term x)))))
   -------------------------------------------- "set-ref"
   (chk Σ Γ Λ (set! x e) unit () Γ_1)]

  ;; a variable whose whole value was moved; one moved on some ways only still
  ;; holds it on the others, where set! drops it
  [(chk ,(Σ+ (term Σ) (term x)) Γ Λ e σ () Γ_1)
   (where (x σ any_s b) ,(assq (term x) (term Γ_1)))
   (side-condition ,(or (eq? (term any_s) 'moved)
                        (and (eq? (term any_s) 'maybe)
                             (or (mutant? 'linear-some-ways) (not (lin? (term Σ) (term σ)))))))
   (where Γ_2 ,(mark-filled (term Γ_1) (term x)))
   -------------------------------------------- "set-moved"
   (chk Σ Γ Λ (set! x e) unit () Γ_2)]

  ;; the same, and the old value is the result instead of being dropped
  [(chk ,(Σ+ (term Σ) (term p)) Γ Λ e σ () Γ_1)
   (where σ ,(place-type (term Σ) (term Γ_1) (term p)))
   (side-condition ,(available? (term Γ_1) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ_1) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ_1) (term Λ)) (term p)))
   -------------------------------------------- "take"
   (chk Σ Γ Λ (take p e) σ () Γ_1)]

  [(chk ,(Σ+ (term Σ) (term e_2) (term e_3)) Γ Λ e_1 int L_1 Γ_1)
   (chk Σ Γ_1 Λ e_2 τ L_2 Γ_2)
   (chk Σ Γ_1 Λ e_3 τ L_3 Γ_3)
   (where L ,(if (mutant? 'no-union) (term L_2) (union (term L_2) (term L_3))))
   (where Γ_4 ,(if (mutant? 'no-join) (term Γ_2) (join (term Σ) (term Γ_2) (term Γ_3))))
   -------------------------------------------- "if0"
   (chk Σ Γ Λ (if0 e_1 e_2 e_3) τ L Γ_4)]

  ;; A loop's body may run again, so when its end is reached it leaves every
  ;; outer variable as the condition found it. The loop is left when the
  ;; condition is 0 or by a break: after it, a variable is moved if it was on
  ;; either way. What the loop names is named again by its next turn.
  [(where Γ_0 ,(clear-breaks (term Γ)))
   (chk ,(Σ+ (term Σ) (term e_c) (term e_b)) Γ_0 Λ e_c int L_c Γ_1)
   (chk ,(Σ-loop (Σ+ (term Σ) (term e_c) (term e_b))) Γ_1 Λ e_b τ_b L_b Γ_2)
   (side-condition ,(or (mutant? 'linear-discard) (not (lin? (term Σ) (term τ_b)))))
   (side-condition ,(or (mutant? 'loop-moves) (dead? (term Γ_2)) (same-states? (term Γ_2) (term Γ_0))))
   (where Γ_3 ,(let ([out (loop-exit (term Σ) (term Γ) (term Γ_1) (term Γ_2))])
                 (if (dead? (term Γ)) (make-dead out) out)))
   -------------------------------------------- "while"
   (chk Σ Γ Λ (while e_c e_b) unit () Γ_3)]

  [(side-condition ,(in-loop? (term Σ)))
   (where Γ_1 ,(record-break (term Σ) (term Γ)))
   -------------------------------------------- "break"
   (chk Σ Γ Λ (break) unit () Γ_1)]

  ;; Leave the function with e's value: every local's scope ends, and the value
  ;; may carry only the loans a result may. Whatever an exclusive or out
  ;; parameter refers to must be whole. τ is the type the form has where it is
  ;; written; nothing after it runs.
  [(where (τ_r (x_p ...) any_only) ,(fn-of (term Σ)))
   (side-condition ,(wf? (term Σ) (term τ)))
   (chk Σ Γ Λ e τ_r L Γ_1)
   (side-condition ,(or (mutant? 'return-escape)
                        (return-ok? (term Σ) (term Γ_1) (term Λ) (term L) (term (x_p ...)) (term any_only))))
   (where Γ_2 ,(make-dead (term Γ_1)))
   -------------------------------------------- "return"
   (chk Σ Γ Λ (return e τ) τ () Γ_2)]

  ;; ---- structs, views, sums

  [(side-condition ,(wf? (term Σ) (term σ)))
   (where ((fld τ_f) ...) ,(fields-of (term Σ) (term σ)))
   (chk-args Σ Γ Λ (e ...) (τ_f ...) L Γ_1)
   -------------------------------------------- "new"
   (chk Σ Γ Λ (new σ e ...) σ () Γ_1)]

  ;; a view borrows from every reference (and view) it is built from
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
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(read-ok? (active (Σ+* (term Σ) (term (e_a ...))) (term Γ) (term Λ)) (term p)))
   (where L_x ,(shared-loans (term Σ) (term Γ) (term Λ) (term p)))
   (chk-arms Σ Γ Λ (((K x) e_a) ...) ((ref σ_K) ...) L_x τ L Γ_1)
   -------------------------------------------- "match-ref"
   (chk Σ Γ Λ (match-ref p ((K x) e_a) ...) τ L Γ_1)]

  [(where σ_s ,(place-type (term Σ) (term Γ) (term p)))
   (where ((K σ_K) ...) ,(variants-of (term Σ) (term σ_s)))
   (side-condition ,(available? (term Γ) (term p)))
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
   (side-condition ,(available? (term Γ_1) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ_1) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ_1) (term Λ)) (term p)))
   -------------------------------------------- "insert"
   (chk Σ Γ Λ (insert p e) (handle σ) () Γ_1)]

  [(where (pool σ) ,(place-type (term Σ) (term Γ) (term p)))
   (where (handle σ) ,(lookup (term Γ) (term x)))
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(available? (term Γ) (term x)))
   (side-condition ,(read-ok? (active (term Σ) (term Γ) (term Λ)) (term x)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(write-ok? (active (term Σ) (term Γ) (term Λ)) (term p)))
   -------------------------------------------- "remove"
   (chk Σ Γ Λ (remove p x) σ () Γ)]

  ;; ---- calls

  ;; A returned reference borrows from every reference argument of the call, or
  ;; from those its `borrows` names. A place passed as `(out p)` holds a value
  ;; once the call returns.
  [(where (defn f (T ...) ((x_p τ_p) ...) τ_r any_b) ,(find-decl (term Σ) 'defn (term f)))
   (side-condition ,(and (= (length (term (T ...))) (length (term (σ ...))))
                         (andmap (λ (t) (wf? (term Σ) t)) (term (σ ...)))))
   (side-condition ,(admits-linear? (term Σ) (term f) (term (T ...)) (term (σ ...))))
   (where (τ_a ...) ,(for/list ([t (term (τ_p ...))]) (subst t (term (T ...)) (term (σ ...)))))
   (where τ_ra ,(subst (term τ_r) (term (T ...)) (term (σ ...))))
   (chk-args-each Σ Γ Λ (e ...) (τ_a ...) (L_a ...) Γ_1)
   (where L ,(borrowed-loans (term Σ) (term f) (term (x_p ...)) (term (L_a ...))))
   (where L_r ,(if (and (second-class? (term τ_ra)) (not (mutant? 'no-call-loans))) (term L) '()))
   (where Γ_2 ,(for/fold ([g (term Γ_1)]) ([a (term (e ...))])
                 (match a [`(out ,p) (mark-filled g p)] [_ g])))
   -------------------------------------------- "call"
   (chk Σ Γ Λ (call f (σ ...) e ...) τ_ra L_r Γ_2)]

  ;; A closure that borrows: it carries the loans of what it captured, and its
  ;; body is a function of its own over the captures and the parameters.
  [(side-condition ,(andmap (λ (t) (and (second-class? t) (not (dropped-view? (term Σ) t))
                                        (not (match t [`(out ,_) #t] [_ #f]))))
                            (term (τ_c ...))))
   (chk-args Σ Γ Λ (e_c ...) (τ_c ...) L Γ_1)
   (where k ,(if (ormap (λ (t) (exclusive? (term Σ) t)) (term (τ_c ...))) 'mut 'shr))
   (side-condition ,(check-closure (term Σ) (term ((x_c τ_c) ...)) (term ((x τ) ...)) (term τ_r) (term e_b) #f))
   (where L_f ,(if (mutant? 'clo-no-loans) '() (term L)))
   -------------------------------------------- "lam"
   (chk Σ Γ Λ (lam ([x_c τ_c e_c] ...) ((x τ) ...) τ_r e_b) (fnb k (τ ...) τ_r) L_f Γ_1)]

  ;; A closure that owns what it captured, which is moved into it: it is
  ;; storable, and calling it may change what it holds.
  [(side-condition ,(or (mutant? 'clo-own-ref) (andmap (λ (t) (not (second-class? t))) (term (τ_c ...)))))
   (side-condition ,(not (ormap (λ (t) (lin? (term Σ) t)) (term (τ_c ...)))))
   (chk-args Σ Γ Λ (e_c ...) (τ_c ...) L Γ_1)
   (side-condition ,(check-closure (term Σ) (term ((x_c τ_c) ...)) (term ((x τ) ...)) (term τ_r) (term e_b) #t))
   -------------------------------------------- "lamo"
   (chk Σ Γ Λ (lamo ([x_c τ_c e_c] ...) ((x τ) ...) τ_r e_b) (fno (τ ...) τ_r) () Γ_1)]

  ;; Calling a closure that borrows uses what it borrowed: its result carries
  ;; those loans, and a loan on the closure itself, exclusive when it captured
  ;; something exclusively. It is lent so while its arguments are evaluated.
  [(where (fnb k (τ_a ...) τ_r) ,(place-type (term Σ) (term Γ) (term x)))
   (side-condition ,(available? (term Γ) (term x)))
   (side-condition ,(if (and (eq? (term k) 'mut) (not (mutant? 'clo-shared-call)))
                        (write-ok? (active (Σ+* (term Σ) (term (e ...))) (term Γ) (term Λ)) (term x))
                        (read-ok? (active (Σ+* (term Σ) (term (e ...))) (term Γ) (term Λ)) (term x))))
   (where k_c ,(if (mutant? 'clo-shared-call) 'shr (term k)))
   (where Λ_1 ,(add-loans (term Λ) (term tmp) (term ((x k_c)))))
   (chk-args ,(Σ+ (term Σ) (term x)) Γ Λ_1 (e ...) (τ_a ...) L Γ_1)
   (where L_r ,(if (second-class? (term τ_r))
                   (union (term L) (union (loans-of (term Λ) (term x)) (term ((x k_c)))))
                   '()))
   -------------------------------------------- "apply"
   (chk Σ Γ Λ (apply x e ...) τ_r L_r Γ_1)]

  ;; Calling a closure that owns what it captured changes it: it is lent
  ;; exclusively for the call. Its result can borrow only from the arguments.
  [(where (fno (τ_a ...) τ_r) ,(place-type (term Σ) (term Γ) (term p)))
   (side-condition ,(available? (term Γ) (term p)))
   (side-condition ,(writable? (term Σ) (term Γ) (term p)))
   (side-condition ,(write-ok? (active (Σ+* (term Σ) (term (e ...))) (term Γ) (term Λ)) (term p)))
   (where Λ_1 ,(add-loans (term Λ) (term tmp) (exclusive-loans (term p))))
   (chk-args ,(Σ+ (term Σ) (term p)) Γ Λ_1 (e ...) (τ_a ...) L Γ_1)
   (where L_r ,(if (second-class? (term τ_r)) (term L) '()))
   -------------------------------------------- "apply-own"
   (chk Σ Γ Λ (apply p e ...) τ_r L_r Γ_1)]

  ;; two calls run at the same time: their arguments are checked as the
  ;; arguments of one call, so nothing lent exclusively to one reaches the other
  [(where (defn f_1 (T_1 ...) ((x_1 τ_1) ...) σ_r1 any_1) ,(find-decl (term Σ) 'defn (term f_1)))
   (where (defn f_2 (T_2 ...) ((x_2 τ_2) ...) σ_r2 any_2) ,(find-decl (term Σ) 'defn (term f_2)))
   (side-condition ,(and (= (length (term (T_1 ...))) (length (term (σ_1 ...))))
                         (= (length (term (T_2 ...))) (length (term (σ_2 ...))))
                         (andmap (λ (t) (wf? (term Σ) t)) (term (σ_1 ... σ_2 ...)))))
   (side-condition ,(and (admits-linear? (term Σ) (term f_1) (term (T_1 ...)) (term (σ_1 ...)))
                         (admits-linear? (term Σ) (term f_2) (term (T_2 ...)) (term (σ_2 ...)))))
   ;; what the two calls give is thrown away: never something linear
   (side-condition ,(or (mutant? 'linear-discard)
                        (not (or (lin? (term Σ) (subst (term σ_r1) (term (T_1 ...)) (term (σ_1 ...))))
                                 (lin? (term Σ) (subst (term σ_r2) (term (T_2 ...)) (term (σ_2 ...))))))))
   (where (τ_a1 ...) ,(for/list ([t (term (τ_1 ...))]) (subst t (term (T_1 ...)) (term (σ_1 ...)))))
   (where (τ_a2 ...) ,(for/list ([t (term (τ_2 ...))]) (subst t (term (T_2 ...)) (term (σ_2 ...)))))
   (chk-args ,(Σ+* (term Σ) (term (e_2 ...))) Γ Λ (e_1 ...) (τ_a1 ...) L_1 Γ_1)
   (where Λ_2 ,(if (mutant? 'par-split) (term Λ) (add-loans (term Λ) (term tmp) (par-loans (term Σ) (term Γ_1) (term Λ) (term L_1)))))
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
   (side-condition ,(admits-linear? (term Σ) (term f) (term (T ...)) (term (σ ...))))
   (side-condition ,(or (mutant? 'spawn-ref) (not (ormap second-class? (term (τ_a ...))))))
   (where σ_ra ,(subst (term σ_r) (term (T ...)) (term (σ ...))))
   (chk-args Σ Γ Λ (e ...) (τ_a ...) L Γ_1)
   -------------------------------------------- "spawn"
   (chk Σ Γ Λ (spawn (call f (σ ...) e ...)) (task σ_ra) () Γ_1)]

  ;; a closure that owns what it captured, run on a thread of its own
  [(chk Σ Γ Λ e (fno () σ) () Γ_1)
   -------------------------------------------- "spawn-fn"
   (chk Σ Γ Λ (spawn-fn e) (task σ) () Γ_1)]

  [(chk Σ Γ Λ e (task σ) () Γ_1)
   -------------------------------------------- "join"
   (chk Σ Γ Λ (join e) σ () Γ_1)]

  ;; ---- globals: lent for a scope, with exclusivity checked when it is entered

  [(where (global g σ any_i) ,(find-decl (term Σ) 'global (term g)))
   (side-condition ,(not (assq (term x) (term Γ))))
   (where Λ_1 ,(cons (list (term x) (term (glob g)) (if (eq? (term w) 'mut) 'mut 'shr)) (term Λ)))
   (where Γ_b ,(bind-var (term Γ) (term x) (term (w σ))))
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

;; Two-phase borrows: an argument lent exclusively is only reserved while the
;; arguments after it are evaluated (they may read it, never write or move it),
;; and is lent exclusively when the call begins, when no other argument may still
;; hold a loan on any of it.
(define (reserve L)
  (for/list ([l L]) (match l [(list p 'mut) (list p 'shr)] [_ l])))
(define (args-apart? L1 L2)
  (or (mutant? 'two-phase-unchecked)
      (not (for*/or ([a L1] [b L2])
             (and (or (eq? (cadr a) 'mut) (eq? (cadr b) 'mut))
                  (overlap? (car a) (car b)))))))

;; arguments, left to right: each one's loans are alive while the rest are evaluated
(define-judgment-form Safe
  #:mode (chk-args I I I I I O O)
  #:contract (chk-args Σ Γ Λ (e ...) (τ ...) L Γ)

  [-------------------------------------------- "no-args"
   (chk-args Σ Γ Λ () () () Γ)]

  ;; a closure that borrows shared goes where one that may borrow exclusively is asked for
  [(chk ,(Σ+* (term Σ) (term (e_r ...))) Γ Λ e_1 τ_a L_1 Γ_1)
   (side-condition ,(fits? (term τ_a) (term τ_1)))
   (where Λ_1 ,(add-loans (term Λ) (term tmp) (if (mutant? 'no-arg-loans) '() (reserve (term L_1)))))
   (chk-args Σ Γ_1 Λ_1 (e_r ...) (τ_r ...) L_2 Γ_2)
   (side-condition ,(args-apart? (term L_1) (term L_2)))
   (where L ,(union (term L_1) (term L_2)))
   -------------------------------------------- "arg"
   (chk-args Σ Γ Λ (e_1 e_r ...) (τ_1 τ_r ...) L Γ_2)])

;; the same, with each argument's loans apart
(define-judgment-form Safe
  #:mode (chk-args-each I I I I I O O)
  #:contract (chk-args-each Σ Γ Λ (e ...) (τ ...) (L ...) Γ)

  [-------------------------------------------- "no-args-each"
   (chk-args-each Σ Γ Λ () () () Γ)]

  [(chk ,(Σ+* (term Σ) (term (e_r ...))) Γ Λ e_1 τ_a L_1 Γ_1)
   (side-condition ,(fits? (term τ_a) (term τ_1)))
   (where Λ_1 ,(add-loans (term Λ) (term tmp) (if (mutant? 'no-arg-loans) '() (reserve (term L_1)))))
   (chk-args-each Σ Γ_1 Λ_1 (e_r ...) (τ_r ...) (L_r ...) Γ_2)
   (side-condition ,(args-apart? (term L_1) (foldl union '() (term (L_r ...)))))
   -------------------------------------------- "arg-each"
   (chk-args-each Σ Γ Λ (e_1 e_r ...) (τ_1 τ_r ...) (L_1 L_r ...) Γ_2)])

;; one arm: x holds the payload (or a reference to it, carrying L_x)
(define-judgment-form Safe
  #:mode (chk-arm I I I I I I I O O O)
  #:contract (chk-arm Σ Γ Λ x τ L e τ L Γ)

  [(side-condition ,(not (assq (term x) (term Γ))))
   (where Λ_1 ,(add-loans (term Λ) (term x) (if (mutant? 'match-no-loans) '() (term L_x))))
   (where Γ_b ,(bind-var (term Γ) (term x) (term τ_x)))
   (chk Σ Γ_b Λ_1 e τ L_2 Γ_2)
   (side-condition ,(not (lin-dropped? (term Σ) (term x) (term Γ_2))))
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
   (where Γ_3 ,(if (mutant? 'no-join) (term Γ_1) (join (term Σ) (term Γ_1) (term Γ_2))))
   -------------------------------------------- "arms"
   (chk-arms Σ Γ Λ (((K x) e) any_a any_r ...) (τ_x τ_y τ_r ...) L_x τ L Γ_3)])

;; ---------------------------------------------------------------- programs

(define (distinct? xs) (not (check-duplicates xs)))
(define (one-answer who rs)
  (match rs
    ['() #f]
    [(list r) r]
    [_ (error who "the rules gave more than one answer: ~a" rs)]))

;; Leaving a function, early or at its end, with a value carrying L: every
;; local's scope ends (newest first), and then the parameters'. The value may
;; carry only the loans the caller lent: nothing on the function's own storage,
;; nothing on a global, whose loan lasts only for its `with`. What an exclusive
;; or out parameter refers to must be whole.
(define (return-ok? Σ Γ Λ L params [only 'all])
  (define vars (vars-of Γ))
  (define after-locals
    (for/fold ([L L]) ([e vars] #:unless (memq (car e) params))
      (and L (exit-scope (car e) (cadr e) Λ L))))
  (define after-params
    (for/fold ([L after-locals]) ([e vars] #:when (memq (car e) params))
      (and L (exit-scope (car e) (cadr e) Λ L))))
  (and after-params
       (not (for/or ([l after-params]) (match (place-root (car l)) [`(glob ,_) #t] [_ #f])))
       ;; with a `borrows`, only on what the parameters it names were lent
       (or (eq? only 'all) (mutant? 'borrows-unchecked)
           (for/and ([l after-params])
             (match (place-root (car l)) [`(ext ,x) (and (memq x only) #t)] [_ #t])))
       (for/and ([e vars] #:when (memq (car e) params))
         (restored? Σ (car e) (cadr e) (caddr e)))
       ;; nor is anything linear dropped, a parameter's or a local's
       (or (mutant? 'linear-scope)
           (for/and ([e vars]) (not (lin-left? Σ (cadr e) (caddr e)))))))

;; The body of a function, a closure or a drop: its parameters (and a closure's
;; captures, which are parameters to it) hold loans on what the caller lent; an
;; out parameter refers to a place that holds nothing yet.
(define (check-body decls Ts params τr body [only 'all] [lin-Ts '()])
  (define Σ (make-Σ decls Ts (list τr (map car params) only) lin-Ts))
  (define Γ (for/list ([p params])
              (list (car p) (cadr p) (match (cadr p) [`(out ,_) '(gone (*))] [_ 'live]) 'none)))
  (define Λ (for/list ([p params] #:when (second-class? (cadr p)))
              (list (car p) `(ext ,(car p)) (kind-of Σ (cadr p)))))
  (and (distinct? (map car params))
       (andmap (λ (p) (wf? Σ (cadr p))) params)
       (wf? Σ τr)
       (match (one-answer 'check-body (judgment-holds (chk ,Σ ,Γ ,Λ ,body τ L Γ_out) (τ L Γ_out)))
         [(list τ L Γ-out)
          (and (equal? τ τr)
               (or (dead? Γ-out)
                   (mutant? 'no-return-check)
                   (return-ok? Σ Γ-out Λ L (map car params) only)))]
         [#f #f])
       Γ))

;; A closure's body, over its captures and its parameters. An owning closure's
;; captures stay in it from one call to the next, so the body must leave them
;; there; a borrowing closure's are references, made again for every call.
(define (check-closure Σ caps params τr body own?)
  (define decls (decls-of Σ))
  (define all (append caps params))
  (and (distinct? (map car all))
       (andmap (λ (c) (wf? Σ (cadr c))) caps)
       (let ([Σb (make-Σ decls (tparams Σ) (list τr (map car all) 'all) (Σ-lin-Ts Σ))]
             [Γ (for/list ([p all])
                  (list (car p) (cadr p) (match (cadr p) [`(out ,_) '(gone (*))] [_ 'live]) 'none))]
             [Λ (for/list ([p all] #:when (second-class? (cadr p)))
                  (list (car p) `(ext ,(car p)) (kind-of Σ (cadr p))))])
         (and (andmap (λ (p) (wf? Σb (cadr p))) params)
              (wf? Σb τr)
              (match (one-answer 'check-closure (judgment-holds (chk ,Σb ,Γ ,Λ ,body τ L Γ_out) (τ L Γ_out)))
                [(list τ L Γ-out)
                 (and (equal? τ τr)
                      (or (dead? Γ-out) (return-ok? Σb Γ-out Λ L (map car all)))
                      (or (not own?) (mutant? 'clo-moves)
                          (dead? Γ-out)
                          (for/and ([c caps]) (eq? (state-of Γ-out (car c)) 'live))))]
                [#f #f])))))

(define (check-fn decls fn)
  (match fn
    [`(defn ,f ,Ts ,params ,τr ,body)
     (and (distinct? (append Ts (decl-names decls)))
          (check-body decls Ts params τr body (borrows-of decls f) (lin-Ts-of decls f Ts))
          #t)]))

;; The names the declarations define: a `borrows` defines none, it says more
;; about a function.
(define (decl-names decls)
  (map cadr (filter (λ (d) (not (memq (car d) '(borrows linear droppable)))) decls)))

;; The parameters f's `borrows` names, or `all`.
(define (borrows-of decls f)
  (or (for/first ([d decls] #:when (and (eq? (car d) 'borrows) (eq? (cadr d) f))) (caddr d))
      'all))

;; The loans a call's result may carry: those of every argument, or of the ones
;; the callee's `borrows` names.
(define (borrowed-loans Σ f params Ls)
  (define only (borrows-of (decls-of Σ) f))
  (for/fold ([L '()]) ([x params] [l Ls])
    (if (or (eq? only 'all) (memq x only)) (union L l) L)))

;; a global's first value is built without running any of the program
(define (constant? e)
  (not (let loop ([t e])
         (and (pair? t)
              (or (memq (car t) '(call par spawn spawn-fn join with unsafe while load store alloc free
                                  lam lamo apply return out))
                  (ormap loop t))))))

(define (check-decl decls d)
  (match d
    [`(,(or 'struct 'sum) ,_ ,Ts ((,names ,ts) ...))
     (and (distinct? Ts) (distinct? names)
          (distinct? (append Ts (decl-names decls)))
          (andmap (λ (t) (wf? (make-Σ decls Ts) t)) ts))]
    [`(view ,V ((,names ,ts) ...) . ,drop)
     (define Σ (make-Σ decls))
     (and (distinct? names) (andmap (λ (t) (wf? Σ t)) ts)
          ;; a view holds no view that holds it
          (not (let inside? ([t `(view ,V)] [seen '()])
                 (for/or ([f (or (fields-of Σ t) '())])
                   (match (cadr f)
                     [`(view ,W) (or (eq? W V) (and (not (memq W seen)) (inside? (cadr f) (cons W seen))))]
                     [_ #f]))))
          ;; the function its drop runs takes the view and gives nothing back
          (match drop
            ['() #t]
            [(list f) (match (find-decl Σ 'defn f)
                        [`(defn ,_ () ((,_ (view ,(== V)))) unit ,_) #t]
                        [_ #f])]))]
    ;; a struct of the program's
    [`(linear ,S)
     (and (match (find-decl (make-Σ decls) 'struct S) [`(struct . ,_) #t] [_ #f])
          (= 1 (for/sum ([e decls]) (if (and (eq? (car e) 'linear) (eq? (cadr e) S)) 1 0))))]
    ;; a function's own type parameters
    [`(droppable ,f ,Ts)
     (match (for/first ([e decls] #:when (and (eq? (car e) 'defn) (eq? (cadr e) f))) e)
       [`(defn ,_ ,fTs . ,_) (and (distinct? Ts) (andmap (λ (T) (memq T fTs)) Ts) #t)]
       [#f #f])]
    ;; a global lives for the whole program, and is never dropped: it holds
    ;; nothing linear, which would then outlive the program's obligations
    [`(global ,_ ,σ ,e)
     (and (wf? (make-Σ decls) σ)
          (not (lin? (make-Σ decls) σ))
          (constant? e)
          (equal? (one-answer 'check-decl (judgment-holds (chk ,(make-Σ decls) () () ,e τ L Γ) τ)) σ))]
    [`(defn . ,_) (check-fn decls d)]
    ;; names a function, once, and only parameters of it that take a reference
    [`(borrows ,f ,xs)
     (match (for/first ([e decls] #:when (and (eq? (car e) 'defn) (eq? (cadr e) f))) e)
       [`(defn ,_ ,_ ,params ,_ ,_)
        (and (distinct? xs)
             (= 1 (for/sum ([e decls]) (if (and (eq? (car e) 'borrows) (eq? (cadr e) f)) 1 0)))
             (for/and ([x xs])
               (match (assq x params)
                 [(list _ t) (second-class? t)]
                 [#f #f])))]
       [#f #f])]))

(define (check-program prog)
  (match prog
    [`(program ,decls ,main)
     (and (redex-match? Safe prog prog)
          (distinct? (decl-names decls))
          (andmap (λ (d) (check-decl decls d)) decls)
          (match (one-answer 'check-program (judgment-holds (chk ,(make-Σ decls) () () ,main τ L Γ) (τ L)))
            [(list τ '()) (not (second-class? τ))]
            [_ #f]))]
    [_ #f]))
