#lang racket
;; The static rules of safe Coil, as a PLT Redex model.
;;
;; The calculus keeps only what the rules are about: owners (a box is a heap
;; allocation freed when its owner goes out of scope), moves, and second-class
;; references. A reference can be a local, an argument or a result; it can never
;; be stored (a box holds only storable types, and a reference is not one).
;;
;; The judgment is algorithmic:   (chk F Γ Λ e τ L Γ′)
;;   F   the program's functions
;;   Γ   each variable in scope, its type, and whether it has been moved
;;   Λ   the loans alive here: who holds each, on which place, shared or exclusive
;;   τ   the type of e
;;   L   the loans the VALUE of e carries (empty unless τ is a reference)
;;   Γ′  Γ after e's moves
;; Λ is an input only: a loan lives exactly as long as the scope of its holder.
(require redex/reduction-semantics)
(provide Safe chk chk-args check-program check-fn
         enforce-exclusive? enforce-escape? enforce-moves? mutant mutants)

;; Redex remembers a judgment's answer for its inputs. The switches below are not
;; inputs, so a remembered answer would be given under a different switch.
(caching-enabled? #f)

;; Switches for testing the tests: with one off, the random search must find a
;; program that goes wrong. They are never off in a real check.
(define enforce-exclusive? (make-parameter #t))
(define enforce-escape? (make-parameter #t))
(define enforce-moves? (make-parameter #t))
;; Finer: one part of one rule left out. Each of these must be found too.
(define mutant (make-parameter #f))
(define mutants
  '((no-call-loans "a returned reference carries no loans from the call's arguments")
    (no-arg-loans "an argument's loans are not alive while later arguments are evaluated")
    (no-return-check "a function may return a reference to its own storage")
    (no-let-loans "a let-bound reference holds no loans")
    (write-through-shared "a place behind a shared reference can be written")
    (copy-mut "an exclusive reference is copied, not moved")
    (no-join "a move in the else branch is forgotten")
    (no-union "the loans of the else branch are forgotten")))
(define (mutant? m) (eq? (mutant) m))

(define-language Safe
  (prog ::= (program (fn ...) e))
  (fn ::= (defn f ((x τ) ...) τ e))
  ;; storable types, and all types
  (σ ::= int unit (box σ))
  (τ ::= σ (ref σ) (mut σ))
  (e ::= n unit p
         (let ([x e]) e) (seq e e) (box e) (ref p) (mut p)
         (set! p e) (call f e ...) (if0 e e e) (+ e e))
  (p ::= x (* p))
  (n ::= integer)
  (k ::= shr mut)
  (s ::= live moved)
  (Γ ::= ((x τ s) ...))
  ;; a loan's place is rooted at a local, or at what a reference parameter refers to
  (q ::= x (ext x) (* q))
  (L ::= ((q k) ...))
  (h ::= x tmp)
  (Λ ::= ((h q k) ...))
  (F ::= (fn ...))
  (x f ::= variable-not-otherwise-mentioned))

;; ---------------------------------------------------------------- helpers

(define (ref-type? τ) (and (pair? τ) (memq (car τ) '(ref mut)) #t))
(define (kind-of τ) (if (eq? (car τ) 'ref) 'shr 'mut))

(define (lookup Γ x)
  (match (assq x Γ)
    [(list _ τ 'live) τ]
    [(list _ τ 'moved) (if (enforce-moves?) #f τ)]
    [_ #f]))

(define (place-root q) (match q [`(* ,q2) (place-root q2)] [_ q]))

(define (place-type Γ p)
  (match p
    [(? symbol? x) (lookup Γ x)]
    [`(* ,p2) (match (place-type Γ p2)
                [`(,(or 'box 'ref 'mut) ,σ) σ]
                [_ #f])]))

;; a place can be written when no step of its path goes through a shared reference
(define (writable? Γ p)
  (match p
    [(? symbol?) #t]
    [`(* ,p2) (and (or (mutant? 'write-through-shared)
                       (match (place-type Γ p2) [`(,(or 'box 'mut) ,_) #t] [_ #f]))
                   (writable? Γ p2))]))

(define (prefix? a b)
  (or (equal? a b) (match b [`(* ,b2) (prefix? a b2)] [_ #f])))
(define (overlap? a b) (or (prefix? a b) (prefix? b a)))

;; reading p: nobody holds an exclusive loan on any part of it
(define (read-ok? Λ p)
  (or (not (enforce-exclusive?))
      (for/and ([l Λ]) (match l [(list _ q k) (not (and (eq? k 'mut) (overlap? q p)))]))))
;; writing, moving or exclusively borrowing p: nobody holds any loan on any part of it
(define (write-ok? Λ p)
  (or (not (enforce-exclusive?))
      (for/and ([l Λ]) (match l [(list _ q _) (not (overlap? q p))]))))

(define (loans-of Λ x)
  (remove-duplicates (for/list ([l Λ] #:when (eq? (car l) x)) (cdr l))))
(define (add-loans Λ h L)
  (append (for/list ([l L]) (cons h l)) Λ))
(define (union L1 L2) (remove-duplicates (append L1 L2)))

;; the loans a shared borrow of p carries: through a shared reference, that
;; reference's own loans; otherwise a shared loan on p itself
(define (shared-loans Γ Λ p)
  (define root (place-root p))
  (match (lookup Γ root)
    [`(ref ,_) (loans-of Λ root)]
    [_ `((,p shr))]))

;; x of type τ leaves scope while a value carrying L leaves with it. A loan on x's
;; own storage cannot leave (#f); a loan through a reference x becomes x's loans.
(define (exit-scope x τ Λ L)
  (let loop ([L L] [acc '()])
    (match L
      ['() (remove-duplicates (reverse acc))]
      [(cons (list q k) rest)
       (cond [(not (eq? (place-root q) x)) (loop rest (cons (list q k) acc))]
             [(ref-type? τ) (loop rest (append (reverse (loans-of Λ x)) acc))]
             [(enforce-escape?) #f]
             [else (loop rest acc)])])))

(define (mark-moved Γ x)
  (if (enforce-moves?)
      (for/list ([b Γ]) (if (eq? (car b) x) (list x (cadr b) 'moved) b))
      Γ))
(define (remove-var Γ x) (filter (λ (b) (not (eq? (car b) x))) Γ))
(define (join Γ1 Γ2)
  (for/list ([a Γ1] [b Γ2])
    (list (car a) (cadr a) (if (and (eq? (caddr a) 'live) (eq? (caddr b) 'live)) 'live 'moved))))
(define (find-fn F f)
  (for/first ([fn F] #:when (eq? (cadr fn) f)) fn))

;; ---------------------------------------------------------------- the rules

(define-judgment-form Safe
  #:mode (chk I I I I O O O)
  #:contract (chk F Γ Λ e τ L Γ)

  [-------------------------------------------- "int"
   (chk F Γ Λ n int () Γ)]

  [-------------------------------------------- "unit"
   (chk F Γ Λ unit unit () Γ)]

  [(chk F Γ Λ e_1 int L_1 Γ_1)
   (chk F Γ_1 Λ e_2 int L_2 Γ_2)
   -------------------------------------------- "add"
   (chk F Γ Λ (+ e_1 e_2) int () Γ_2)]

  ;; reading a place that holds plain data copies it
  [(where σ ,(place-type (term Γ) (term p)))
   (side-condition ,(memq (term σ) '(int unit)))
   (side-condition ,(read-ok? (term Λ) (term p)))
   -------------------------------------------- "copy"
   (chk F Γ Λ p σ () Γ)]

  ;; naming an owner moves it; only a whole variable can be moved
  [(where (box σ) ,(lookup (term Γ) (term x)))
   (side-condition ,(write-ok? (term Λ) (term x)))
   (where Γ_1 ,(mark-moved (term Γ) (term x)))
   -------------------------------------------- "move"
   (chk F Γ Λ x (box σ) () Γ_1)]

  ;; a shared reference is copied, and the copy carries the same loans
  [(where (ref σ) ,(lookup (term Γ) (term x)))
   (where L ,(loans-of (term Λ) (term x)))
   -------------------------------------------- "copy-ref"
   (chk F Γ Λ x (ref σ) L Γ)]

  ;; an exclusive reference is moved, and must not be reborrowed at the time
  [(where (mut σ) ,(lookup (term Γ) (term x)))
   (side-condition ,(write-ok? (term Λ) (term x)))
   (where L ,(loans-of (term Λ) (term x)))
   (where Γ_1 ,(if (mutant? 'copy-mut) (term Γ) (mark-moved (term Γ) (term x))))
   -------------------------------------------- "move-mut"
   (chk F Γ Λ x (mut σ) L Γ_1)]

  [(where σ ,(place-type (term Γ) (term p)))
   (side-condition ,(read-ok? (term Λ) (term p)))
   (where L ,(shared-loans (term Γ) (term Λ) (term p)))
   -------------------------------------------- "borrow"
   (chk F Γ Λ (ref p) (ref σ) L Γ)]

  [(where σ ,(place-type (term Γ) (term p)))
   (side-condition ,(writable? (term Γ) (term p)))
   (side-condition ,(write-ok? (term Λ) (term p)))
   -------------------------------------------- "borrow-mut"
   (chk F Γ Λ (mut p) (mut σ) ((p mut)) Γ)]

  [(chk F Γ Λ e σ () Γ_1)
   -------------------------------------------- "box"
   (chk F Γ Λ (box e) (box σ) () Γ_1)]

  ;; the loans of e_1's value belong to x until x's scope ends
  [(chk F Γ Λ e_1 τ_1 L_1 Γ_1)
   (side-condition ,(not (assq (term x) (term Γ_1))))
   (where Λ_2 ,(add-loans (term Λ) (term x) (if (mutant? 'no-let-loans) '() (term L_1))))
   (where Γ_b ,(cons (term (x τ_1 live)) (term Γ_1)))
   (chk F Γ_b Λ_2 e_2 τ_2 L_2 Γ_2)
   (where L_3 ,(exit-scope (term x) (term τ_1) (term Λ_2) (term L_2)))
   (where Γ_3 ,(remove-var (term Γ_2) (term x)))
   -------------------------------------------- "let"
   (chk F Γ Λ (let ([x e_1]) e_2) τ_2 L_3 Γ_3)]

  [(chk F Γ Λ e_1 τ_1 L_1 Γ_1)
   (chk F Γ_1 Λ e_2 τ_2 L_2 Γ_2)
   -------------------------------------------- "seq"
   (chk F Γ Λ (seq e_1 e_2) τ_2 L_2 Γ_2)]

  ;; the new value is computed first; then the place must be whole, reachable
  ;; for writing, and free of loans, because its old value is dropped
  [(chk F Γ Λ e σ () Γ_1)
   (where σ ,(place-type (term Γ_1) (term p)))
   (side-condition ,(writable? (term Γ_1) (term p)))
   (side-condition ,(write-ok? (term Λ) (term p)))
   -------------------------------------------- "set"
   (chk F Γ Λ (set! p e) unit () Γ_1)]

  [(chk F Γ Λ e_1 int L_1 Γ_1)
   (chk F Γ_1 Λ e_2 τ L_2 Γ_2)
   (chk F Γ_1 Λ e_3 τ L_3 Γ_3)
   (where L ,(if (mutant? 'no-union) (term L_2) (union (term L_2) (term L_3))))
   (where Γ_4 ,(if (mutant? 'no-join) (term Γ_2) (join (term Γ_2) (term Γ_3))))
   -------------------------------------------- "if0"
   (chk F Γ Λ (if0 e_1 e_2 e_3) τ L Γ_4)]

  ;; a returned reference borrows from every reference argument of the call
  [(where (defn f ((x_p τ_p) ...) τ_r e_b) ,(find-fn (term F) (term f)))
   (chk-args F Γ Λ (e ...) (τ_p ...) L Γ_1)
   (where L_r ,(if (and (ref-type? (term τ_r)) (not (mutant? 'no-call-loans))) (term L) '()))
   -------------------------------------------- "call"
   (chk F Γ Λ (call f e ...) τ_r L_r Γ_1)])

;; arguments, left to right: each one's loans are alive while the rest are evaluated
(define-judgment-form Safe
  #:mode (chk-args I I I I I O O)
  #:contract (chk-args F Γ Λ (e ...) (τ ...) L Γ)

  [-------------------------------------------- "no-args"
   (chk-args F Γ Λ () () () Γ)]

  [(chk F Γ Λ e_1 τ_1 L_1 Γ_1)
   (where Λ_1 ,(add-loans (term Λ) (term tmp) (if (mutant? 'no-arg-loans) '() (term L_1))))
   (chk-args F Γ_1 Λ_1 (e_r ...) (τ_r ...) L_2 Γ_2)
   (where L ,(union (term L_1) (term L_2)))
   -------------------------------------------- "arg"
   (chk-args F Γ Λ (e_1 e_r ...) (τ_1 τ_r ...) L Γ_2)])

;; ---------------------------------------------------------------- programs

;; A function's reference parameters hold loans on what the caller lent. Its
;; result may carry only those: nothing rooted at the function's own storage.
(define (check-fn F fn)
  (match fn
    [`(defn ,_ ,params ,τr ,body)
     (and (not (check-duplicates (map car params)))
          (let* ([Γ (for/list ([p params]) (list (car p) (cadr p) 'live))]
                 [Λ (for/list ([p params] #:when (ref-type? (cadr p)))
                      (list (car p) `(ext ,(car p)) (kind-of (cadr p))))]
                 [rs (judgment-holds (chk ,F ,Γ ,Λ ,body τ L Γ) (τ L))])
            (match rs
              [(list (list τ L))
               (and (equal? τ τr)
                    (or (mutant? 'no-return-check)
                        (for/fold ([L L]) ([p params])
                          (and L (exit-scope (car p) (cadr p) Λ L))))
                    #t)]
              ['() #f]
              [_ (error 'check-fn "the rules gave more than one answer: ~a" rs)])))]))

(define (check-program prog)
  (match prog
    [`(program ,F ,main)
     (and (redex-match? Safe prog prog)
          (not (check-duplicates (map cadr F)))
          (andmap (λ (fn) (check-fn F fn)) F)
          (match (judgment-holds (chk ,F () () ,main τ L Γ) (τ L))
            [(list (list τ '())) (not (ref-type? τ))]
            ['() #f]
            [(list _) #f]
            [rs (error 'check-program "the rules gave more than one answer: ~a" rs)]))]))
