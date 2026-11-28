#lang racket
;; A model program as Coil source, for checking the Coil checker against the
;; model: `safe.check` must accept what `check-program` accepts and refuse what
;; it refuses.
;;
;; (program->coil prog module-name) -> a string, or #f with a reason when Coil
;; has nothing the program could be written with:
;;   - an exclusive reference read out of a view's field as a value: the model
;;     has no rule for it, and Coil would lend through it again instead;
;;   - `match-mut` on a sum with a plain-data payload: Coil copies such a
;;     payload into the arm and lends only the parts that own something;
;;   - an out parameter, or a variable made with nothing in it: Coil has neither;
;;   - a closure capture that is not a borrow of a place or a variable holding a
;;     reference.
;;
;; A closure type `(fnb k (τ…) τ)` or `(fno (τ…) τ)` is a `deffn` type of safe.fn,
;; one per parameter and result types (`F<n>`, and `F<n>-own` for one that owns
;; what it captured). A function with a `return` in it has its body in a block
;; `:ret` that the return leaves.

(require "rules.rkt")
(provide program->coil)

(struct untranslatable (why))
(define (bail why) (raise (untranslatable why)))

(define (fn-name f) (format "f-~a" f))
(define (var-name x) (format "v-~a" x))
(define (type-name S) (format "M~a" S))
(define (variant-name K) (format "K~a" K))
;; A view is a Coil struct marked `View`. Coil does not let a struct hold a
;; reference, so a field that is one is a raw pointer, read through a function
;; that lends what it points at: `W<V>-<field>`, and `W<V>-<field>-mut` for an
;; exclusive one.
(define (view-name V) (format "W~a" V))
;; is the closure being written the value a `let` binds? Only one that a name
;; holds can be erased, which is the type the model gives it
(define lambda-bound (make-parameter #f))
;; the closure types of the program being written: (τs τr) -> its deffn name
(define closure-names (make-parameter (make-hash)))
(define (closure-name τs τr)
  (hash-ref! (closure-names) (list τs τr) (λ () (format "F~a" (hash-count (closure-names))))))

;; ---------------------------------------------------------------- types

(define (coil-type τ)
  (match τ
    ['int "i64"]
    ['unit "i64"]
    [`(box ,σ) (format "(Box ~a)" (coil-type σ))]
    ['arena "Arena"]
    [`(abox ,σ) (format "(BoxIn ~a ArenaRef)" (coil-type σ))]
    [`(ptr ,σ) (format "(ptr ~a)" (coil-type σ))]
    [`(pool ,σ) (format "(Pool ~a)" (coil-type σ))]
    [`(handle ,σ) (format "(Handle ~a)" (coil-type σ))]
    [`(task ,σ) (format "(Task ~a)" (coil-type σ))]
    [`(ref ,σ) (format "(ref ~a)" (coil-type σ))]
    [`(mut ,σ) (format "(mut ~a)" (coil-type σ))]
    [`(view ,V) (view-name V)]
    ;; a closure is erased: one that borrows is a `-view`, one that owns an `-own`
    [`(fnb ,_ ,τs ,τr) (when (second-class? τr) (bail "a closure that returns a reference"))
                      (format "~a-view" (closure-name τs τr))]
    [`(fno ,τs ,τr) (when (second-class? τr) (bail "a closure that returns a reference"))
                    (format "~a-own" (closure-name τs τr))]
    [`(out ,σ) (format "(out ~a)" (coil-type σ))]
    [(? symbol? T) (symbol->string T)]
    [(list S) (type-name S)]
    [(cons S args) (format "(~a ~a)" (type-name S) (string-join (map coil-type args)))]))

(define (ref? τ) (match τ [`(,(or 'ref 'mut) ,_) #t] [_ #f]))
(define (mut? τ) (match τ [`(mut ,_) #t] [_ #f]))
(define (view? τ) (match τ [`(view ,_) #t] [_ #f]))
(define (closure? τ) (match τ [`(fnb . ,_) #t] [_ #f]))
;; a view Coil moves rather than copies: one with an exclusive reference in it,
;; or a drop of its own
(define (moved-view? Σ τ) (and (view? τ) (or (exclusive? Σ τ) (and (view-drop Σ τ) #t))))

;; ---------------------------------------------------------------- the model's types, without its loans

(define (lookup Γ x) (cond [(assq x Γ) => cdr] [else (bail "an unbound variable")]))

(define (place-type Σ Γ p)
  (match p
    [(? symbol? x) (lookup Γ x)]
    [`(* ,q) (match (place-type Σ Γ q)
               [`(,(or 'box 'ref 'mut 'abox) ,σ) σ]
               [_ (bail "an ill-typed program")])]
    [`(: ,q ,fld) (match (assq fld (or (fields-of Σ (place-type Σ Γ q)) '()))
                    [(list _ t) t]
                    [_ (bail "an ill-typed program")])]
    [`(at ,q ,_) (match (place-type Σ Γ q)
                   [`(pool ,σ) σ]
                   [_ (bail "an ill-typed program")])]
    ;; what is no place: the rules refuse the program
    [_ (bail "an ill-typed program")]))

;; the view q is, when `(: q fld)` is a reference held in a view; else #f
(define (view-reference Σ Γ q fld)
  (match (place-type Σ Γ q)
    [`(view ,V) (and (ref? (place-type Σ Γ `(: ,q ,fld))) V)]
    [_ #f]))

(define (place? e)
  (match e
    [(? symbol? x) (not (eq? x 'unit))]
    [`(* ,_) #t]
    [`(: ,_ ,_) #t]
    [`(at ,_ ,_) #t]
    [_ #f]))

;; the program's declarations; Σ is the model's own (see `make-Σ`)
(define current-decls (make-parameter '()))
;; the functions that cannot be written in Coil: a call of one cannot be either
(define unwritten (make-parameter '()))
(define (decl Σ kind name)
  (when (and (eq? kind 'defn) (memq name (unwritten))) (bail "a call of a function Coil cannot express"))
  (or (for/first ([d (current-decls)] #:when (and (eq? (car d) kind) (eq? (cadr d) name))) d)
      (bail "an ill-typed program")))

(define (type-of Σ Γ e)
  (match e
    [(? integer?) 'int]
    ['unit 'unit]
    [(? place?) (place-type Σ Γ e)]
    [`(let ([,x ,e1]) ,e2) (type-of Σ (cons (cons x (type-of Σ Γ e1)) Γ) e2)]
    [`(seq ,_ ,e2) (type-of Σ Γ e2)]
    [`(if0 ,_ ,e2 ,_) (type-of Σ Γ e2)]
    [`(+ ,_ ,_) 'int]
    [`(while ,_ ,_) 'unit]
    [`(break) 'unit]
    [`(return ,_ ,τ) τ]
    [`(uninit ,σ) σ]
    [`(out ,p) `(out ,(place-type Σ Γ p))]
    [`(lam ([,_ ,τcs ,_] ...) ((,_ ,τs) ...) ,τr ,_)
     `(fnb ,(if (ormap (λ (t) (exclusive? Σ t)) τcs) 'mut 'shr) ,τs ,τr)]
    [`(lamo ,_ ((,_ ,τs) ...) ,τr ,_) `(fno ,τs ,τr)]
    [`(apply ,p ,_ ...)
     (match (place-type Σ Γ p)
       [`(fnb ,_ ,_ ,τr) τr]
       [`(fno ,_ ,τr) τr]
       [_ (bail "an ill-typed program")])]
    [`(spawn-fn ,e1) (match (type-of Σ Γ e1) [`(fno () ,σ) `(task ,σ)] [_ (bail "an ill-typed program")])]
    [`(box ,e1) `(box ,(type-of Σ Γ e1))]
    [`(unbox ,e1) (match (type-of Σ Γ e1) [`(,(or 'box 'abox) ,σ) σ] [_ (bail "an ill-typed program")])]
    ['(arena-new) 'arena]
    [`(destroy ,_) 'unit]
    [`(abox ,_ ,e1) `(abox ,(type-of Σ Γ e1))]
    [`(reset! ,_) 'unit]
    [`(ref ,p) `(ref ,(place-type Σ Γ p))]
    [`(mut ,p) `(mut ,(place-type Σ Γ p))]
    [`(set! ,_ ,_) 'unit]
    [`(take ,p ,_) (place-type Σ Γ p)]
    [`(new ,τ ,_ ...) τ]
    [`(inj ,σ ,_ ,_) σ]
    [`(match ,e1 ((,K ,x) ,ea) ,_ ...)
     (type-of Σ (cons (cons x (variant-type Σ (type-of Σ Γ e1) K)) Γ) ea)]
    [`(,(and form (or 'match-ref 'match-mut)) ,p ((,K ,x) ,ea) ,_ ...)
     (type-of Σ (cons (cons x `(,(if (eq? form 'match-ref) 'ref 'mut) ,(variant-type Σ (place-type Σ Γ p) K))) Γ) ea)]
    [`(pool-new ,σ) `(pool ,σ)]
    [`(insert ,p ,_) (match (place-type Σ Γ p) [`(pool ,σ) `(handle ,σ)] [_ (bail "an ill-typed program")])]
    [`(remove ,p ,_) (match (place-type Σ Γ p) [`(pool ,σ) σ] [_ (bail "an ill-typed program")])]
    [`(call ,f ,σs ,_ ...)
     (match (decl Σ 'defn f)
       [`(defn ,_ ,Ts ,_ ,τr ,_)
        (unless (= (length Ts) (length σs)) (bail "an ill-typed program"))
        (subst τr Ts σs)])]
    [`(par ,_ ,_) 'unit]
    [`(spawn (call ,f ,σs ,_ ...))
     (match (decl Σ 'defn f)
       [`(defn ,_ ,Ts ,_ ,τr ,_)
        (unless (= (length Ts) (length σs)) (bail "an ill-typed program"))
        `(task ,(subst τr Ts σs))])]
    [`(join ,e1) (match (type-of Σ Γ e1) [`(task ,σ) σ] [_ (bail "an ill-typed program")])]
    [`(with ,w ,g ,x ,e1)
     (match (decl Σ 'global g)
       [`(global ,_ ,σ ,_) (type-of Σ (cons (cons x `(,w ,σ)) Γ) e1)])]
    [`(unsafe ,e1) (type-of Σ Γ e1)]
    [`(addr ,p) `(ptr ,(place-type Σ Γ p))]
    [`(load ,e1) (match (type-of Σ Γ e1) [`(ptr ,σ) σ] [_ (bail "an ill-typed program")])]
    [`(store ,_ ,_) 'unit]
    [`(alloc ,e1) `(ptr ,(type-of Σ Γ e1))]
    [`(free ,_) 'unit]
    [_ (bail "an ill-typed program")]))

(define (variant-type Σ τ K)
  (match (assq K (or (variants-of Σ τ) '()))
    [(list _ t) t]
    [_ (bail "an ill-typed program")]))

;; ---------------------------------------------------------------- places

;; the place, as an expression that can be lent shared or read through
(define (shared-place Σ Γ p)
  (match p
    [(? symbol? x) (var-name x)]
    [`(* ,q) (match (place-type Σ Γ q)
               [`(box ,_) (format "(Box::get ~a)" (shared-place Σ Γ q))]
               [`(abox ,_) (format "(BoxIn::get ~a)" (shared-place Σ Γ q))]
               [_ (shared-place Σ Γ q)])]
    [`(: ,q ,fld)
     (define V (view-reference Σ Γ q fld))
     (if V
         (format "(~a-~a ~a)" (view-name V) fld (shared-place Σ Γ q))
         (format "(.~a ~a)" fld (shared-place Σ Γ q)))]
    [`(at ,q ,x) (format "(Pool::at ~a ~a)" (shared-place Σ Γ q) (var-name x))]))

;; the place, as an expression `(mut …)` and `(set! …)` take
(define (written-place Σ Γ p)
  (match p
    [(? symbol? x) (var-name x)]
    [`(* ,q) (match (place-type Σ Γ q)
               [`(box ,_) (format "(Box::get-mut (mut ~a))" (written-place Σ Γ q))]
               [`(abox ,_) (format "(BoxIn::get-mut (mut ~a))" (written-place Σ Γ q))]
               [_ (written-place Σ Γ q)])]
    [`(: ,q ,fld)
     (define V (view-reference Σ Γ q fld))
     (cond [(and V (mut? (place-type Σ Γ p)))
            (format "(~a-~a-mut (mut ~a))" (view-name V) fld (written-place Σ Γ q))]
           [V (format "(~a-~a ~a)" (view-name V) fld (shared-place Σ Γ q))]
           [else (format "(.~a ~a)" fld (written-place Σ Γ q))])]
    [`(at ,q ,x) (format "(Pool::at-mut (mut ~a) ~a)" (written-place Σ Γ q) (var-name x))]))

;; is the place's Coil expression a reference, so that reading its value is a load?
(define (behind-reference? Σ Γ p)
  (match p
    [(? symbol? x) (ref? (lookup Γ x))]
    [`(* ,_) #t]
    [`(at ,_ ,_) #t]
    [`(: ,_ ,_) #f]))

;; ---------------------------------------------------------------- expressions

;; e as a value of its type
(define (value Σ Γ e)
  (define τ (type-of Σ Γ e))
  (cond [(mut? τ) (exclusive Σ Γ e)]
        [(ref? τ) (shared Σ Γ e)]
        [else (plain Σ Γ e)]))

;; e, bound by a `let`. Coil makes a name a reference only when it is bound to a
;; call that returns one: a reference from anything else is read through, and
;; the name gets a copy.
(define (bound Σ Γ e)
  (define τ (type-of Σ Γ e))
  (define direct? (match e [(? place?) #t] [`(,(or 'ref 'mut 'call) ,_ ...) #t] [_ #f]))
  (cond [(or direct? (not (ref? τ))) (value Σ Γ e)]
        [(mut? τ) (format "(borrow-mut (mut ~a))" (value Σ Γ e))]
        [else (format "(borrow ~a)" (value Σ Γ e))]))

;; e, evaluated for what it does. Naming a place there reads it, and moves an
;; owner out of it, which a bare name as a Coil statement does not.
;; does e's value come from naming a place, at the end of a seq or a let?
(define (ends-in-place? e)
  (match e
    [(? place?) #t]
    [`(seq ,_ ,e2) (ends-in-place? e2)]
    [`(let ,_ ,e2) (ends-in-place? e2)]
    [_ #f]))
(define (discarded Σ Γ e)
  (define τ (type-of Σ Γ e))
  (cond ;; each branch of a conditional is thrown away on its own
        [(match e [`(if0 ,_ ,e2 ,e3) (or (ends-in-place? e2) (ends-in-place? e3))] [_ #f])
         (match e
           [`(if0 ,e1 ,e2 ,e3)
            (format "(if (= ~a 0) (do ~a 0) (do ~a 0))" (plain Σ Γ e1) (discarded Σ Γ e2) (discarded Σ Γ e3))])]
        [(not (ends-in-place? e)) (value Σ Γ e)]
        [(ref? τ) (value Σ Γ e)]
        ;; a view is never passed for a type parameter; one that is moved has a
        ;; function of its own to take it
        [(view? τ) (if (moved-view? Σ τ)
                       (format "(drop-~a ~a)" (view-name (cadr τ)) (value Σ Γ e))
                       (value Σ Γ e))]
        ;; a closure that borrows is a view of its own, moved: it has a function to take it
        [(closure? τ) (format "(drop-~a ~a)" (coil-type τ) (value Σ Γ e))]
        [else (format "(move ~a)" (value Σ Γ e))]))

;; e, whose type is a shared reference
(define (shared Σ Γ e)
  (match e
    [(? place?) (format "(borrow ~a)" (shared-place Σ Γ e))]
    [`(ref ,p) (format "(borrow ~a)" (shared-place Σ Γ p))]
    [_ (compound Σ Γ e)]))

;; e, whose type is an exclusive reference
(define (exclusive Σ Γ e)
  (match e
    [(? symbol?) (format "(borrow-mut (mut ~a))" (written-place Σ Γ e))]
    [(? place?) (bail "an exclusive reference read out of a view's field")]
    [`(mut ,p) (format "(borrow-mut (mut ~a))" (written-place Σ Γ p))]
    [_ (compound Σ Γ e)]))

;; e, whose type is storable
(define (plain Σ Γ e)
  (match e
    [(? integer? n) (if (negative? n) (format "(- 0 ~a)" (- n)) (number->string n))]
    ['unit "0"]
    [(? place? p)
     (if (behind-reference? Σ Γ p)
         (format "(primitive/load ~a)" (shared-place Σ Γ p))
         (shared-place Σ Γ p))]
    [_ (compound Σ Γ e)]))

(define (unit-after s) (format "(do ~a 0)" s))

(define (compound Σ Γ e)
  (match e
    ;; a closure that borrows is a lambda of its own type, held by a name of its
    ;; own; X is that lambda erased, so that it has the one type the model gives it
    [`(let ([,x ,(and e1 `(lam . ,_))]) ,e2)
     (define τ1 (type-of Σ Γ e1))
     (format "(let [(mut ~a--lambda) ~a (mut ~a) (~a-of (mut ~a--lambda))] ~a)"
             (var-name x) (parameterize ([lambda-bound #t]) (plain Σ Γ e1)) (var-name x) (coil-type τ1) (var-name x)
             (value Σ (cons (cons x τ1) Γ) e2))]
    [`(let ([,x ,e1]) ,e2)
     (define τ1 (type-of Σ Γ e1))
     (format "(let [~a ~a] ~a)"
             (if (ref? τ1) (var-name x) (format "(mut ~a)" (var-name x)))
             (bound Σ Γ e1)
             (value Σ (cons (cons x τ1) Γ) e2))]
    [`(seq ,e1 ,e2) (format "(do ~a ~a)" (discarded Σ Γ e1) (value Σ Γ e2))]
    [`(if0 ,e1 ,e2 ,e3)
     (format "(if (= ~a 0) ~a ~a)" (plain Σ Γ e1) (value Σ Γ e2) (value Σ Γ e3))]
    [`(+ ,e1 ,e2) (format "(+ ~a ~a)" (plain Σ Γ e1) (plain Σ Γ e2))]
    [`(while ,ec ,eb)
     (unit-after (format "(while (!= ~a 0) ~a)" (plain Σ Γ ec) (discarded Σ Γ eb)))]
    [`(break) "(do (break) 0)"]
    [`(uninit ,σ) (format "(uninit [~a])" (coil-type σ))]
    [`(out ,p) (place-type Σ Γ p) (format "(mut ~a)" (written-place Σ Γ p))]
    [`(return ,e1 ,_)
     (format "(return-from :ret ~a)" (value Σ Γ e1))]
    [`(lam ([,xs ,τcs ,es] ...) ((,ps ,τps) ...) ,τr ,body)
     #:when (and (second-class? τr) (bail "a closure that returns a reference"))
     ""]
    [`(lamo ([,xs ,τcs ,es] ...) ((,ps ,τps) ...) ,τr ,body)
     #:when (and (second-class? τr) (bail "a closure that returns a reference"))
     ""]
    [`(lam ([,xs ,τcs ,es] ...) ((,ps ,τps) ...) ,τr ,body)
     (unless (lambda-bound) (bail "a closure that borrows, made where no name holds it"))
     (parameterize ([lambda-bound #f])
       (format "(lambda ~a [~a] ~a)" (closure-name τps τr)
               (string-join (for/list ([x xs] [τc τcs] [e1 es]) (capture Σ Γ x τc e1)))
               (closure-body Σ (append (map cons xs τcs) (map cons ps τps)) ps τps body)))]
    [`(lamo ([,xs ,τcs ,es] ...) ((,ps ,τps) ...) ,τr ,body)
     (format "(~a-own-of (lambda-own ~a [~a] ~a))" (closure-name τps τr) (closure-name τps τr)
             (string-join (for/list ([x xs] [e1 es]) (format "(~a ~a)" (var-name x) (plain Σ Γ e1))))
             (closure-body Σ (append (map cons xs τcs) (map cons ps τps)) ps τps body))]
    [`(apply ,p ,es ...)
     (define-values (name τas place)
       (match (place-type Σ Γ p)
         [`(fnb ,_ ,τas ,τr) (values (closure-name τas τr) τas (written-place Σ Γ p))]
         [`(fno ,τas ,τr) (values (closure-name τas τr) τas (written-place Σ Γ p))]
         [_ (bail "an ill-typed program")]))
     (format "(~a::run (mut ~a)~a)" name place
             (string-append* (for/list ([τa τas] [e1 es]) (format " ~a" (argument Σ Γ τa e1)))))]
    [`(spawn-fn ,e1)
     (match (type-of Σ Γ e1)
       [`(fno () ,σ) (format "(spawn (~a-call-once ~a))" (closure-name '() σ) (plain Σ Γ e1))]
       [_ (bail "an ill-typed program")])]
    [`(box ,e1) (format "(Box::new ~a)" (plain Σ Γ e1))]
    [`(unbox ,e1) (match (type-of Σ Γ e1)
                    [`(abox ,_) (format "(BoxIn::into ~a)" (plain Σ Γ e1))]
                    [_ (format "(Box::into ~a)" (plain Σ Γ e1))])]
    ['(arena-new) "(Arena::new)"]
    [`(destroy ,e1) (unit-after (format "(destroy ~a)" (plain Σ Γ e1)))]
    [`(abox ,p ,e1) (format "(BoxIn::in-arena [~a] ~a ~a)"
                            (coil-type (type-of Σ Γ e1)) (shared-place Σ Γ p) (plain Σ Γ e1))]
    [`(reset! ,p) (unit-after (format "(Arena::reset! (mut ~a))" (written-place Σ Γ p)))]
    [`(set! ,p ,e1)
     (unit-after
      (if (symbol? p)
          (format "(set! ~a ~a)" (var-name p) (plain Σ Γ e1))
          (match p
            [`(: ,_ ,_) (format "(set! ~a ~a)" (written-place Σ Γ p) (plain Σ Γ e1))]
            ;; an out parameter's place holds nothing yet: it is assigned, not lent
            [`(* ,(? symbol? x)) #:when (match (lookup Γ x) [`(out ,_) #t] [_ #f])
             (format "(set! ~a ~a)" (var-name x) (plain Σ Γ e1))]
            [_ (format "(set! (mut ~a) ~a)" (written-place Σ Γ p) (plain Σ Γ e1))])))]
    ;; the model computes the new value before it looks at the place
    [`(take ,p ,e1)
     (format "(let [(mut new-value) ~a] (replace! (mut ~a) new-value))" (plain Σ Γ e1) (written-place Σ Γ p))]
    [`(new (view ,V) ,es ...)
     (define fields (or (fields-of Σ `(view ,V)) (bail "an ill-typed program")))
     (unless (= (length fields) (length es)) (bail "an ill-typed program"))
     (format "(new-~a~a)" (view-name V)
             (string-append*
              (for/list ([f fields] [e1 es])
                (format " ~a" (cond [(mut? (cadr f)) (format "(mut ~a)" (exclusive Σ Γ e1))]
                                    [(ref? (cadr f)) (shared Σ Γ e1)]
                                    [else (plain Σ Γ e1)])))))]
    [`(new ,σ ,es ...)
     (define fields (or (fields-of Σ σ) (bail "an ill-typed program")))
     (unless (= (length fields) (length es)) (bail "an ill-typed program"))
     (format "(~a~a)" (constructor (type-name (car σ)) (cdr σ))
             (string-append* (for/list ([f fields] [e1 es]) (format " :~a ~a" (car f) (plain Σ Γ e1)))))]
    [`(inj ,σ ,K ,e1)
     ;; a payload of another type than the variant's: the rules refuse the program
     (unless (equal? (type-of Σ Γ e1) (variant-type Σ σ K))
       (bail "an ill-typed program"))
     (format "(~a ~a)" (constructor (variant-name K) (cdr σ)) (plain Σ Γ e1))]
    [`(match ,e1 ,arms ...)
     (define τ1 (type-of Σ Γ e1))
     (format "(match (move ~a)~a)" (plain Σ Γ e1)
             (string-append*
              (for/list ([arm arms])
                (match arm
                  [`((,K ,x) ,ea)
                   (define Γa (cons (cons x (variant-type Σ τ1 K)) Γ))
                   ;; the arm's name is rebound so that the arm can change it
                   (format " (~a [~a] (let [(mut ~a) ~a] ~a))" (variant-name K) (var-name x)
                           (var-name x) (var-name x) (value Σ Γa ea))]))))]
    [`(,(and form (or 'match-ref 'match-mut)) ,p ,arms ...)
     (define τp (place-type Σ Γ p))
     (define k (if (eq? form 'match-ref) 'ref 'mut))
     ;; Coil copies a plain-data payload into the arm. A shared reference to the
     ;; copy reads what a reference to the payload would, while the scrutinee
     ;; keeps the place lent; an exclusive one would change the copy only.
     (for ([v (or (variants-of Σ τp) (bail "an ill-typed program"))])
       (when (and (eq? k 'mut) (copy? Σ (cadr v)))
         (bail "a match by exclusive reference on a plain-data payload")))
     ;; a match on a name that can be written lends its payload exclusively; on a
     ;; shared reference to the same place, shared
     (define-values (before scrutinee after)
       (if (eq? k 'ref)
           (values (format "(let [scrutinee (borrow ~a)] " (shared-place Σ Γ p)) "scrutinee" ")")
           (values "" (written-place Σ Γ p) "")))
     (format "~a(match ~a~a)~a" before scrutinee
             (string-append*
              (for/list ([arm arms])
                (match arm
                  [`((,K ,x) ,ea)
                   (define Γa (cons (cons x `(,k ,(variant-type Σ τp K))) Γ))
                   (if (copy? Σ (variant-type Σ τp K))
                       (format " (~a [copied] (let [~a (borrow copied)] ~a))"
                               (variant-name K) (var-name x) (value Σ Γa ea))
                       (format " (~a [~a] ~a)" (variant-name K) (var-name x) (value Σ Γa ea)))])))
             after)]
    [`(pool-new ,σ) (format "(Pool::new [~a])" (coil-type σ))]
    [`(insert ,p ,e1)
     (format "(let [(mut new-value) ~a] (Pool::insert! (mut ~a) new-value))" (plain Σ Γ e1) (written-place Σ Γ p))]
    [`(remove ,p ,x) (format "(Pool::remove! (mut ~a) ~a)" (written-place Σ Γ p) (var-name x))]
    [`(call ,f ,σs ,es ...)
     (match (decl Σ 'defn f)
       [`(defn ,_ ,Ts ,params ,_ ,_)
        (unless (and (= (length Ts) (length σs)) (= (length params) (length es)))
          (bail "an ill-typed program"))
        (format "(~a~a~a)" (fn-name f)
                (if (null? σs) "" (format " [~a]" (string-join (map coil-type σs))))
                (string-append*
                 (for/list ([p params] [e1 es])
                   (define τp (subst (cadr p) Ts σs))
                   (format " ~a"
                           (cond [(mut? τp) (format "(mut ~a)" (exclusive Σ Γ e1))]
                                 [(ref? τp) (shared Σ Γ e1)]
                                 [else (plain Σ Γ e1)])))))])]
    ;; `par` reads how each argument is passed from how it is written
    [`(par ,c1 ,c2) (format "(par ~a ~a)" (par-call Σ Γ c1) (par-call Σ Γ c2))]
    ;; a thread's call is written as any call is; Coil refuses a reference argument
    [`(spawn ,c) (format "(spawn ~a)" (par-call Σ Γ c))]
    [`(join ,e1) (format "(Task::join ~a)" (plain Σ Γ e1))]
    [`(with ,w ,g ,x ,e1)
     (match (decl Σ 'global g)
       [`(global ,_ ,σ ,_)
        (format "(~a (g-~a) ~a ~a)" (if (eq? w 'ref) "with-ref" "with-mut") g (var-name x)
                (value Σ (cons (cons x `(,w ,σ)) Γ) e1))])]
    [`(unsafe ,e1) (format "(unsafe ~a)" (value Σ Γ e1))]
    [`(addr ,p) (format "(primitive/cast ~a (borrow ~a))" (coil-type (type-of Σ Γ e)) (shared-place Σ Γ p))]
    ;; `(load q)` on a name that can be assigned reads the name; the pointer is
    ;; followed when it arrives as a value
    [`(load ,e1) (format "(primitive/load (move ~a))" (plain Σ Γ e1))]
    [`(store ,e1 ,e2) (unit-after (format "(primitive/store! (move ~a) ~a)" (plain Σ Γ e1) (plain Σ Γ e2)))]
    [`(alloc ,e1)
     (format "(alloc/box! (alloc/malloc-allocator) ~a ~a)" (coil-type (type-of Σ Γ e1)) (plain Σ Γ e1))]
    [`(free ,e1) (unit-after (format "(alloc/destroy (alloc/malloc-allocator) ~a)" (plain Σ Γ e1)))]
    [_ (bail "an ill-typed program")]))

;; e passed for a parameter of type τ
(define (argument Σ Γ τ e)
  (cond [(match e [`(out ,_) #t] [_ #f]) (compound Σ Γ e)]
        [(mut? τ) (format "(mut ~a)" (exclusive Σ Γ e))]
        [(ref? τ) (shared Σ Γ e)]
        [else (plain Σ Γ e)]))

;; A borrowing closure's capture x of type τ, made by e: a borrow of a place, or
;; a variable that holds a reference, lent again.
(define (capture Σ Γ x τ e)
  (match* (τ e)
    [(`(ref ,_) `(ref ,p)) (format "(~a (ref ~a))" (var-name x) (shared-place Σ Γ p))]
    [(`(mut ,_) `(mut ,p)) (format "(~a (mut ~a))" (var-name x) (written-place Σ Γ p))]
    [(`(ref ,_) (? symbol? y)) #:when (ref? (lookup Γ y)) (format "(~a (ref ~a))" (var-name x) (var-name y))]
    [(`(mut ,_) (? symbol? y)) #:when (mut? (lookup Γ y)) (format "(~a (mut ~a))" (var-name x) (var-name y))]
    [(_ _) (bail "a closure capture that is not a borrow")]))

;; `[PARAM…] BODY` of a closure over Γb: parameters taken by value are rebound so
;; that the body can change them, and a `return` leaves the block `:ret`.
(define (closure-body Σ Γb ps τps body)
  (define rebound
    (string-append* (for/list ([p ps] [t τps] #:unless (or (ref? t) (closure? t)))
                      (format "(mut ~a) ~a " (var-name p) (var-name p)))))
  (format "[~a] ~a" (string-join (map var-name ps))
          (returning body (format "(let [~a] ~a)" rebound (value Σ Γb body)))))

(define (mentions-return? e)
  (match e
    [`(return . ,_) #t]
    [`(,(or 'lam 'lamo) . ,_) #f]
    [(? pair?) (ormap mentions-return? e)]
    [_ #f]))
(define (returning body text)
  (if (mentions-return? body) (format "(block :ret ~a)" text) text))

(define (par-call Σ Γ c)
  (match c
    [`(call ,f ,σs ,es ...)
     #:when (and (ormap (λ (e) (match e [`(out ,_) #t] [_ #f])) es)
                 (bail "an out parameter given to a call on another thread"))
     ""]
    [`(call ,f ,σs ,es ...)
     (match (decl Σ 'defn f)
       [`(defn ,_ ,Ts ,params ,_ ,_)
        (unless (and (= (length Ts) (length σs)) (= (length params) (length es)))
          (bail "an ill-typed program"))
        (format "(~a~a~a)" (fn-name f)
                (if (null? σs) "" (format " [~a]" (string-join (map coil-type σs))))
                (string-append*
                 (for/list ([p params] [e1 es])
                   (define τp (subst (cadr p) Ts σs))
                   (format " ~a"
                           (cond [(mut? τp) (format "(mut ~a)" (exclusive Σ Γ e1))]
                                 [(ref? τp)
                                  (let ([text (shared Σ Γ e1)])
                                    (if (string-prefix? text "(borrow ") text (format "(borrow ~a)" text)))]
                                 [else (plain Σ Γ e1)])))))])]))

(define (constructor name args)
  (if (null? args) name (format "~a [~a]" name (string-join (map coil-type args)))))

;; ---------------------------------------------------------------- declarations

(define (type-params Ts [droppable '()])
  (if (null? Ts)
      ""
      (format " [~a]" (string-join (for/list ([T Ts])
                                     (if (memq T droppable)
                                         (format "(~a Droppable)" T)
                                         (symbol->string T)))))))

(define (declaration ds d)
  (match d
    [`(struct ,S ,Ts ((,flds ,ts) ...))
     (format "(defstruct ~a~a [~a])" (type-name S) (type-params Ts)
             (string-join (for/list ([f flds] [t ts]) (format "(~a ~a)" f (coil-type t)))))]
    [`(sum ,S ,Ts ((,Ks ,ts) ...))
     (format "(defsum ~a~a ~a)" (type-name S) (type-params Ts)
             (string-join (for/list ([K Ks] [t ts]) (format "(~a [(payload ~a)])" (variant-name K) (coil-type t)))))]
    [`(view ,V ((,flds ,ts) ...) . ,drop)
     (define W (view-name V))
     (define moved? (moved-view? (make-Σ ds) `(view ,V)))
     (string-join
      (append
       (list (format "(defstruct ~a [~a])" W
                     (string-join (for/list ([f flds] [t ts])
                                    (format "(~a ~a)" f (if (ref? t) (format "(ptr ~a)" (coil-type (cadr t))) (coil-type t))))))
             (format "(impl View ~a)" W))
       ;; a view that gives exclusive access is moved, never copied
       ;; a drop of its own runs the function the model names, given the view
       (if moved?
           (list (match drop
                   [(list f) (format "(impl Drop ~a (drop [(self (mut ~a))] (-> void) (~a self) 0))" W W (fn-name f))]
                   [_ (format "(impl Drop ~a (drop [(self (mut ~a))] (-> void) 0))" W W)])
                 (format "(defn drop-~a [(v ~a)] (-> i64) 0)" W W))
           '())
       (list (format "(defn new-~a [~a] (-> ~a)\n  (unsafe (~a~a)))" W
                     (string-join (for/list ([f flds] [t ts]) (format "(~a ~a)" f (coil-type t))))
                     W W
                     (string-append*
                      (for/list ([f flds] [t ts])
                        (format " :~a ~a" f
                                (cond [(mut? t) (format "(primitive/cast (ptr ~a) (mut ~a))" (coil-type (cadr t)) f)]
                                      [(ref? t) (format "(primitive/cast (ptr ~a) ~a)" (coil-type (cadr t)) f)]
                                      [else f]))))))
       (for/list ([f flds] [t ts] #:when (ref? t))
         (format "(defn ~a-~a [(v (ref ~a))] (-> (ref ~a))\n  (unsafe (lend [~a] (.~a v))))"
                 W f W (coil-type (cadr t)) (coil-type (cadr t)) f))
       (for/list ([f flds] [t ts] #:when (mut? t))
         (format "(defn ~a-~a-mut [(v (mut ~a))] (-> (mut ~a))\n  (unsafe (lend-mut [~a] (.~a v))))"
                 W f W (coil-type (cadr t)) (coil-type (cadr t)) f)))
      "\n")]
    [`(global ,g ,σ ,e)
     (format "(defglobal g-~a ~a ~a)" g (coil-type σ) (plain (make-Σ ds) '() e))]
    ;; said on the function itself, as an annotation
    [`(borrows ,_ ,_) ""]
    ;; said as the bound of the type parameters
    [`(droppable ,_ ,_) ""]
    ;; Coil copies plain data, so a linear struct of plain data is given a drop,
    ;; which makes it an owner, moved as the model moves it
    [`(linear ,S)
     (define T (type-name S))
     (if (copy-shape? (make-Σ ds) `(,S))
         (format "(impl Linear ~a)\n(impl Drop ~a (drop [(self (mut ~a))] (-> void) 0))" T T T)
         (format "(impl Linear ~a)" T))]
    [`(defn ,f ,Ts ,params ,τr ,body)
     (define Σ (make-Σ ds Ts))
     ;; the function a view's drop runs is given the view as Coil's drop has it
     (define dropping (for/or ([d ds]) (match d [`(view ,V ,_ ,(== f)) V] [_ #f])))
     (define Γ (for/list ([p params]) (cons (car p) (cadr p))))
     ;; a parameter taken by value is rebound so that the body can change it
     (define rebound
       (string-append*
        (for/list ([p params] #:unless (or (ref? (cadr p)) (match (cadr p) [`(out ,_) #t] [_ #f])))
          (format "(mut ~a) ~a " (var-name (car p)) (var-name (car p))))))
     ;; what the result may borrow from, when the model says
     (define borrows
       (for/or ([d ds]) (match d [`(borrows ,(== f) ,xs) xs] [_ #f])))
     (format "(defn ~a~a~a [~a] (-> ~a)\n  ~a)"
             (fn-name f)
             (if borrows
                 (format " :safe/borrows ~s" (string-join (map var-name borrows)))
                 "")
             (type-params Ts (droppable-of ds f))
             (string-join (for/list ([p params])
                            (format "(~a ~a)" (var-name (car p))
                                    (if dropping (format "(ref ~a)" (view-name dropping)) (coil-type (cadr p))))))
             (coil-type τr)
             (returning body (format "(let [~a] ~a)" (if dropping "" rebound) (value Σ Γ body))))]))

;; The functions of DS that cannot be written, with why: one that uses what Coil
;; lacks, and then any that calls one of those.
(define (find-unwritten ds)
  (let loop ([found '()])
    (define more
      (for/fold ([found found]) ([d ds] #:when (and (eq? (car d) 'defn) (not (memq (cadr d) found))))
        (with-handlers ([untranslatable? (λ (u) (cons (cadr d) found))])
          (parameterize ([unwritten found]) (declaration ds d))
          found)))
    (if (equal? more found) found (loop more))))

;; A declaration nothing in the program uses may be left out: a view that is
;; only declared, a function that is never called.
(define (program->coil prog name)
  (with-handlers ([untranslatable? (λ (u) (values #f (untranslatable-why u)))])
    (match prog
      [`(program ,ds ,main)
       (define Σ (make-Σ ds))
       (parameterize ([current-decls ds] [closure-names (make-hash)])
         (parameterize ([unwritten (find-unwritten ds)])
           (type-of Σ '() main)
           (define decl-text
             (string-append*
              (for/list ([d ds] #:unless (and (eq? (car d) 'defn) (memq (cadr d) (unwritten))))
                (define text (declaration ds d))
                (if text (string-append text "\n") ""))))
           (define main-text (format "(defn main [] (-> i64)\n  (let [result ~a] 0))\n" (value Σ '() main)))
           (define closure-text
             (string-append*
              (for/list ([(sig n) (closure-names)])
                (format "(deffn ~a [~a] ~a)\n(defn drop-~a-view [(f ~a-view)] (-> i64) 0)\n" n
                        (string-join (map coil-type (car sig))) (coil-type (cadr sig)) n n))))
           (values
            (string-append
             (format "(module ~a)\n" name)
             "(import \"coil.primitive\" :as primitive)\n"
             "(import \"coil.alloc\" :as alloc)\n"
             "(import \"safe.core\" :use [unsafe replace! borrow borrow-mut move lend lend-mut View Linear Droppable destroy])\n"
             "(import \"safe.box\" :use [Box BoxIn])\n"
             "(import \"safe.alloc\" :use [Arena ArenaRef])\n"
             "(import \"safe.pool\" :use [Pool Handle])\n"
             "(import \"safe.global\" :use [defglobal with-ref with-mut Global])\n"
             "(import \"safe.par\" :use [par])\n"
             "(import \"safe.thread\" :use [spawn Task])\n"
             "(import \"safe.fn\" :use [deffn lambda lambda-own])\n"
             closure-text
             decl-text
             main-text)
            #f)))])))
