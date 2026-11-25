#lang racket
;; A model program as Coil source, for checking the Coil checker against the
;; model: `safe.check` must accept what `check-program` accepts and refuse what
;; it refuses.
;;
;; (program->coil prog module-name) -> a string, or #f with a reason when Coil
;; has nothing the program could be written with:
;;   - a view: Coil does not let a struct hold a reference;
;;   - `match-ref` and `match-mut` on a sum with a plain-data payload: Coil
;;     copies such a payload into the arm and lends only the parts that own
;;     something.

(require "rules.rkt")
(provide program->coil)

(struct untranslatable (why))
(define (bail why) (raise (untranslatable why)))

(define (fn-name f) (format "f-~a" f))
(define (var-name x) (format "v-~a" x))
(define (type-name S) (format "M~a" S))
(define (variant-name K) (format "K~a" K))

;; ---------------------------------------------------------------- types

(define (coil-type τ)
  (match τ
    ['int "i64"]
    ['unit "i64"]
    [`(box ,σ) (format "(Box ~a)" (coil-type σ))]
    [`(ptr ,σ) (format "(ptr ~a)" (coil-type σ))]
    [`(pool ,σ) (format "(Pool ~a)" (coil-type σ))]
    [`(handle ,σ) (format "(Handle ~a)" (coil-type σ))]
    [`(task ,σ) (format "(Task ~a)" (coil-type σ))]
    [`(ref ,σ) (format "(ref ~a)" (coil-type σ))]
    [`(mut ,σ) (format "(mut ~a)" (coil-type σ))]
    [`(view ,_) (bail "a view")]
    [(? symbol? T) (symbol->string T)]
    [(list S) (type-name S)]
    [(cons S args) (format "(~a ~a)" (type-name S) (string-join (map coil-type args)))]))

(define (ref? τ) (match τ [`(,(or 'ref 'mut) ,_) #t] [_ #f]))
(define (mut? τ) (match τ [`(mut ,_) #t] [_ #f]))

;; ---------------------------------------------------------------- the model's types, without its loans

(define (lookup Γ x) (cond [(assq x Γ) => cdr] [else (bail "an unbound variable")]))

(define (place-type Σ Γ p)
  (match p
    [(? symbol? x) (lookup Γ x)]
    [`(* ,q) (match (place-type Σ Γ q)
               [`(,(or 'box 'ref 'mut) ,σ) σ]
               [_ (bail "an ill-typed program")])]
    [`(: ,q ,fld) (match (assq fld (or (fields-of Σ (place-type Σ Γ q)) '()))
                    [(list _ t) t]
                    [_ (bail "an ill-typed program")])]
    [`(at ,q ,_) (match (place-type Σ Γ q)
                   [`(pool ,σ) σ]
                   [_ (bail "an ill-typed program")])]))

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
    [`(box ,e1) `(box ,(type-of Σ Γ e1))]
    [`(unbox ,e1) (match (type-of Σ Γ e1) [`(box ,σ) σ] [_ (bail "an ill-typed program")])]
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
               [_ (shared-place Σ Γ q)])]
    [`(: ,q ,fld) (format "(.~a ~a)" fld (shared-place Σ Γ q))]
    [`(at ,q ,x) (format "(Pool::at ~a ~a)" (shared-place Σ Γ q) (var-name x))]))

;; the place, as an expression `(mut …)` and `(set! …)` take
(define (written-place Σ Γ p)
  (match p
    [(? symbol? x) (var-name x)]
    [`(* ,q) (match (place-type Σ Γ q)
               [`(box ,_) (format "(Box::get-mut (mut ~a))" (written-place Σ Γ q))]
               [_ (written-place Σ Γ q)])]
    [`(: ,q ,fld) (format "(.~a ~a)" fld (written-place Σ Γ q))]
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
  (if (and (ends-in-place? e) (not (ref? (type-of Σ Γ e))))
      (format "(move ~a)" (value Σ Γ e))
      (value Σ Γ e)))

;; e, whose type is a shared reference
(define (shared Σ Γ e)
  (match e
    [(? place?) (format "(borrow ~a)" (shared-place Σ Γ e))]
    [`(ref ,p) (format "(borrow ~a)" (shared-place Σ Γ p))]
    [_ (compound Σ Γ e)]))

;; e, whose type is an exclusive reference
(define (exclusive Σ Γ e)
  (match e
    [(? place?) (format "(borrow-mut (mut ~a))" (written-place Σ Γ e))]
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
    [`(box ,e1) (format "(Box::new ~a)" (plain Σ Γ e1))]
    [`(unbox ,e1) (format "(Box::into ~a)" (plain Σ Γ e1))]
    [`(set! ,p ,e1)
     (unit-after
      (if (symbol? p)
          (format "(set! ~a ~a)" (var-name p) (plain Σ Γ e1))
          (match p
            [`(: ,_ ,_) (format "(set! ~a ~a)" (written-place Σ Γ p) (plain Σ Γ e1))]
            [_ (format "(set! (mut ~a) ~a)" (written-place Σ Γ p) (plain Σ Γ e1))])))]
    ;; the model computes the new value before it looks at the place
    [`(take ,p ,e1)
     (format "(let [(mut new-value) ~a] (replace! (mut ~a) new-value))" (plain Σ Γ e1) (written-place Σ Γ p))]
    [`(new (view ,_) ,_ ...) (bail "a view")]
    [`(new ,σ ,es ...)
     (define fields (or (fields-of Σ σ) (bail "an ill-typed program")))
     (unless (= (length fields) (length es)) (bail "an ill-typed program"))
     (format "(~a~a)" (constructor (type-name (car σ)) (cdr σ))
             (string-append* (for/list ([f fields] [e1 es]) (format " :~a ~a" (car f) (plain Σ Γ e1)))))]
    [`(inj ,σ ,K ,e1)
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
     (for ([v (or (variants-of Σ τp) (bail "an ill-typed program"))])
       (when (copy? Σ (cadr v))
         (bail "a match by reference on a plain-data payload")))
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
                   (format " (~a [~a] ~a)" (variant-name K) (var-name x) (value Σ Γa ea))])))
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

(define (par-call Σ Γ c)
  (match c
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

(define (type-params Ts)
  (if (null? Ts) "" (format " [~a]" (string-join (map symbol->string Ts)))))

(define (declaration ds d)
  (match d
    [`(struct ,S ,Ts ((,flds ,ts) ...))
     (format "(defstruct ~a~a [~a])" (type-name S) (type-params Ts)
             (string-join (for/list ([f flds] [t ts]) (format "(~a ~a)" f (coil-type t)))))]
    [`(sum ,S ,Ts ((,Ks ,ts) ...))
     (format "(defsum ~a~a ~a)" (type-name S) (type-params Ts)
             (string-join (for/list ([K Ks] [t ts]) (format "(~a [(payload ~a)])" (variant-name K) (coil-type t)))))]
    [`(view ,_ ,_) #f]
    [`(global ,g ,σ ,e)
     (format "(defglobal g-~a ~a ~a)" g (coil-type σ) (plain (make-Σ ds) '() e))]
    [`(defn ,f ,Ts ,params ,τr ,body)
     (define Σ (make-Σ ds Ts))
     (define Γ (for/list ([p params]) (cons (car p) (cadr p))))
     ;; a parameter taken by value is rebound so that the body can change it
     (define rebound
       (string-append*
        (for/list ([p params] #:unless (ref? (cadr p)))
          (format "(mut ~a) ~a " (var-name (car p)) (var-name (car p))))))
     (format "(defn ~a~a [~a] (-> ~a)\n  (let [~a] ~a))"
             (fn-name f) (type-params Ts)
             (string-join (for/list ([p params]) (format "(~a ~a)" (var-name (car p)) (coil-type (cadr p)))))
             (coil-type τr) rebound (value Σ Γ body))]))

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
       (parameterize ([current-decls ds])
         (parameterize ([unwritten (find-unwritten ds)])
           (type-of Σ '() main)
           (values
            (string-append
             (format "(module ~a)\n" name)
             "(import \"coil.primitive\" :as primitive)\n"
             "(import \"coil.alloc\" :as alloc)\n"
             "(import \"safe.core\" :use [unsafe replace! borrow borrow-mut move])\n"
             "(import \"safe.box\" :use [Box])\n"
             "(import \"safe.pool\" :use [Pool Handle])\n"
             "(import \"safe.global\" :use [defglobal with-ref with-mut Global])\n"
             "(import \"safe.par\" :use [par])\n"
             "(import \"safe.thread\" :use [spawn Task])\n"
             (string-append*
              (for/list ([d ds] #:unless (and (eq? (car d) 'defn) (memq (cadr d) (unwritten))))
                (define text (declaration ds d))
                (if text (string-append text "\n") "")))
             (format "(defn main [] (-> i64)\n  (let [result ~a] 0))\n" (value Σ '() main)))
            #f)))])))
