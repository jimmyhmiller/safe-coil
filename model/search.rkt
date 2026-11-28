#lang racket
;; The search for a counterexample to: a program the rules accept, with no
;; `unsafe` in it, never gets stuck and never leaks. (It may panic: a stale
;; handle and a global entered twice are checked when the program runs.)
;;
;; Programs are built by type, so most of them are well typed apart from the
;; rules under test: the generator pays no attention to moves, loans or scopes.
;; That is what makes an accepted program worth running.
;;
;;   racket search.rkt            the property, on 20000 programs
;;   racket search.rkt N SEED     N programs from SEED
;;   racket search.rkt teeth [N]  each rule weakened in turn: the search must
;;                                then find a program that goes wrong
;;   racket search.rkt teeth N NAME ...   only those weakenings
(require "rules.rkt" "machine.rkt" "cases.rkt" racket/pretty)
(provide search gen-program)

(define Σ0 (make-Σ prelude))
(define (fields τ) (fields-of Σ0 τ))
(define (variants τ) (variants-of Σ0 τ))
(define globals '((g1 . (box int)) (g2 . (Opt (box int)))))

;; Functions every generated program has, beside its random ones: the small
;; shapes that real code is made of, each one accepted by the rules. Random
;; bodies seldom come out as any of these, and calls to them are where the
;; rules about arguments and results are exercised.
(define stock
  '((defn get () ((r (ref int))) int (* r))
    (defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1)))
    (defn eat () ((b (box int))) int (* b))
    (defn renew () ((m (mut (box int)))) unit (set! (* m) (box 9)))
    (defn inner () ((r (ref (box int)))) (ref int) (ref (* (* r))))
    (defn inner-mut () ((r (mut (box int)))) (mut int) (mut (* (* r))))
    (defn either () ((x (ref int)) (y (ref int))) (ref int) (if0 (* x) x y))
    (defn grow () ((xs (mut (box int))) (x (ref int))) int (seq (set! (* xs) (box 2)) (* x)))
    (defn both () ((x (mut (box int))) (y (mut (box int)))) int
      (let ([r (ref (* (* y)))]) (seq (set! (* x) (box 2)) (* r))))
    (defn look () ((r (ref int))) (view Peek) (new (view Peek) r 1))
    (defn first () ((p (ref (Pair)))) (ref (box int)) (ref (: (* p) a)))
    (defn some () ((o (ref (Opt (box int)))) (d (ref (box int)))) (ref (box int))
      (match-ref (* o) ((None u) d) ((Some x) x)))
    (defn id (T) ((x T)) T x)
    (defn wrap (T) ((x T)) (Wrap T) (new (Wrap T) x 0))
    (defn call-it () ((f (fnb shr () int))) int (apply f))
    (defn call-twice () ((f (fnb mut () int))) int (+ (apply f) (apply f)))
    (defn run-own () ((f (fno () int))) int (+ (apply f) (apply f)))
    (defn fill () ((r (out (box int)))) unit (set! (* r) (box 4)))
    (defn swap-in () ((m (mut (Pair)))) int
      (let ([old (: (* m) a)]) (seq (set! (: (* m) a) (box 7)) (* old))))
    (defn lock () ((r (mut (box int)))) (view Lock) (new (view Lock) r))
    ;; a view lent where it lies
    (defn relock () ((k (mut (view Lock)))) unit (set! (* (: (* k) r)) (box 5)))
    (defn peek-at () ((v (ref (view Peek)))) int (+ (* (: (* v) s)) (: (* v) i)))
    ;; linear values: one made, one used up, one passed through a type
    ;; parameter that may be linear
    (defn open () () (Tx) (new (Tx) 3))
    (defn finish () ((t (Tx))) int (let ([n (: t n)]) (seq (destroy t) n)))
    (defn pass (T) ((x T)) T x)))
(define stock-sigs
  (for/list ([fn stock] #:when (eq? (car fn) 'defn))
    (match-define `(defn ,f ,Ts ((,_ ,τs) ...) ,τr ,_) fn)
    (list f Ts τs τr)))

(define tvars (make-parameter '()))
(define in-loop (make-parameter #f))
;; the result type of the function (or closure) being generated, for a return
(define fn-ret (make-parameter #f))

(define (pick xs) (list-ref xs (random (length xs))))
(define base-storables
  '(int int int int unit (box int) (box int) (box int) (box (box int))
    (Pair) (Pt) (Wrap (box int)) (Opt (box int)) (Opt (box int)) (Opt int)
    (pool (box int)) (handle (box int)) (ptr int) (ptr (box int)) arena (Tx)))
(define (gen-storable)
  (if (and (pair? (tvars)) (zero? (random 3)))
      (pick '(T T (box T) (Opt T) (Wrap T)))
      (pick base-storables)))
(define closure-types
  '((fnb shr () int) (fnb mut () int) (fnb shr () (ref int)) (fnb mut () (mut (box int)))
    (fnb shr ((ref int)) int) (fno () int) (fno ((ref int)) int)))
(define (gen-type)
  (case (random 14)
    [(0 1) `(ref ,(gen-storable))]
    [(2 3) `(mut ,(gen-storable))]
    [(4) (pick '((view Two) (view Peek) (view Lock) (view Nest) (view Watch) (view InArena) (view Node)))]
    [(5) (pick closure-types)]
    [else (gen-storable)]))

(define (storable? τ) (not (second-class? τ)))
;; owns nothing (the generator's own idea of it, whatever the rules are set to)
(define (plain? σ)
  (match σ
    [(or 'int 'unit) #t]
    [(? symbol?) #f]
    [`(,(or 'ptr 'handle) ,_) #t]
    [`(,(or 'box 'pool 'task) ,_) #f]
    [(list (or 'Tx 'Deal)) #f]
    [`(fno . ,_) #f]
    [_ (andmap (λ (part) (plain? (cadr part))) (or (fields σ) (variants σ) '()))]))

(define counter 0)
(define (fresh base) (set! counter (add1 counter)) (string->symbol (format "~a~a" base counter)))

;; every place reachable from the variables in scope, with its type
(define (places env)
  (append*
   (for/list ([b env])
     (let loop ([p (car b)] [τ (cdr b)])
       (cons (cons p τ)
             (match τ
               [`(,(or 'box 'ref 'mut 'abox) ,σ) (loop `(* ,p) σ)]
               [`(pool ,σ) (append* (for/list ([h env] #:when (equal? (cdr h) `(handle ,σ)))
                                      (loop `(at ,p ,(car h)) σ)))]
               [(? pair?) #:when (fields τ)
                (append* (for/list ([f (fields τ)]) (loop `(: ,p ,(car f)) (cadr f))))]
               [_ '()]))))))
(define (root p) (if (symbol? p) p (root (cadr p))))

;; a function that may be called: (f Ts τs τr). -> its type arguments when its
;; result can be τ, else #f
(define (instantiate sig τ)
  (match-define (list _ Ts _ τr) sig)
  (cond
    [(null? Ts) (and (equal? τr τ) '())]
    [else
     (define found
       (let loop ([pat τr] [t τ])
         (cond [(eq? pat 'T) t]
               [(and (pair? pat) (pair? t) (= (length pat) (length t)))
                (for/or ([a pat] [b t]) (loop a b))]
               [else #f])))
     (define targ (or found (pick base-storables)))
     (and (storable? targ) (equal? (subst τr Ts (list targ)) τ) (list targ))]))
(define (instantiate-any sig)
  (if (null? (cadr sig)) '() (list (pick base-storables))))

(define (gen-expr env sigs τ d)
  (define ps (places env))
  (define (of-type t) (for/list ([pt ps] #:when (equal? (cdr pt) t)) (car pt)))
  (define here (of-type τ))
  (define calls (filter (λ (s) (instantiate s τ)) sigs))
  (define (sub t [dd (sub1 d)]) (gen-expr env sigs t dd))
  (define (in-scope x τx t [dd (sub1 d)]) (gen-expr (cons (cons x τx) env) sigs t dd))

  (define (leaf-of t) (gen-expr env sigs t 0))
  (define (leaf)
    (match τ
      ['int (if (and (pair? here) (< (random 4) 3)) (pick here) (random 3))]
      ['unit 'unit]
      ['arena (if (and (pair? here) (zero? (random 2))) (pick here) '(arena-new))]
      [(? symbol?) (if (pair? here) (pick here) (error 'gen "no value of type ~a in scope" τ))]
      [`(box ,σ) (if (and (pair? here) (zero? (random 2))) (pick here) `(box ,(sub σ 0)))]
      [`(ptr ,σ)
       (define targets (of-type σ))
       (cond [(and (pair? here) (zero? (random 3))) (pick here)]
             [(and (pair? targets) (< (random 4) 3)) `(addr ,(pick targets))]
             [else (let ([y (fresh 'v)]) `(let ([,y ,(sub σ 0)]) (addr ,y)))])]
      [`(pool ,σ) (if (and (pair? here) (zero? (random 2))) (pick here) `(pool-new ,σ))]
      [`(abox ,σ)
       (define arenas (of-type 'arena))
       (cond [(and (pair? here) (zero? (random 3))) (pick here)]
             [(pair? arenas) `(abox ,(pick arenas) ,(sub σ 0))]
             [else (let ([y (fresh 'v)]) `(let ([,y (arena-new)]) (abox ,y ,(sub σ 0))))])]
      [`(handle ,σ)
       (define pools (of-type `(pool ,σ)))
       (cond [(and (pair? here) (< (random 3) 2)) (pick here)]
             [(pair? pools) `(insert ,(pick pools) ,(sub σ 0))]
             [else (let ([y (fresh 'v)]) `(let ([,y (pool-new ,σ)]) (insert ,y ,(sub σ 0))))])]
      [`(,(and k (or 'ref 'mut)) ,σ)
       (define targets (of-type σ))
       (cond [(and (pair? here) (zero? (random 3))) (pick here)]
             [(pair? targets) `(,k ,(pick targets))]
             [else (let ([y (fresh 'v)]) `(let ([,y ,(sub σ 0)]) (,k ,y)))])]
      [`(view ,_)
       (if (and (pair? here) (zero? (random 3)))
           (pick here)
           `(new ,τ ,@(for/list ([f (fields τ)]) (sub (cadr f) 0))))]
      [`(fnb ,k ,τs ,τr)
       (if (and (pair? here) (zero? (random 3))) (pick here) (gen-closure #f k τs τr))]
      [`(fno ,τs ,τr)
       (if (and (pair? here) (zero? (random 3))) (pick here) (gen-closure #t #f τs τr))]
      ;; a place lent to be filled: usually one that holds a value, which the
      ;; rules refuse; `gen-out` makes the ones that hold nothing
      [`(out ,σ) (let ([ts (of-type σ)]) (if (pair? ts) `(out ,(pick ts)) `(out ,(fresh 'nowhere))))]
      [_ (cond [(and (pair? here) (zero? (random 2))) (pick here)]
               [(fields τ) => (λ (fs) `(new ,τ ,@(for/list ([f fs]) (sub (cadr f) 0))))]
               [else (let ([v (pick (variants τ))]) `(inj ,τ ,(car v) ,(sub (cadr v) 0)))])]))

  ;; A closure over captures from what is in scope: borrows of places for one
  ;; that borrows, owners or copies for one that owns (and now and then a
  ;; borrow, which the rules must refuse). Its body reads through what it
  ;; captured.
  (define (gen-closure own? k τs τr)
    ;; a closure's body is generated with no type parameters in scope, so it
    ;; captures nothing whose type mentions one
    (define (mentions-tvar? t) (let loop ([t t]) (or (and (symbol? t) (memq t (tvars)) #t) (and (pair? t) (ormap loop t)))))
    (define ts (filter (λ (pt) (and (storable? (cdr pt)) (not (mentions-tvar? (cdr pt))))) ps))
    ;; usually each capture borrows from a variable no other capture does
    (define used-roots '())
    (define caps
      (for/list ([i (random 3)])
        (define y (fresh 'c))
        (cond
          [(and own? (or (null? ts) (< (random 5) 4)))
           (define t (pick '((box int) (box int) int (box (box int)) (Pair) (Opt (box int)))))
           (list y t (gen-expr env sigs t 0))]
          [(null? ts) (list y 'int (random 3))]
          [else
           (define apart (let ([a (filter (λ (pt) (not (memq (root (car pt)) used-roots))) ts)])
                           (if (and (pair? a) (< (random 4) 3)) a ts)))
           (match-define (cons p σ) (let ([inner (filter (λ (pt) (pair? (car pt))) apart)])
                                      (if (and (pair? inner) (zero? (random 2))) (pick inner) (pick apart))))
           (set! used-roots (cons (root p) used-roots))
           (define w (if (and (eq? k 'mut) (zero? i)) 'mut (pick '(ref ref mut))))
           (list y `(,w ,σ) `(,w ,p))])))
    ;; a borrowing closure's captures are second-class; plain ones are passed as borrows
    (define caps2
      (if own? caps
          (for/list ([c caps])
            (match c [(list y 'int v) (list y '(ref int) (let ([s (filter (λ (pt) (equal? (cdr pt) 'int)) ps)])
                                                             (if (pair? s) `(ref ,(car (pick s))) v)))]
                     [_ c]))))
    (define params (for/list ([t τs]) (cons (fresh 'a) t)))
    (define benv (append (for/list ([c caps2]) (cons (car c) (cadr c))) params))
    (define body
      (parameterize ([fn-ret τr] [in-loop #f] [tvars '()])
        (define main (gen-expr benv sigs τr (random 3)))
        (define mine (filter (λ (pt) (eq? (cdr pt) 'int)) (places benv)))
        (define moves (if (and own? (pair? caps2) (zero? (random 3)))
                          (let ([c (pick caps2)]) (if (plain? (cadr c)) '() (list `(seq ,(car c) unit))))
                          '()))
        (for/fold ([b main]) ([r (append moves (if (pair? mine) (list (car (pick mine))) '()))])
          `(seq ,r ,b))))
    `(,(if own? 'lamo 'lam) ,(for/list ([c caps2]) (list (car c) (cadr c) (caddr c)))
                            ,(for/list ([p params]) (list (car p) (cdr p)))
                            ,τr ,body))
  ;; A place with nothing in it (a new variable, or a part just moved away),
  ;; filled by a call through an out parameter, then read.
  (define (gen-out)
    (define fillers (filter (λ (s) (and (null? (cadr s)) (ormap (λ (t) (match t [`(out ,_) #t] [_ #f])) (caddr s)))) sigs))
    (define sig (pick fillers))
    (match-define (list f _ τs _) sig)
    (define at (index-where τs (λ (t) (match t [`(out ,_) #t] [_ #f]))))
    (define σ (cadr (list-ref τs at)))
    (define y (fresh 'v))
    (define (the-call target)
      `(call ,f () ,@(for/list ([t τs] [i (in-naturals)]) (if (= i at) `(out ,target) (sub t 0)))))
    (define reads (let ([ints (for/list ([pt (places (list (cons y σ)))] #:when (eq? (cdr pt) 'int)) (car pt))])
                    (if (pair? ints) (pick ints) 'unit)))
    (case (random 3)
      [(0) `(let ([,y (uninit ,σ)]) (seq ,(if (zero? (random 4)) 'unit (the-call y)) (seq ,reads ,(sub τ))))]
      [(1) `(let ([,y ,(sub σ 0)]) (seq (seq ,y unit) (seq ,(the-call y) (seq ,reads ,(sub τ)))))]
      [else
       ;; a part of a struct moved away and filled again
       (define w (fresh 'v))
       `(let ([,w (new (Pair) (box 1) (box 2))])
          (seq (seq (: ,w a) unit)
               (seq ,(if (equal? σ '(box int)) `(call ,f () ,@(for/list ([t τs] [i (in-naturals)]) (if (= i at) `(out (: ,w a)) (sub t 0)))) 'unit)
                    (seq (* (: ,w a)) ,(sub τ)))))]))

  ;; `(apply f args…)` with arguments from what is in scope ENV: a reference
  ;; argument borrows a place there, or one bound around the call
  (define (apply-with f τs env)
    (define outer '())
    (define args
      (for/list ([t τs])
        (match t
          [`(,(and k (or 'ref 'mut)) ,σ)
           (define ts (for/list ([pt (places env)] #:when (equal? (cdr pt) σ)) (car pt)))
           (cond [(and (pair? ts) (< (random 4) 3)) `(,k ,(pick ts))]
                 [else (define y (fresh 'v))
                       (set! outer (cons (list y (gen-expr env sigs σ 0)) outer))
                       `(,k ,y)])]
          [_ (gen-expr env sigs t 0)])))
    (for/fold ([e `(apply ,f ,@args)]) ([o outer]) `(let ([,(car o) ,(cadr o)]) ,e)))

  (define (bind)
    (define y (fresh 'v))
    (define τy (gen-type))
    `(let ([,y ,(sub τy)]) ,(in-scope y τy τ)))
  ;; arguments are mostly direct: a borrow, a variable, a literal
  (define (call-with sig targs [env env])
    (match-define (list f Ts τs _) sig)
    `(call ,f ,targs
           ,@(for/list ([t τs])
               (gen-expr env sigs (subst t Ts targs) (if (zero? (random 4)) (min 1 (sub1 d)) 0)))))
  (define (call) (let ([sig (pick calls)]) (call-with sig (instantiate sig τ))))
  (define (assign)
    (define targets (filter (λ (pt) (storable? (cdr pt))) ps))
    ;; a reference or view local given another: often to a place it does not
    ;; hold, which the rules must refuse
    (define refs (for/list ([b env] #:when (and (symbol? (car b)) (second-class? (cdr b)))) b))
    (cond [(and (pair? refs) (zero? (random 3)))
           (match-let ([(cons x τx) (pick refs)]) `(set! ,x ,(sub τx 0)))]
          [(null? targets) 'unit]
          [else (match-let ([(cons p σ) (pick targets)]) `(set! ,p ,(sub σ)))]))
  (define (construct)
    (match τ
      ['int `(+ ,(sub 'int) ,(sub 'int))]
      ['unit (assign)]
      [`(box ,σ) `(box ,(sub σ))]
      [(? pair?) #:when (and (storable? τ) (fields τ))
       `(new ,τ ,@(for/list ([f (fields τ)]) (sub (cadr f))))]
      [(? pair?) #:when (and (storable? τ) (variants τ))
       (let ([v (pick (variants τ))]) `(inj ,τ ,(car v) ,(sub (cadr v))))]
      [_ (if (pair? calls) (call) (leaf))]))
  (define (arms σ form)
    (for/list ([v (variants σ)])
      (define x (fresh 'v))
      (define τx (case form
                   [(match) (cadr v)]
                   [(match-ref) `(ref ,(cadr v))]
                   [else `(mut ,(cadr v))]))
      `((,(car v) ,x) ,(in-scope x τx τ))))
  (define (gen-match)
    (define sums (filter (λ (pt) (and (storable? (cdr pt)) (variants (cdr pt)))) ps))
    (cond [(and (pair? sums) (< (random 4) 3))
           (match-define (cons p σ) (pick sums))
           (define form (pick '(match-ref match-ref match-mut match)))
           `(,form ,p ,@(arms σ form))]
          [else (let ([σ (pick '((Opt (box int)) (Opt int)))])
                  `(match ,(sub σ) ,@(arms σ 'match)))]))
  ;; a counted loop: the body cannot see the counter, so it ends
  (define (gen-while)
    (define i (fresh 'i))
    `(let ([,i ,(add1 (random 3))])
       (while ,i (seq ,(parameterize ([in-loop #t]) (sub (gen-type)))
                      (set! ,i (+ ,i -1))))))
  (define (gen-with)
    (match-define (cons g σ) (pick globals))
    (define x (fresh 'v))
    (define w (pick '(ref mut)))
    `(with ,w ,g ,x ,(in-scope x `(,w ,σ) τ)))
  (define (gen-par)
    (define ok (filter (λ (s) (storable? (cadddr s))) sigs))
    (define (one) (let ([sig (pick ok)]) (call-with sig (instantiate-any sig))))
    ;; both sides given a borrow of one place: the shape a data race has
    (define (aimed)
      (define (first-ref sig)
        (match (caddr sig) [(cons `(,(or 'ref 'mut) ,σ) _) (and (null? (cadr sig)) σ)] [_ #f]))
      (define takers (filter first-ref ok))
      (define sig1 (and (pair? takers) (pick takers)))
      (define σ (and sig1 (first-ref sig1)))
      (define sig2 (and σ (pick (filter (λ (s) (equal? (first-ref s) σ)) takers))))
      (define targets (if σ (of-type σ) '()))
      (cond [(pair? targets)
             (define p (pick targets))
             (define (side sig)
               (match-define (list f _ (cons `(,k ,_) τs) _) sig)
               `(call ,f () (,k ,p) ,@(for/list ([t τs]) (sub t 0))))
             `(par ,(side sig1) ,(side sig2))]
            [else `(par ,(one) ,(one))]))
    (cond [(null? ok) 'unit]
          [(zero? (random 2)) (aimed)]
          [else `(par ,(one) ,(one))]))
  ;; a call on its own thread, something done while it runs, and sometimes a join
  (define (gen-spawn)
    (define ok (filter (λ (s) (storable? (cadddr s))) sigs))
    (define y (fresh 'v))
    (define (after) (if (zero? (random 2)) `(seq (join ,y) ,(sub τ)) (sub τ)))
    ;; the thread given a borrow of a place this one then writes
    (define (aimed)
      (define (first-ref sig)
        (match (caddr sig) [(cons `(,(or 'ref 'mut) ,σ) _) (and (null? (cadr sig)) σ)] [_ #f]))
      (define takers (filter first-ref ok))
      (define sig (and (pair? takers) (pick takers)))
      (define σ (and sig (first-ref sig)))
      (define targets (if σ (of-type σ) '()))
      (cond [(pair? targets)
             (define p (pick targets))
             (match-define (list f _ (cons `(,k ,_) τs) _) sig)
             `(let ([,y (spawn (call ,f () (,k ,p) ,@(for/list ([t τs]) (sub t 0))))])
                (seq (set! ,p ,(sub σ 0)) ,(after)))]
            [else #f]))
    (define (plain)
      (define sig (pick ok))
      `(let ([,y (spawn ,(call-with sig (instantiate-any sig)))])
         (seq ,(sub (gen-type)) ,(after))))
    (cond [(null? ok) (sub τ)]
          [(zero? (random 3)) (or (aimed) (plain))]
          [else (plain)]))
  ;; a call made for what it does; when it is given a place to change, what is
  ;; there is read afterwards
  (define (call-for-effect)
    (define changers
      (for*/list ([s sigs] #:when (null? (cadr s))
                  [t (caddr s)] #:when (match t [`(mut ,_) #t] [_ #f])
                  [pt ps] #:when (equal? (cdr pt) (cadr t)))
        (list s t (car pt))))
    (cond
      [(null? sigs) 'unit]
      [(and (pair? changers) (zero? (random 2)))
       (match-define (list sig t p) (pick changers))
       (match-define (list f _ τs _) sig)
       (define at (index-of τs t))
       (define inside (for/list ([pt (places env)] #:when (and (eq? (root (car pt)) (root p)) (eq? (cdr pt) 'int)))
                        (car pt)))
       `(seq (call ,f () ,@(for/list ([u τs] [i (in-naturals)]) (if (= i at) `(mut ,p) (sub u 0))))
             ,(if (pair? inside) (pick inside) 'unit))]
      [else (let ([sig (pick sigs)]) (call-with sig (instantiate-any sig)))]))
  ;; An owner is used up somewhere (straight away, in one branch, in a match
  ;; arm, in a loop) and then used again: the shape every move error has.
  (define (move-hazard)
    (define existing (for/list ([b env] #:when (and (storable? (cdr b)) (not (plain? (cdr b))))) b))
    (define fresh-one
      (let ([t (pick '((box int) (box int) (box (box int)) (Pair) (Opt (box int)) (pool (box int))))])
        (cons (fresh 'v) t)))
    (define own (if (and (pair? existing) (zero? (random 2))) (pick existing) fresh-one))
    (define x (car own))
    ;; what is used up: the variable, or a part of it (a field, what a box
    ;; holds), or what an exclusive parameter in scope refers to
    (define parts
      (for/list ([pt (append (places (list own))
                             (append* (for/list ([b env] #:when (match (cdr b) [`(mut ,_) #t] [_ #f]))
                                        (cdr (places (list b))))))]
                 #:when (and (storable? (cdr pt)) (not (plain? (cdr pt)))
                             (not (match (car pt) [`(at . ,_) #t] [_ #f]))))
        pt))
    (match-define (cons tp tτ) (if (and (pair? parts) (zero? (random 2))) (pick parts) own))
    (define (use-up)
      (define takers (filter (λ (s) (and (null? (cadr s)) (member tτ (caddr s)))) sigs))
      (cond [(and (pair? takers) (zero? (random 2)))
             (match-define (list f _ τs _) (pick takers))
             (define at (index-of τs tτ))
             `(seq (call ,f () ,@(for/list ([t τs] [i (in-naturals)]) (if (= i at) tp (sub t 0)))) unit)]
            [(zero? (random 2)) (let ([y (fresh 'v)]) `(let ([,y ,tp]) unit))]
            [else `(seq ,tp unit)]))
    (define used
      (case (random 10)
        [(0) (use-up)]
        [(1) `(if0 ,(random 2) ,(use-up) unit)]
        [(2 3) `(if0 ,(random 2) unit ,(use-up))]
        [(4) `(match (inj (Opt int) ,(pick '(None Some)) ,(pick '(unit 1)))
                ((None ,(fresh 'v)) unit) ((Some ,(fresh 'v)) ,(use-up)))]
        [(5 6) (let ([i (fresh 'i)])
                 `(let ([,i 2]) (while ,i (seq ,(use-up) (set! ,i (+ ,i -1))))))]
        ;; used up, and the loop left at once
        [(7 8) (let ([i (fresh 'i)])
                 `(let ([,i 2]) (while ,i (seq ,(if (zero? (random 3)) `(if0 ,(random 2) (break) unit) 'unit)
                                               (seq ,(use-up) ,(if (zero? (random 4)) `(set! ,i (+ ,i -1)) '(break)))))))]
        [else `(seq ,(use-up) ,(use-up))]))
    (define mine (filter (λ (pt) (eq? (root (car pt)) (root tp))) (places (cons own env))))
    (define ints (for/list ([pt mine] #:when (eq? (cdr pt) 'int)) (car pt)))
    (define inside (for/list ([pt mine] #:when (and (pair? (car pt)) (storable? (cdr pt))
                                                    (not (equal? (car pt) tp))
                                                    (let loop ([q (car pt)]) (and (pair? q) (or (equal? (cadr q) tp) (loop (cadr q)))))))
                     pt))
    (define again (case (random 7)
                    [(0) 'unit]
                    [(1 2) (if (pair? ints) (pick ints) tp)]
                    ;; given a value again, then used
                    [(3) `(seq (set! ,tp ,(sub tτ 0)) ,(if (pair? ints) (pick ints) tp))]
                    ;; a part of what was moved away is assigned
                    [(4) (if (pair? inside)
                             (match-let ([(cons q σ) (pick inside)]) `(set! ,q ,(sub σ 0)))
                             tp)]
                    [else tp]))
    (define restore (if (and (not (eq? (root tp) x)) (< (random 4) 3)) `(set! ,tp ,(sub tτ 0)) 'unit))
    (define body `(seq ,used (seq ,again (seq ,restore ,(sub τ)))))
    (if (eq? own fresh-one) `(let ([,x ,(sub (cdr own) 0)]) ,body) body))
  ;; A linear value is made and then used up: destroyed, taken apart, given
  ;; away, on every way or only some, or else dropped, overwritten, thrown
  ;; away, boxed and dropped, or given to a type parameter that may drop it.
  (define (linear-hazard)
    (define x (fresh 'v))
    (define deal? (zero? (random 3)))
    (define t (if deal? '(Deal) '(Tx)))
    (define made (cond [deal? `(new (Deal) (box ,(random 3)) (box ,(random 3)))]
                       [(zero? (random 3)) '(call open ())]
                       [(zero? (random 4)) `(call pass ((Tx)) (new (Tx) ,(random 3)))]
                       [else `(new (Tx) ,(random 3))]))
    (define (consume)
      (case (random (if deal? 3 5))
        [(0) `(destroy ,x)]
        [(1) (if deal?
                 (let ([a (fresh 'v)] [b (fresh 'v)])
                   `(let ([,a (: ,x amt)]) (let ([,b (: ,x fee)]) (+ (* ,a) (* ,b)))))
                 `(seq (call finish () ,x) unit))]
        [(2) (let ([y (fresh 'v)]) `(let ([,y ,x]) (destroy ,y)))]
        [(3) `(seq (call finish () (call pass ((Tx)) ,x)) unit)]
        [else `(seq (call ,(pick '(id finish)) ,@(if (zero? (random 2)) '(((Tx))) '(())) ,x) unit)]))
    (define body
      (case (random 14)
        [(0 1 2 3) `(seq ,(consume) ,(sub τ))]
        [(4) `(seq (if0 ,(random 2) ,(consume) ,(consume)) ,(sub τ))]
        [(5) `(seq (if0 ,(random 2) ,(consume) unit) ,(sub τ))]
        [(6) (let ([i (fresh 'i)])
               `(let ([,i 2]) (while ,i (seq ,(consume) (seq (break) (set! ,i 0))))))]
        [(7) `(seq (set! ,x ,(leaf-of t)) (seq ,(consume) ,(sub τ)))]
        [(8) `(seq ,x ,(sub τ))]
        [(9) (let ([b (fresh 'v)]) `(let ([,b (box ,x)]) ,(sub τ)))]
        [(10) (let ([b (fresh 'v)] [y (fresh 'v)])
                `(let ([,b (box ,x)]) (let ([,y (unbox ,b)]) (seq (destroy ,y) ,(sub τ)))))]
        [(11) `(seq (match (inj (Opt int) ,(pick '(None Some)) ,(pick '(unit 1)))
                      ((None ,(fresh 'v)) ,(consume)) ((Some ,(fresh 'v)) ,(consume)))
                    ,(sub τ))]
        [(12) (if deal?
                  (let ([a (fresh 'v)]) `(let ([,a (: ,x amt)]) (seq (* ,a) ,(sub τ))))
                  `(seq (call id ((Tx)) ,x) ,(sub τ)))]
        [else (sub τ)]))
    `(let ([,x ,made]) ,body))
  (define (maybe-unsafe e) (if (zero? (random 2)) `(unsafe ,e) e))
  (define (gen-raw)
    (if (and (storable? τ) (zero? (random 2)))
        (maybe-unsafe `(load ,(sub `(ptr ,τ) 0)))
        `(seq ,(maybe-unsafe `(store ,(sub '(ptr int) 0) ,(sub 'int 0))) ,(sub τ))))
  (define (gen-pool)
    (define pools (filter (λ (pt) (match (cdr pt) [`(pool ,_) #t] [_ #f])) ps))
    (cond
      [(null? pools) (bind)]
      [else
       (match-define (cons p `(pool ,σ)) (pick pools))
       (define hs (for/list ([b env] #:when (equal? (cdr b) `(handle ,σ))) (car b)))
       (cond [(and (pair? hs) (equal? σ τ) (zero? (random 2))) `(remove ,p ,(pick hs))]
             [(and (pair? hs) (zero? (random 2))) `(seq (remove ,p ,(pick hs)) ,(sub τ))]
             [else (let ([h (fresh 'v)])
                     `(let ([,h (insert ,p ,(sub σ 0))]) ,(in-scope h `(handle ,σ) τ)))])]))
  (define (gen-take)
    (cond [(not (storable? τ)) (leaf)]
          [(and (pair? here) (zero? (random 2))) `(take ,(pick here) ,(sub τ 0))]
          [else `(unbox ,(sub `(box ,τ)))]))

  ;; Get one to three references (a borrow, a copy of one, a call's result,
  ;; either arm of a conditional, a view, a match arm's reference, a global's),
  ;; do something to what they came from, then read through them: the shape
  ;; every aliasing error has.
  (define (hazard)
    (define near '())
    (define entered '())
    (define (note! . things) (set! near (append (filter symbol? (flatten things)) near)))
    (define (storable-places env)
      (filter (λ (pt) (storable? (cdr pt))) (places env)))
    (define (ref-type-for env)
      (define ts (storable-places env))
      (and (pair? ts) `(,(pick '(ref ref mut)) ,(cdr (pick ts)))))
    ;; a borrow of a place inside something is the one that can be left dangling
    (define (inner-borrow env τr)
      (define inner (for/list ([pt (places env)]
                               #:when (and (pair? (car pt)) (equal? (cdr pt) (cadr τr))))
                      (car pt)))
      (if (pair? inner) `(,(car τr) ,(pick inner)) (gen-expr env sigs τr 0)))
    (define (ref-source env held)
      (define ref-calls (filter (λ (s) (second-class? (cadddr s))) sigs))
      (define τr (ref-type-for env))
      (define sums (filter (λ (pt) (variants (cdr pt))) (storable-places env)))
      (define (borrowed) (and τr `(let ,τr ,(inner-borrow env τr))))
      (define (inside-of y τy)
        (for/list ([pt (places (list (cons y τy)))] #:when (and (pair? (car pt)) (storable? (cdr pt)))) pt))
      (define arenas (for/list ([pt (storable-places env)] #:when (eq? (cdr pt) 'arena)) (car pt)))
      (case (cond [(and (pair? entered) (zero? (random 2))) 15]
                  [(and (pair? sums) (zero? (random 3))) 5]
                  [(and (pair? held) (zero? (random 4))) 22]
                  [(and (pair? arenas) (zero? (random 2))) 24]
                  [else (random 22)])
        ;; a borrow of something whose scope has already ended
        [(13)
         (define y (fresh 'v))
         (define τy (pick '((box int) (box (box int)) (Pair) (view Peek) (view Peek) (view Two) (Opt (box int)))))
         (define inner (inside-of y τy))
         (define at (and (pair? inner) (pick inner)))
         (if at
             `(let (ref ,(cdr at)) (let ([,y ,(gen-expr env sigs τy 0)]) (ref ,(car at))))
             (borrowed))]
        ;; a borrow of a global that leaves its `with`
        [(14)
         (match-define (cons g σ) (pick globals))
         (define x (fresh 'v))
         (define at (pick (inside-of x `(ref ,σ))))
         `(let (ref ,(cdr at)) (with ref ,g ,x (ref ,(car at))))]
        ;; a second reference made from one already held
        [(15 16)
         (define inner (append* (for/list ([h held]) (inside-of (car h) (cdr h)))))
         (if (pair? inner)
             (let ([at (pick inner)]) `(let (ref ,(cdr at)) (ref ,(car at))))
             (borrowed))]
        [(0 1)
         (cond [(pair? ref-calls)
                ;; the program's own functions as often as the stock ones
                (define own (filter (λ (s) (not (memq s stock-sigs))) ref-calls))
                (define sig (if (and (pair? own) (zero? (random 2))) (pick own) (pick ref-calls)))
                (define targs (instantiate-any sig))
                `(let ,(subst (cadddr sig) (cadr sig) targs)
                   ,(call-with sig targs env))]
               [else (borrowed)])]
        [(2) (if (pair? held) (let ([h (pick held)]) `(let ,(cdr h) ,(car h))) (borrowed))]
        ;; what a closure already held gives back, held in turn
        [(22 23)
         (define giving (for/list ([h held] #:when (match (cdr h) [`(fnb ,_ ,_ ,τr) (second-class? τr)] [_ #f])) h))
         (if (pair? giving)
             (match-let ([(cons f `(fnb ,_ ,τs ,τr)) (pick giving)]) `(let ,τr ,(apply-with f τs env)))
             (borrowed))]
        [(3 17)
         (and τr
              (let* ([one (inner-borrow env τr)]
                     [other (or (for/or ([try 4]) (let ([b (inner-borrow env τr)]) (and (not (equal? b one)) b)))
                                one)])
                `(let ,τr (if0 ,(random 2) ,one ,other))))]
        [(4)
         (define V (pick '((view Peek) (view Two))))
         `(let ,V (new ,V ,@(for/list ([f (fields V)])
                              (if (second-class? (cadr f))
                                  (inner-borrow env (cadr f))
                                  (gen-expr env sigs (cadr f) 0)))))]
        [(5 6)
         (cond [(pair? sums)
                (match-define (cons p σ) (pick sums))
                (define form (pick '(match-ref match-ref match-mut)))
                (define k (if (eq? form 'match-ref) 'ref 'mut))
                (define full (filter (λ (v) (not (eq? (cadr v) 'unit))) (variants σ)))
                (define chosen (if (and (pair? full) (< (random 4) 3)) (pick full) (pick (variants σ))))
                (define x (fresh 'v))
                (note! p)
                `(scoped (,k ,(cadr chosen)) ,x
                         ,(λ (body)
                            `(,form ,p
                                    ,@(for/list ([v (variants σ)])
                                        (if (eq? (car v) (car chosen))
                                            `((,(car v) ,x) ,body)
                                            `((,(car v) ,(fresh 'v)) ,(gen-expr env sigs τ 0)))))))]
               [else (borrowed)])]
        [(7)
         (match-define (cons g σ) (pick globals))
         (define w (pick '(ref ref mut)))
         (define x (fresh 'v))
         `(scoped (,w ,σ) ,x ,(λ (body) `(with ,w ,g ,x ,body)))]
        [(8) (and τr `(let ,τr ,(gen-expr env sigs τr (min (sub1 d) (random 2)))))]
        ;; a closure over borrows of what is in scope
        [(18 19)
         (define t (pick (filter (λ (t) (eq? (car t) 'fnb)) closure-types)))
         `(let ,t ,(gen-expr env sigs t 0))]
        ;; a lock: dropped at the end of its scope, and its drop reads what it holds
        [(20)
         ;; usually one inside something else, which can be freed under it
         (define boxes (for/list ([pt (storable-places env)] #:when (equal? (cdr pt) '(box int))) (car pt)))
         (define inner (filter pair? boxes))
         (cond [(and (pair? inner) (zero? (random 2))) `(let (view Watch) (new (view Watch) (ref ,(pick inner))))]
               [(and (pair? inner) (< (random 4) 3)) `(let (view Lock) (new (view Lock) (mut ,(pick inner))))]
               [(pair? boxes) `(let (view Lock) (new (view Lock) (mut ,(pick boxes))))]
               [else (borrowed)])]
;; a box in an arena: it keeps the arena lent until its scope ends
        [(24)
         (define ints (for/list ([pt (storable-places env)] #:when (eq? (cdr pt) 'int)) (car pt)))
         (case (random 3)
           ;; now and then an owner, which an arena refuses
           [(0) (if (zero? (random 4))
                    `(let (abox (box int)) (abox ,(pick arenas) (box ,(random 3))))
                    `(let (abox (Pt)) (abox ,(pick arenas) (new (Pt) ,(random 3) ,(random 3)))))]
           ;; a view in the arena: the box holds what the view borrowed too
           [(1) (if (pair? ints)
                    `(let (abox (view Peek)) (abox ,(pick arenas) (new (view Peek) (ref ,(pick ints)) ,(random 3))))
                    `(let (abox int) (abox ,(pick arenas) ,(random 3))))]
           [else `(let (abox int) (abox ,(pick arenas) ,(random 3)))])]
        ;; a closure that owns what it captured, made in a scope that then ends
        [(21)
         (define y (fresh 'v))
         (define c (fresh 'c))
         `(let (fno () int)
            (let ([,y (box ,(random 3))])
              (lamo ([,c (ref (box int)) (ref ,y)]) () int ,(if (zero? (random 2)) 1 `(* (* ,c))))))]
        [else (borrowed)]))
    (define (reads-through y env)
      (define τy (cdr (assq y env)))
      (match τy
        [`(,(or 'fnb 'fno) . ,_) (apply-through y τy env)]
        [_ (reads-through-place y env)]))
    ;; call a closure held, with arguments from what is in scope, and read
    ;; through what it gives back
    (define (apply-through y τy env)
      (define τs (match τy [`(fnb ,_ ,τs ,_) τs] [`(fno ,τs ,_) τs]))
      (define τr (match τy [`(fnb ,_ ,_ ,τr) τr] [`(fno ,_ ,τr) τr]))
      (define call (apply-with y τs env))
      (define z (fresh 'v))
      (match τr
        [`(,(or 'ref 'mut) int) `(let ([,z ,call]) (* ,z))]
        [`(ref (box int)) `(let ([,z ,call]) (* (* ,z)))]
        ;; given an exclusive reference, write through it
        [`(mut (box int)) (if (zero? (random 2))
                              `(let ([,z ,call]) (* (* ,z)))
                              `(let ([,z ,call]) (set! (* ,z) (box ,(random 3)))))]
        [_ call]))
    (define (reads-through-place y env)
      (define mine (filter (λ (pt) (eq? (root (car pt)) y)) (places env)))
      (define ints (for/list ([pt mine] #:when (eq? (cdr pt) 'int)) (car pt)))
      (define sums (for/list ([pt mine] #:when (and (storable? (cdr pt)) (variants (cdr pt)))) pt))
      (cond [(pair? ints) (pick ints)]
            [(pair? sums)
             (match-define (cons p σ) (pick sums))
             `(match-ref ,p ,@(for/list ([v (variants σ)]) `((,(car v) ,(fresh 'v)) 0)))]
            [else 'unit]))
    ;; usually aimed at something the references were made from, or at one of them
    (define (disturb env)
      (define aimed? (and (pair? near) (< (random 4) 3)))
      (define (aimed pts) (if aimed? (filter (λ (pt) (memq (root (car pt)) near)) pts) pts))
      (define ts (aimed (storable-places env)))
      ;; replacing an owner frees the old one, and so does moving its owner away
      (define owning (filter (λ (pt) (not (plain? (cdr pt)))) ts))
      (define owners (for/list ([b env]
                                #:when (and (not (memq (cdr b) '(int unit)))
                                            (or (not aimed?) (memq (car b) near))))
                       (car b)))
      ;; a sum is often replaced by its empty variant, which is what strands a
      ;; reference to the payload it had
      (define (new-value σ)
        (define empty (filter (λ (v) (eq? (cadr v) 'unit)) (or (variants σ) '())))
        (if (and (pair? empty) (zero? (random 2)))
            `(inj ,σ ,(car (pick empty)) unit)
            (gen-expr env sigs σ 0)))
      (define (deep pts)
        (define inner (filter (λ (pt) (pair? (car pt))) pts))
        (if (and (pair? inner) (zero? (random 2))) (pick inner) (pick pts)))
      (case (if (and (pair? entered) (zero? (random 2))) 8 (random 12))
        [(0 1 2) (if (pair? owning)
                     (match-let ([(cons p σ) (deep owning)]) `(set! ,p ,(new-value σ)))
                     'unit)]
        [(3) (if (pair? owners) (pick owners) 'unit)]
        [(4) (if (pair? ts)
                 (match-let ([(cons p σ) (pick ts)]) `(set! ,p ,(gen-expr env sigs σ (min 1 (sub1 d)))))
                 'unit)]
        [(5) (if (pair? owning)
                 (match-let ([(cons p σ) (deep owning)]) `(take ,p ,(new-value σ)))
                 'unit)]
        [(6 7)
         (define pools (filter (λ (pt) (match (cdr pt) [`(pool ,_) #t] [_ #f])) ts))
         (cond [(pair? pools)
                (match-define (cons p `(pool ,σ)) (pick pools))
                (define hs (for/list ([b env] #:when (equal? (cdr b) `(handle ,σ))) (car b)))
                (if (pair? hs) `(remove ,p ,(pick hs)) `(set! ,p (pool-new ,σ)))]
               [else 'unit])]
        [(8 9)
         (match-define (cons g σ) (if (pair? entered) (assq (pick entered) globals) (pick globals)))
         (define y (fresh 'v))
         `(with mut ,g ,y (set! (* ,y) ,(new-value σ)))]
        [(10) (gen-expr env sigs (gen-type) (min 1 (sub1 d)))]
        ;; an arena gives back everything in it
        [(11)
         (define arenas (for/list ([pt ts] #:when (eq? (cdr pt) 'arena)) (car pt)))
         (if (pair? arenas) `(reset! ,(pick arenas)) 'unit)]
        [else 'unit]))
    ;; the hazard brings some owners of its own, so there is something to free
    (define owned
      (append*
       (for/list ([i (random 3)])
         (cond [(zero? (random 3)) (list (list (fresh 'v) 'arena '(arena-new)))]
               [(zero? (random 4))
                (define pl (fresh 'v))
                (list (list pl '(pool (box int)) '(pool-new (box int)))
                      (list (fresh 'v) '(handle (box int)) `(insert ,pl (box ,(random 3)))))]
               [else
                (define t (if (zero? (random 2)) '(box int) (pick '((box (box int)) (Pair) (Opt (box int)) (Opt (box int))))))
                (list (list (fresh 'v) t (if (variants t) `(inj ,t Some (box ,(random 3))) (gen-expr env sigs t 0))))]))))
    ;; sometimes the references already in scope (a function's parameters) are the ones held
    (define held0
      (if (zero? (random 3))
          (for/list ([b env] #:when (second-class? (cdr b))) b)
          '()))
    (set! near (map car held0))
    (define env0 (append (for/list ([o (reverse owned)]) (cons (car o) (cadr o))) env))
    (define body
      (let loop ([n (if (pair? held0) (random 2) (add1 (random 3)))] [env env0] [held held0])
        (match (and (> n 0) (ref-source env held))
          [`(let ,τr ,e)
           (define y (fresh 'v))
           (note! e y)
           `(let ([,y ,e]) ,(loop (sub1 n) (cons (cons y τr) env) (cons (cons y τr) held)))]
          [`(scoped ,τx ,x ,build)
           (note! x)
           (match (build 'unit) [`(with ,_ ,g . ,_) (set! entered (cons g entered))] [_ (void)])
           (build (loop (sub1 n) (cons (cons x τx) env) (cons (cons x τx) held)))]
          [_
           ;; Half the time only some of the references are read afterwards,
           ;; the newest among them: a loan lasts while its holder is named, so
           ;; one that is not named again is where that rule can go wrong.
           (define readers
             (cond [(or (null? held) (zero? (random 2))) held]
                   [else (cons (car held) (filter (λ (_) (zero? (random 2))) (cdr held)))]))
           (if (null? held)
               (gen-expr env sigs τ (sub1 d))
               `(seq ,(disturb env)
                     ,(for/fold ([tail (gen-expr env sigs τ (sub1 d))]) ([h readers])
                        `(seq ,(reads-through (car h) env) ,tail))))])))
    (for/fold ([body body]) ([o (reverse owned)])
      `(let ([,(car o) ,(caddr o)]) ,body)))

  (cond
    [(<= d 0) (leaf)]
    [else
     (case (if (and (pair? (tvars)) (zero? (random 3))) 26 (random 34))
       [(32 33) (linear-hazard)]
       [(0 1 2 3) (hazard)]
       [(26 27 28) (move-hazard)]
       [(29 30) `(seq ,(call-for-effect) ,(sub τ))]
       [(4 5 6) (bind)]
       [(7 8) (if (pair? calls) (call) (bind))]
       [(9) `(seq ,(sub (gen-type)) ,(sub τ))]
       [(10 11) `(seq ,(assign) ,(sub τ))]
       [(12) `(if0 ,(sub 'int) ,(sub τ) ,(sub τ))]
       [(13) (construct)]
       [(14) (gen-match)]
       [(15) `(seq ,(gen-while) ,(sub τ))]
       [(16) (gen-with)]
       [(17) `(seq ,(gen-par) ,(sub τ))]
       [(18) (gen-raw)]
       [(19) (gen-pool)]
       [(20) (gen-take)]
       [(21) (if (in-loop) `(seq (break) ,(sub τ 0)) (leaf))]
       [(22) (gen-spawn)]
       [(23) (match (fn-ret)
               [#f (leaf)]
               ;; a reference returned early: often to a local of this function
               [`(,(and k (or 'ref 'mut)) ,σ)
                #:when (zero? (random 2))
                (define y (fresh 'v))
                `(let ([,y ,(sub σ 0)])
                   (seq (if0 ,(sub 'int 0) (return (,k ,y) ,'unit) unit) ,(in-scope y σ τ)))]
               [r `(seq (if0 ,(sub 'int 0) (return ,(sub r) unit) unit) ,(sub τ))])]
       [(24) (gen-out)]
       ;; a closure, called once or twice, then the rest
       [(25) (let* ([f (fresh 'v)] [t (pick closure-types)]
                    [τs (match t [`(fnb ,_ ,τs ,_) τs] [`(fno ,τs ,_) τs])]
                    [env2 (cons (cons f t) env)]
                    [call (λ () `(seq ,(apply-with f τs env2) unit))])
               `(let ([,f ,(leaf-of t)])
                  (seq ,(call) ,(if (zero? (random 2)) `(seq ,(call) ,(in-scope f t τ)) (in-scope f t τ)))))]
       [else (leaf)])]))

(define (gen-program)
  (set! counter 0)
  (define sigs
    (for/list ([i (random 4)])
      (define Ts (if (zero? (random 3)) '(T) '()))
      (parameterize ([tvars Ts])
        ;; a generic function has a value of its parameter type to work with;
        ;; half the others take a reference first, so that many can return one
        (define params
          (for/list ([j (add1 (random 3))])
            (cons (fresh 'p)
                  (cond [(and (zero? j) (pair? Ts)) 'T]
                        [(zero? (random 12)) '(out (box int))]
                        [(and (<= j 1) (zero? (random 2)))
                         `(,(pick '(ref mut)) ,(pick '((box int) (box int) (box (box int)) int (Pair) (Opt (box int)) (pool (box int)))))]
                        [else (gen-type)]))))
        ;; a reference result usually has a parameter it could come from
        (define refs (filter (λ (p) (match (cdr p) [`(,(or 'ref 'mut) ,_) #t] [_ #f])) params))
        (define ret (if (and (pair? refs) (zero? (random 2)))
                        ;; of what the parameter refers to, or of something inside it
                        (match (cdr (pick refs))
                          [`(,k ,σ)
                           (define inner (match σ [`(box ,σ2) (if (zero? (random 2)) σ2 σ)] [_ σ]))
                           `(,(if (zero? (random 3)) 'ref k) ,inner)])
                        (gen-type)))
        ;; with two or more references, the result may say which it comes from
        (define borrows
          (and (>= (length refs) 2) (second-class? ret) (zero? (random 2))
               (let ([some (filter (λ (_) (zero? (random 2))) refs)])
                 (map car (if (null? some) (list (pick refs)) some)))))
        (list (fresh 'f) Ts params ret borrows))))
  ;; A function calls only earlier ones, so every program terminates. A body the
  ;; rules refuse is tried again a few times and then left out: one bad function
  ;; would otherwise refuse the whole program, and few calls would ever run.
  (define-values (fns call-sigs)
    (for/fold ([fns stock] [call-sigs stock-sigs]) ([s sigs])
      (match-define (list f Ts params ret borrows) s)
      (define bdecl (append (if borrows (list `(borrows ,f ,borrows)) '())
                            (if (and (pair? Ts) (zero? (random 2))) (list `(droppable ,f ,Ts)) '())))
      (define fn
        (for/or ([try 5])
          (define fn `(defn ,f ,Ts ,(for/list ([p params]) (list (car p) (cdr p))) ,ret
                        ,(parameterize ([tvars Ts] [fn-ret ret])
                           (let ([outs (for/list ([p params] #:when (match (cdr p) [`(out ,_) #t] [_ #f])) (car p))])
                             ;; an out parameter is usually filled first
                             (for/fold ([b (gen-expr params call-sigs ret (random 3))]) ([o outs])
                               (if (zero? (random 4)) b `(seq (set! (* ,o) (box ,(random 3))) ,b)))))))
          (and (check-fn (append prelude fns bdecl (list fn)) fn) fn)))
      (if fn
          (values (append fns bdecl (list fn)) (append call-sigs (list (list f Ts (map cdr params) ret))))
          (values fns call-sigs))))
  `(program (,@prelude ,@fns)
            ,(gen-expr '() call-sigs (pick '(int int int unit (box int) (Opt (box int)))) (+ 1 (random 4)))))

(define (mentions? t heads)
  (let loop ([t t])
    (and (pair? t) (or (and (memq (car t) heads) #t) (ormap loop t)))))
(define (own-part prog)
  ;; a generated program has the prelude and the stock functions first; a
  ;; hand-written case only the prelude
  (define ds (cadr prog))
  (define k (+ (length prelude) (length stock)))
  (list-tail ds (if (>= (length ds) k) k (min (length ds) (length prelude)))))

(define features
  '(("references" ref mut) ("calls" call) ("fields" :) ("match" match match-ref match-mut)
    ("views" view) ("pools" insert remove at) ("take/unbox" take unbox) ("loops" while)
    ("break" break) ("borrows" borrows) ("arenas" abox) ("globals" with) ("par" par) ("threads" spawn spawn-fn) ("raw pointers" addr)
    ("closures" lam lamo) ("closure calls" apply) ("out" out) ("return" return)))

;; -> the first counterexample, or #f
(define (search n seed #:quiet [quiet #f])
  (random-seed seed)
  (define accepted 0)
  (define unsafe 0)
  (define outcomes (make-hasheq))
  (define seen (make-hash))
  (define found
    (for/or ([i n])
      (define prog (gen-program))
      (and (check-program prog)
           (let ([mine (list (own-part prog) (caddr prog))])
             (set! accepted (add1 accepted))
             (for ([f features]) (when (mentions? mine (cdr f)) (hash-update! seen (car f) add1 0)))
             (cond
               [(mentions? mine '(unsafe)) (set! unsafe (add1 unsafe)) #f]
               [else
                (define ran (run prog))
                (hash-update! outcomes (car ran) add1 0)
                (match ran
                  [(list 'ok _ 0) #f]
                  [(list (or 'timeout 'panic) _ ...) #f]
                  [_ (list prog ran)])])))))
  (unless quiet
    (printf "programs: ~a, accepted: ~a, of which set aside for using unsafe: ~a\n" n accepted unsafe)
    (printf "ran to the end: ~a, stopped by a run-time check: ~a, timed out: ~a\n"
            (hash-ref outcomes 'ok 0) (hash-ref outcomes 'panic 0) (hash-ref outcomes 'timeout 0))
    (printf "accepted programs using:~a\n"
            (string-append* (for/list ([f features]) (format " ~a ~a," (car f) (hash-ref seen (car f) 0))))))
  found)

(define (report found)
  (cond [found (printf "COUNTEREXAMPLE, the machine says ~a:\n" (cadr found))
               (pretty-write `(program ,(own-part (car found)) ,(caddr (car found))))]
        [else (printf "no counterexample\n")]))

;; The programs a seed gives depend on the rules, since a function body the
;; rules refuse is generated again. So a weakening one seed's programs happen
;; not to exercise is looked for in the next seed's.
(define (search-seeds n)
  (for/or ([seed '(1 2 3 4)]) (search n seed #:quiet #t)))

;; The hand-written cases under the rules as they are now: the first one the
;; rules should refuse but take, and that goes wrong when it runs.
(define (case-counterexample)
  (for/or ([c cases])
    (match-define (list want _ prog) c)
    (and (eq? want 'reject)
         (check-program prog)
         (let ([ran (run prog)])
           (match ran
             [(list 'stuck _) (list prog ran)]
             [_ #f])))))

(define (teeth n only)
  (define (try what thunk)
    (define found (thunk))
    (printf "if ~a: ~a\n" what
            (if found (format "found, the machine says ~a" (cadr found)) "NOTHING FOUND"))
    (when found (pretty-write `(program ,(own-part (car found)) ,(caddr (car found)))))
    (flush-output)
    (and found #t))
  (define results
    (append
     (for/list ([m mutants] #:when (or (null? only) (memq (car m) only)))
       (try (cadr m) (λ () (parameterize ([mutant (car m)]) (or (case-counterexample) (search-seeds n))))))
     (if (or (null? only) (memq 'no-global-check only))
         (list (try "a global is entered without the run-time check"
                    (λ () (parameterize ([check-globals? #f]) (search-seeds n)))))
         '())))
  (andmap values results))

(module+ main
  (match (current-command-line-arguments)
    [(vector "teeth") (exit (if (teeth 20000 '()) 0 1))]
    [(vector "teeth" n only ...) (exit (if (teeth (string->number n) (map string->symbol only)) 0 1))]
    [(vector) (let ([f (search 20000 1)]) (report f) (exit (if f 1 0)))]
    [(vector n seed) (let ([f (search (string->number n) (string->number seed))]) (report f) (exit (if f 1 0)))]))
