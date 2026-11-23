#lang racket
;; The search for a counterexample to: a program the rules accept never gets
;; stuck and never leaks.
;;
;; Programs are built by type, so most of them are well typed apart from the
;; rules under test: the generator pays no attention to moves, loans or scopes.
;; That is what makes an accepted program worth running.
;;
;;   racket search.rkt            the property, on 20000 programs
;;   racket search.rkt N SEED     N programs from SEED
;;   racket search.rkt teeth      each rule switched off in turn: the search
;;                                must then find a program that goes wrong
(require "rules.rkt" "machine.rkt" racket/pretty)
(provide search gen-program)

(define storables '(int int int unit (box int) (box int) (box (box int))))
(define (pick xs) (list-ref xs (random (length xs))))
(define (gen-storable) (pick storables))
(define (gen-type)
  (case (random 6)
    [(0) `(ref ,(gen-storable))]
    [(1) `(mut ,(gen-storable))]
    [else (gen-storable)]))

(define counter 0)
(define (fresh base) (set! counter (add1 counter)) (string->symbol (format "~a~a" base counter)))

;; every place reachable from the variables in scope, with its type
(define (places env)
  (append*
   (for/list ([b env])
     (let loop ([p (car b)] [τ (cdr b)])
       (cons (cons p τ)
             (match τ
               [`(,(or 'box 'ref 'mut) ,σ) (loop `(* ,p) σ)]
               [_ '()]))))))
(define (places-of env τ) (for/list ([pt (places env)] #:when (equal? (cdr pt) τ)) (car pt)))
(define (storable? τ) (not (and (pair? τ) (memq (car τ) '(ref mut)))))

;; sigs: (f (τ ...) τ) for each function that may be called
(define (gen-expr env sigs τ d)
  (define here (places-of env τ))
  (define calls (for/list ([s sigs] #:when (equal? (caddr s) τ)) s))
  (define (leaf)
    (match τ
      ['int (if (and (pair? here) (< (random 4) 3)) (pick here) (random 3))]
      ['unit 'unit]
      [`(box ,σ) (if (and (pair? here) (zero? (random 2))) (pick here) `(box ,(gen-expr env sigs σ 0)))]
      [`(,(and k (or 'ref 'mut)) ,σ)
       (define targets (places-of env σ))
       (cond [(and (pair? here) (zero? (random 3))) (pick here)]
             [(pair? targets) `(,k ,(pick targets))]
             [else (let ([y (fresh 'v)]) `(let ([,y ,(gen-expr env sigs σ 0)]) (,k ,y)))])]))
  (define (bind)
    (define y (fresh 'v))
    (define τy (gen-type))
    `(let ([,y ,(gen-expr env sigs τy (sub1 d))])
       ,(gen-expr (cons (cons y τy) env) sigs τ (sub1 d))))
  ;; arguments are mostly direct: a borrow, a variable, a literal
  (define (call-of sig)
    (match-define (list f τs _) sig)
    `(call ,f ,@(for/list ([t τs]) (gen-expr env sigs t (if (zero? (random 4)) (min 1 (sub1 d)) 0)))))
  (define (call) (call-of (pick calls)))
  (define (assign)
    (define targets (filter (λ (pt) (storable? (cdr pt))) (places env)))
    (if (null? targets)
        'unit
        (match-let ([(cons p σ) (pick targets)]) `(set! ,p ,(gen-expr env sigs σ (sub1 d))))))
  ;; Get a reference (a borrow, a copy of one, a call's result, either arm of a
  ;; conditional), perhaps derive a second from it, do something to what they
  ;; came from, then read through them: the shape every aliasing error has.
  (define (hazard)
    (define (ref-type-for env)
      (define ts (filter (λ (pt) (storable? (cdr pt))) (places env)))
      (and (pair? ts) `(,(pick '(ref ref mut)) ,(cdr (pick ts)))))
    ;; a borrow of a place inside a box is the one that can be left dangling
    (define (inner-borrow env τr)
      (define ps (for/list ([pt (places env)] #:when (and (pair? (car pt)) (equal? (cdr pt) (cadr τr)))) (car pt)))
      (if (pair? ps) `(,(car τr) ,(pick ps)) (gen-expr env sigs τr 0)))
    (define (reads-through y τy)
      ;; every place reached through y, read (a box is only looked into)
      (define leaves (for/list ([pt (places (list (cons y τy)))] #:when (memq (cdr pt) '(int unit))) (car pt)))
      (if (null? leaves) 'unit (pick leaves)))
    ;; usually aimed at a variable the references were made from, or at one of them
    (define (disturb env0 near)
      (define env (if (and (pair? near) (< (random 4) 3))
                      (filter (λ (b) (memq (car b) near)) env0)
                      env0))
      (define owners (for/list ([b env] #:when (not (memq (cdr b) '(int unit)))) (car b)))
      (define ts (filter (λ (pt) (storable? (cdr pt))) (places env)))
      ;; replacing a box frees the old one, and so does moving its owner away
      (define boxes (filter (λ (pt) (and (pair? (cdr pt)) (eq? (cadr pt) 'box))) (places env)))
      (case (random 7)
        [(5 6) (if (pair? boxes)
                   ;; more often a box reached through something than a variable
                   (match-let ([(cons p σ) (let ([deep (filter (λ (pt) (pair? (car pt))) boxes)])
                                             (if (and (pair? deep) (zero? (random 2))) (pick deep) (pick boxes)))]) `(set! ,p ,(gen-expr env0 sigs σ 0)))
                   'unit)]
        [(0) (if (pair? owners) (pick owners) 'unit)]
        [(1 2) (if (pair? ts)
                   (match-let ([(cons p σ) (pick ts)]) `(set! ,p ,(gen-expr env0 sigs σ (min 1 (sub1 d)))))
                   'unit)]
        [(3) (gen-expr env0 sigs (gen-type) (min 1 (sub1 d)))]
        [else 'unit]))
    ;; One to three references, each from: a call's result, either arm of a
    ;; conditional, or any expression of its type (a borrow, a copy of an
    ;; earlier one). Then the disturbance, then a read through each.
    (define ref-calls (for/list ([s sigs] #:when (not (storable? (caddr s)))) s))
    (define (one-ref env held)
      (define from-call (and (pair? ref-calls) (zero? (random 3)) (pick ref-calls)))
      (define τr (if from-call (caddr from-call) (ref-type-for env)))
      (and τr
           (cons τr
                 (cond [from-call (call-of from-call)]
                       ;; a copy of a reference already held
                       [(and (pair? held) (zero? (random 3))) #f]
                       [(zero? (random 4))
                        `(if0 ,(random 2) ,(inner-borrow env τr) ,(inner-borrow env τr))]
                       [(zero? (random 2)) (inner-borrow env τr)]
                       [else (gen-expr env sigs τr (min (sub1 d) (random 2)))]))))
    (define near '())
    ;; the hazard brings one or two boxes of its own, so there is something to free
    (define own (for/list ([i (random 3)]) (cons (fresh 'v) (pick '((box int) (box int) (box (box int)))))))
    (define (with-own body)
      (for/fold ([body body]) ([b own]) `(let ([,(car b) ,(gen-expr env sigs (cdr b) 0)]) ,body)))
    (with-own
     (let loop ([n (add1 (random 3))] [env (append own env)] [held '()])
      (define r0 (and (> n 0) (one-ref env held)))
      (define r (and r0 (if (cdr r0) r0 (let ([h (pick held)]) (cons (cdr h) (car h))))))
      (cond
        [r (define y (fresh 'v))
           (set! near (append (filter symbol? (flatten (cdr r))) (list y) near))
           `(let ([,y ,(cdr r)]) ,(loop (sub1 n) (cons (cons y (car r)) env) (cons (cons y (car r)) held)))]
        [(null? held) (bind)]
        [else
         (let ([reads (for/fold ([tail (gen-expr env sigs τ (sub1 d))]) ([h held])
                        `(seq ,(reads-through (car h) (cdr h)) ,tail))])
           `(seq ,(disturb env near) ,reads))]))))
  (cond
    [(<= d 0) (leaf)]
    [else
     (case (random 14)
       [(12 13) (hazard)]
       [(0 1 2) (bind)]
       [(3 4) (if (pair? calls) (call) (bind))]
       [(5) `(seq ,(gen-expr env sigs (gen-type) (sub1 d)) ,(gen-expr env sigs τ (sub1 d)))]
       [(6 7) `(seq ,(assign) ,(gen-expr env sigs τ (sub1 d)))]
       [(8) `(if0 ,(gen-expr env sigs 'int (sub1 d))
                  ,(gen-expr env sigs τ (sub1 d))
                  ,(gen-expr env sigs τ (sub1 d)))]
       [(9) (match τ
              ['int `(+ ,(gen-expr env sigs 'int (sub1 d)) ,(gen-expr env sigs 'int (sub1 d)))]
              ['unit (assign)]
              [`(box ,σ) `(box ,(gen-expr env sigs σ (sub1 d)))]
              [_ (if (pair? calls) (call) (leaf))])]
       [else (leaf)])]))

(define (gen-program)
  (set! counter 0)
  (define sigs
    (for/list ([i (random 4)])
      ;; half the functions take a reference first, so that many can return one
      (define params
        (for/list ([j (add1 (random 3))])
          (cons (fresh 'p)
                (if (and (zero? j) (zero? (random 2)))
                    `(,(pick '(ref mut)) ,(pick '((box int) (box int) (box (box int)) int)))
                    (gen-type)))))
      ;; a reference result usually has a parameter it could come from
      (define refs (filter (λ (p) (not (storable? (cdr p)))) params))
      (define ret (if (and (pair? refs) (zero? (random 2)))
                      ;; of what the parameter refers to, or of something inside it
                      (match (cdr (pick refs))
                        [`(,k ,σ)
                         (define inner (match σ [`(box ,σ2) (if (zero? (random 2)) σ2 σ)] [_ σ]))
                         `(,(if (zero? (random 3)) 'ref k) ,inner)])
                      (gen-type)))
      (list (fresh 'f) params ret)))
  ;; A function calls only earlier ones, so every program terminates. A body the
  ;; rules refuse is tried again a few times and then left out: one bad function
  ;; would otherwise refuse the whole program, and few calls would ever run.
  (define-values (fns call-sigs)
    (for/fold ([fns '()] [call-sigs '()]) ([s sigs])
      (match-define (list f params ret) s)
      (define fn
        (for/or ([try 6])
          (define fn `(defn ,f ,(for/list ([p params]) (list (car p) (cdr p))) ,ret
                        ,(gen-expr params call-sigs ret (random 3))))
          (and (check-fn (append fns (list fn)) fn) fn)))
      (if fn
          (values (append fns (list fn)) (append call-sigs (list (list f (map cdr params) ret))))
          (values fns call-sigs))))
  `(program ,fns ,(gen-expr '() call-sigs (pick '(int int unit (box int))) (+ 1 (random 4)))))

(define (mentions? prog heads)
  (let loop ([t prog])
    (and (pair? t) (or (and (memq (car t) heads) #t) (ormap loop t)))))

;; -> the first counterexample, or #f
(define (search n seed #:quiet [quiet #f])
  (random-seed seed)
  (define accepted 0)
  (define with-refs 0)
  (define with-ref-calls 0)
  (define timeouts 0)
  (define found
    (for/or ([i n])
      (define prog (gen-program))
      (and (check-program prog)
           (let ([ran (run prog)])
             (set! accepted (add1 accepted))
             (when (mentions? prog '(ref mut)) (set! with-refs (add1 with-refs)))
             (when (and (mentions? prog '(call)) (mentions? prog '(ref mut)))
               (set! with-ref-calls (add1 with-ref-calls)))
             (match ran
               [(list 'ok _ 0) #f]
               [(list 'timeout) (set! timeouts (add1 timeouts)) #f]
               [_ (list prog ran)])))))
  (unless quiet
    (printf "programs: ~a, accepted: ~a (using references: ~a; references and calls: ~a), timed out: ~a\n"
            n accepted with-refs with-ref-calls timeouts))
  found)

(define (report found)
  (cond [found (printf "COUNTEREXAMPLE, the machine says ~a:\n" (cadr found))
               (pretty-write (car found))]
        [else (printf "no counterexample\n")]))

(module+ main
  (match (current-command-line-arguments)
    [(vector "teeth")
     (define ok
       (for/and ([sw (list (cons "exclusivity" enforce-exclusive?)
                           (cons "escape" enforce-escape?)
                           (cons "moves" enforce-moves?))])
         (define found (parameterize ([(cdr sw) #f]) (search 20000 1 #:quiet #t)))
         (printf "without the ~a rule: ~a\n" (car sw)
                 (if found (format "found, the machine says ~a" (cadr found)) "NOTHING FOUND"))
         (when found (pretty-write (car found)))
         found))
     (define ok2
       (for/fold ([ok #t]) ([m mutants])
         (define found (parameterize ([mutant (car m)]) (search 80000 1 #:quiet #t)))
         (printf "if ~a: ~a\n" (cadr m)
                 (if found (format "found, the machine says ~a" (cadr found)) "NOTHING FOUND"))
         (when found (pretty-write (car found)))
         (and ok found #t)))
     (exit (if (and ok ok2) 0 1))]
    [(vector) (let ([f (search 20000 1)]) (report f) (exit (if f 1 0)))]
    [(vector n seed) (let ([f (search (string->number n) (string->number seed))]) (report f) (exit (if f 1 0)))]))
