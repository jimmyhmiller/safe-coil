#lang racket
;; What a program does, with every memory error made explicit.
;;
;; This file shares nothing with rules.rkt: no types, no loans. Every variable,
;; box and global is a cell; a reference or raw pointer is a cell and a path into
;; the value it holds (a field, a variant's payload, a pool element). A cell dies
;; when its scope ends or its owner is dropped.
;;
;; The machine is STUCK on what the rules exist to rule out: a read or write of
;; a dead cell, a read of a moved value, a double free, a path into a variant or
;; pool element that is no longer there, and two accesses to one place from the
;; two sides of a `par` when one of them writes.
;;
;; It PANICS, which is a defined stop and not an error, on the two checks safe
;; Coil makes at run time: a stale handle, and a global entered while it is
;; already lent in a way that conflicts.
(provide run check-globals?)

(struct stuck (why) #:transparent)
(struct panic (why) #:transparent)
(struct brk ())
(struct cell (v live? heap?) #:mutable)

;; Testing the tests: without the run-time check on globals, the search must
;; find a program that gets stuck.
(define check-globals? (make-parameter #t))

;; -> (list 'ok value leaked-cells) | (list 'stuck why) | (list 'panic why) | (list 'timeout)
(define (run prog [fuel 20000])
  (match-define `(program ,decls ,main) prog)
  (define store (make-hasheqv))
  (define next 0)
  (define steps 0)
  (define globals (make-hasheq))  ; g -> cell address
  (define lent (make-hasheq))     ; g -> (mcons readers writer?)
  ;; inside a `par` side: every access made, to compare with the other side's
  (define log #f)
  (define held '())               ; globals this side has entered: (g . w)

  (define (find kind name)
    (for/first ([d decls] #:when (and (eq? (car d) kind) (eq? (cadr d) name))) d))
  (define (field-names τ)
    (match τ
      [`(view ,V) (map car (caddr (find 'view V)))]
      [(cons S _) (map car (cadddr (find 'struct S)))]))

  (define (alloc! v heap?)
    (set! next (add1 next))
    (hash-set! store next (cell v #t heap?))
    next)
  (define (log! a path write?)
    (when log (hash-set! log (list a path write? held) #t)))
  (define (live-cell a what)
    (define c (hash-ref store a))
    (unless (cell-live? c) (raise (stuck (format "~a a dead cell" what))))
    c)

  ;; the part of v at path
  (define (nav v path)
    (cond
      [(null? path) v]
      [else
       (match* ((car path) v)
         [(_ 'moved) (raise (stuck "use of a moved value"))]
         [(`(f ,fld) `(rec . ,fs)) (nav (cdr (assq fld fs)) (cdr path))]
         [(`(k ,K) `(var ,K2 ,pv))
          (unless (eq? K K2) (raise (stuck "a reference to the payload of a variant that was replaced")))
          (nav pv (cdr path))]
         [(`(e ,slot) `(tbl . ,es))
          (match (assv slot es)
            [(cons _ ev) (nav ev (cdr path))]
            [_ (raise (stuck "a reference to a pool element that was removed"))])]
         [(step v) (raise (stuck (format "no ~a in ~a" step v)))])]))
  ;; v with the part at path replaced
  (define (update v path new)
    (cond
      [(null? path) new]
      [else
       (match* ((car path) v)
         [(_ 'moved) (raise (stuck "use of a moved value"))]
         [(`(f ,fld) `(rec . ,fs))
          `(rec ,@(for/list ([f fs]) (if (eq? (car f) fld) (cons fld (update (cdr f) (cdr path) new)) f)))]
         [(`(k ,K) `(var ,K2 ,pv))
          (unless (eq? K K2) (raise (stuck "a reference to the payload of a variant that was replaced")))
          `(var ,K ,(update pv (cdr path) new))]
         [(`(e ,slot) `(tbl . ,es))
          (unless (assv slot es) (raise (stuck "a reference to a pool element that was removed")))
          `(tbl ,@(for/list ([e es]) (if (eqv? (car e) slot) (cons slot (update (cdr e) (cdr path) new)) e)))]
         [(step v) (raise (stuck (format "no ~a in ~a" step v)))])]))

  ;; an address is (cell . path)
  (define (peek ad what)
    (nav (cell-v (live-cell (car ad) what)) (cdr ad)))
  (define (read! ad)
    (log! (car ad) (cdr ad) #f)
    (define v (peek ad "read of"))
    (when (eq? v 'moved) (raise (stuck "read of a moved value")))
    v)
  (define (write! ad v)
    (log! (car ad) (cdr ad) #t)
    (define c (live-cell (car ad) "write to"))
    (set-cell-v! c (update (cell-v c) (cdr ad) v)))
  (define (kill! a)
    (log! a '() #t)
    (set-cell-live?! (hash-ref store a) #f))

  (define (owning? v)
    (match v
      [`(own ,_) #t]
      [`(tbl . ,_) #t]
      [`(rec (,_ . ,vs) ...) (ormap owning? vs)]
      [`(var ,_ ,pv) (owning? pv)]
      [_ #f]))
  (define (drop-val! v)
    (match v
      [`(own ,a)
       (define c (hash-ref store a))
       (unless (cell-live? c) (raise (stuck "double free")))
       (drop-val! (cell-v c))
       (kill! a)]
      [`(rec (,_ . ,vs) ...) (for-each drop-val! vs)]
      [`(var ,_ ,pv) (drop-val! pv)]
      [`(tbl (,_ . ,vs) ...) (for-each drop-val! vs)]
      [_ (void)]))
  (define (end-scope! a)
    (drop-val! (cell-v (hash-ref store a)))
    (kill! a))

  ;; run thunk, then cleanup; a break passing through runs it too
  (define (scoped cleanup thunk)
    (define r (with-handlers ([brk? (λ (b) (cleanup) (raise b))]) (thunk)))
    (cleanup)
    r)

  (define (addr p env)
    (match p
      [(? symbol? x) (cons (hash-ref env x) '())]
      [`(* ,p2) (match (read! (addr p2 env))
                  [`(own ,a) (cons a '())]
                  [`(ptr ,a ,path) (cons a path)]
                  [v (raise (stuck (format "dereference of ~a" v)))])]
      [`(: ,p2 ,fld) (let ([ad (addr p2 env)]) (cons (car ad) (append (cdr ad) `((f ,fld)))))]
      [`(at ,p2 ,x)
       (define ad (addr p2 env))
       (match* ((read! (cons (hash-ref env x) '())) (read! ad))
         [(`(h ,slot) `(tbl . ,es))
          (unless (assv slot es) (raise (panic "stale handle")))
          (cons (car ad) (append (cdr ad) `((e ,slot))))]
         [(h t) (raise (stuck (format "element ~a of ~a" h t)))])]))

  ;; left to right; a break part way drops what was already made
  (define (ev-list es env)
    (let loop ([es es] [acc '()])
      (if (null? es)
          (reverse acc)
          (let ([v (with-handlers ([brk? (λ (b) (for-each drop-val! acc) (raise b))])
                     (ev (car es) env))])
            (loop (cdr es) (cons v acc))))))

  (define (invoke fn vs)
    (match-define `(defn ,_ ,_ ,params ,_ ,body) fn)
    (define cells (for/list ([v vs]) (alloc! v #f)))
    (scoped (λ () (for-each end-scope! (reverse cells)))
            (λ () (ev body (for/fold ([h (hasheq)]) ([p params] [a cells]) (hash-set h (car p) a))))))

  (define (bind-arm x v body env)
    (define a (alloc! v #f))
    (scoped (λ () (end-scope! a)) (λ () (ev body (hash-set env x a)))))
  (define (arm-of arms K)
    (for/first ([arm arms] #:when (eq? (caar arm) K)) arm))

  ;; do the two sides touch one place, one of them writing, with no global
  ;; whose `with` keeps them apart?
  (define (race? l1 l2)
    (define by-cell (make-hasheqv))
    (for ([k (in-hash-keys l2)]) (hash-update! by-cell (car k) (λ (ks) (cons k ks)) '()))
    (define (inside? a b) (and (<= (length a) (length b)) (equal? a (take b (length a)))))
    (define (apart? h1 h2)
      (for/or ([g1 h1])
        (for/or ([g2 h2]) (and (eq? (car g1) (car g2)) (or (eq? (cdr g1) 'mut) (eq? (cdr g2) 'mut))))))
    (for/or ([k1 (in-hash-keys l1)])
      (match-define (list a p1 w1 h1) k1)
      (for/or ([k2 (hash-ref by-cell a '())])
        (match-define (list _ p2 w2 h2) k2)
        (and (or w1 w2) (or (inside? p1 p2) (inside? p2 p1)) (not (apart? h1 h2))))))

  (define (ev e env)
    (set! steps (add1 steps))
    (when (> steps fuel) (raise 'timeout))
    (match e
      [(? integer?) e]
      ['unit 'unit]
      [(or (? symbol?) `(* ,_) `(: ,_ ,_) `(at ,_ ,_))
       (define ad (addr e env))
       (define v (read! ad))
       ;; an owner is moved out of where it was; anything else is copied
       (when (owning? v) (write! ad 'moved))
       v]
      [`(let ([,x ,e1]) ,e2)
       (define a (alloc! (ev e1 env) #f))
       (scoped (λ () (end-scope! a)) (λ () (ev e2 (hash-set env x a))))]
      [`(seq ,e1 ,e2) (drop-val! (ev e1 env)) (ev e2 env)]
      [`(if0 ,c ,t ,f) (if (eqv? (ev c env) 0) (ev t env) (ev f env))]
      [`(+ ,a ,b) (let* ([x (ev a env)] [y (ev b env)]) (+ x y))]
      [`(while ,c ,b)
       (let loop ()
         (unless (eqv? (ev c env) 0)
           (when (with-handlers ([brk? (λ (_) #f)]) (drop-val! (ev b env)) #t)
             (loop))))
       'unit]
      [`(break) (raise (brk))]
      [`(box ,e1) `(own ,(alloc! (ev e1 env) #t))]
      [`(unbox ,e1)
       (match (ev e1 env)
         [`(own ,a)
          (define v (read! (cons a '())))
          (kill! a)
          v])]
      [`(,(or 'ref 'mut 'addr) ,p) (let ([ad (addr p env)]) `(ptr ,(car ad) ,(cdr ad)))]
      [`(set! ,p ,e1)
       (define v (ev e1 env))
       (define ad (addr p env))
       (drop-val! (peek ad "write to"))
       (write! ad v)
       'unit]
      [`(take ,p ,e1)
       (define v (ev e1 env))
       (define ad (addr p env))
       (define old (read! ad))
       (write! ad v)
       old]
      [`(new ,τ ,es ...)
       `(rec ,@(map cons (field-names τ) (ev-list es env)))]
      [`(inj ,_ ,K ,e1) `(var ,K ,(ev e1 env))]
      [`(match ,e1 ,arms ...)
       (match (ev e1 env)
         [`(var ,K ,pv)
          (match-define `((,_ ,x) ,body) (arm-of arms K))
          (bind-arm x pv body env)])]
      [`(,(or 'match-ref 'match-mut) ,p ,arms ...)
       (define ad (addr p env))
       (match (read! ad)
         [`(var ,K ,_)
          (match-define `((,_ ,x) ,body) (arm-of arms K))
          (bind-arm x `(ptr ,(car ad) ,(append (cdr ad) `((k ,K)))) body env)])]
      [`(pool-new ,_) '(tbl)]
      [`(insert ,p ,e1)
       (define v (ev e1 env))
       (define ad (addr p env))
       (match (read! ad)
         [`(tbl . ,es)
          (set! next (add1 next))
          (write! ad `(tbl ,@es (,next . ,v)))
          `(h ,next)])]
      [`(remove ,p ,x)
       (define ad (addr p env))
       (match* ((read! (cons (hash-ref env x) '())) (read! ad))
         [(`(h ,slot) `(tbl . ,es))
          (match (assv slot es)
            [(cons _ v)
             (write! ad `(tbl ,@(filter (λ (e) (not (eqv? (car e) slot))) es)))
             v]
            [_ (raise (panic "stale handle"))])])]
      [`(call ,f ,_ ,args ...) (invoke (find 'defn f) (ev-list args env))]
      [`(par (call ,f1 ,_ ,args1 ...) (call ,f2 ,_ ,args2 ...))
       (define vs (ev-list (append args1 args2) env))
       (define-values (vs1 vs2) (split-at vs (length args1)))
       (define outer-log log)
       (define outer-held held)
       (define (side fn vs)
         (set! log (make-hash))
         (set! held '())
         (drop-val! (invoke fn vs))
         log)
       (define l1 (side (find 'defn f1) vs1))
       (define l2 (side (find 'defn f2) vs2))
       (set! log outer-log)
       (set! held outer-held)
       (when (race? l1 l2) (raise (stuck "data race")))
       (when log
         (for* ([l (list l1 l2)] [k (in-hash-keys l)])
           (match-define (list a path w h) k)
           (hash-set! log (list a path w (append h held)) #t)))
       'unit]
      [`(with ,w ,g ,x ,body)
       (define st (hash-ref lent g))
       (when (check-globals?)
         (when (or (mcdr st) (and (eq? w 'mut) (positive? (mcar st))))
           (raise (panic "a global entered while it is lent"))))
       (define was-writer (mcdr st))
       (if (eq? w 'mut) (set-mcdr! st #t) (set-mcar! st (add1 (mcar st))))
       (define outer-held held)
       (set! held (cons (cons g w) held))
       (define a (alloc! `(ptr ,(hash-ref globals g) ()) #f))
       (scoped (λ ()
                 (end-scope! a)
                 (set! held outer-held)
                 (if (eq? w 'mut) (set-mcdr! st was-writer) (set-mcar! st (sub1 (mcar st)))))
               (λ () (ev body (hash-set env x a))))]
      [`(unsafe ,e1) (ev e1 env)]
      [`(load ,e1)
       (match (ev e1 env) [`(ptr ,a ,path) (read! (cons a path))])]
      [`(store ,e1 ,e2)
       (match (ev e1 env)
         [`(ptr ,a ,path) (write! (cons a path) (ev e2 env)) 'unit])]
      [`(alloc ,e1) `(ptr ,(alloc! (ev e1 env) #t) ())]
      [`(free ,e1)
       (match (ev e1 env)
         [`(ptr ,a ,path)
          (define c (live-cell a "free of"))
          (unless (and (null? path) (cell-heap? c)) (raise (stuck "free of what was not allocated")))
          (kill! a)
          'unit])]))

  (with-handlers ([stuck? (λ (s) (list 'stuck (stuck-why s)))]
                  [panic? (λ (s) (list 'panic (panic-why s)))]
                  [brk? (λ (_) (list 'stuck "a break with no loop around it"))]
                  [(λ (x) (eq? x 'timeout)) (λ (_) (list 'timeout))])
    (define order
      (for/list ([d decls] #:when (eq? (car d) 'global))
        (match-define `(global ,g ,_ ,init) d)
        (define a (alloc! (ev init (hasheq)) #f))
        (hash-set! globals g a)
        (hash-set! lent g (mcons 0 #f))
        a))
    (define v (ev main (hasheq)))
    (drop-val! v)
    (for-each end-scope! (reverse order))
    (list 'ok v (for/sum ([(a c) store]) (if (and (cell-heap? c) (cell-live? c)) 1 0)))))
