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
;; a `return`: the value the function gives back
(struct ret (v))
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
  ;; threads not yet joined: id -> (cons accesses-by-cell result). A thread's
  ;; call is run to its end where it is spawned; what it touched is then
  ;; compared with everything done until it is joined.
  (define tasks (make-hasheqv))

  (define (find kind name)
    (for/first ([d decls] #:when (and (eq? (car d) kind) (eq? (cadr d) name))) d))
  (define (field-names τ)
    (match τ
      [`(view ,V) (map car (caddr (find 'view V)))]
      [(cons S _) (map car (cadddr (find 'struct S)))]))
  ;; the function a view's drop runs, or #f
  (define (view-drop V)
    (match (find 'view V) [`(view ,_ ,_ ,f) f] [_ #f]))

  (define (alloc! v heap?)
    (set! next (add1 next))
    (hash-set! store next (cell v #t heap?))
    next)
  (define (log! a path write?)
    (when log (hash-set! log (list a path write? held) #t))
    (for ([t (in-hash-values tasks)])
      (when (races? (list a path write? held) (car t)) (raise (stuck "data race")))))
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
      [`(oclo ,_) #t]
      [`(arena ,_) #t]
      [`(abox ,_) #t]
      ;; a view whose drop runs code is moved, so that the code runs once
      [`(rec (%drop . ,_) . ,_) #t]
      [`(task ,_) #t]
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
      [`(oclo ,a)
       (define c (hash-ref store a))
       (unless (cell-live? c) (raise (stuck "double free")))
       (match (cell-v c)
         [`(env ,caps ,_ ,_)
          (for ([cap caps]) (end-scope! (cdr cap)))])
       (kill! a)]
      [`(rec (%drop . ,V) . ,fs)
       (drop-val! (invoke (find 'defn (view-drop V)) (list `(rec ,@fs))))]
      ;; an arena gives back the memory of everything in it
      [`(arena ,a)
       (define c (hash-ref store a))
       (unless (cell-live? c) (raise (stuck "double free")))
       (empty-arena! a)
       (kill! a)]
      ;; a box in an arena owns nothing to drop; its memory is the arena's.
      ;; Its cell must still be there: the box may not outlive the arena.
      [`(abox ,m) (live-cell m "drop in") (void)]
      [`(rec (,_ . ,vs) ...) (for-each drop-val! vs)]
      [`(var ,_ ,pv) (drop-val! pv)]
      [`(tbl (,_ . ,vs) ...) (for-each drop-val! vs)]
      ;; a task that is dropped waits for its thread and drops what it returned
      [`(task ,id) (drop-val! (finish! id))]
      [_ (void)]))
  ;; the thread is over: what its call returned
  (define (finish! id)
    (define t (hash-ref tasks id (λ () (raise (stuck "a task joined twice")))))
    (hash-remove! tasks id)
    (cdr t))
  ;; every cell the arena A gave out is given back; nothing in one is dropped
  (define (empty-arena! a)
    (match (cell-v (hash-ref store a))
      [`(members . ,ms)
       (for ([m ms])
         (when (cell-live? (hash-ref store m)) (kill! m)))
       (set-cell-v! (hash-ref store a) '(members))]))
  (define (end-scope! a)
    (drop-val! (cell-v (hash-ref store a)))
    (kill! a))

  ;; run thunk, then cleanup; a break or a return passing through runs it too
  (define (scoped cleanup thunk)
    (define r (with-handlers ([(λ (x) (or (brk? x) (ret? x))) (λ (b) (cleanup) (raise b))]) (thunk)))
    (cleanup)
    r)

  (define (addr p env)
    (match p
      [(? symbol? x) (cons (hash-ref env x) '())]
      [`(* ,p2) (match (read! (addr p2 env))
                  [`(own ,a) (cons a '())]
                  [`(abox ,a) (cons a '())]
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
          (let ([v (with-handlers ([(λ (x) (or (brk? x) (ret? x))) (λ (b) (for-each drop-val! acc) (raise b))])
                     (ev (car es) env))])
            (loop (cdr es) (cons v acc))))))

  (define (invoke fn vs)
    (match-define `(defn ,_ ,_ ,params ,_ ,body) fn)
    (run-body body (for/list ([p params] [v vs]) (cons (car p) (alloc! v #f))) '()))
  ;; a body over variables in cells: the cells in OWN end with it, the others
  ;; (an owning closure's captures) stay
  (define (run-body body own others)
    (with-handlers ([ret? ret-v])
      (scoped (λ () (for-each end-scope! (reverse (map cdr own))))
              (λ () (ev body (for/fold ([h (hasheq)]) ([c (append others own)]) (hash-set h (car c) (cdr c))))))))
  (define (apply-closure f vs)
    (match f
      [`(clo ,caps ,ps ,body)
       (run-body body (append (for/list ([c caps]) (cons (car c) (alloc! (cdr c) #f)))
                              (for/list ([x ps] [v vs]) (cons x (alloc! v #f))))
                 '())]
      [`(oclo ,a)
       (match-define `(env ,caps ,ps ,body) (read! (cons a '())))
       (run-body body (for/list ([x ps] [v vs]) (cons x (alloc! v #f))) caps)]
      [_ (raise (stuck (format "a call of ~a" f)))]))

  (define (bind-arm x v body env)
    (define a (alloc! v #f))
    (scoped (λ () (end-scope! a)) (λ () (ev body (hash-set env x a)))))
  (define (arm-of arms K)
    (for/first ([arm arms] #:when (eq? (caar arm) K)) arm))

  ;; do the two sides touch one place, one of them writing, with no global
  ;; whose `with` keeps them apart?
  (define (by-cell l)
    (define cells (make-hasheqv))
    (for ([k (in-hash-keys l)]) (hash-update! cells (car k) (λ (ks) (cons k ks)) '()))
    cells)
  ;; does the access k1 race with one of the accesses in cells?
  (define (races? k1 cells)
    (define (inside? a b) (and (<= (length a) (length b)) (equal? a (take b (length a)))))
    (define (apart? h1 h2)
      (for/or ([g1 h1])
        (for/or ([g2 h2]) (and (eq? (car g1) (car g2)) (or (eq? (cdr g1) 'mut) (eq? (cdr g2) 'mut))))))
    (match-define (list a p1 w1 h1) k1)
    (for/or ([k2 (hash-ref cells a '())])
      (match-define (list _ p2 w2 h2) k2)
      (and (or w1 w2) (or (inside? p1 p2) (inside? p2 p1)) (not (apart? h1 h2)))))
  (define (race? l1 l2)
    (define cells (by-cell l2))
    (for/or ([k1 (in-hash-keys l1)]) (races? k1 cells)))

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
      [`(return ,e1 ,_) (raise (ret (ev e1 env)))]
      [`(uninit ,_) 'moved]
      [`(lam ([,ys ,_ ,es] ...) ((,ps ,_) ...) ,_ ,body)
       `(clo ,(map cons ys (ev-list es env)) ,ps ,body)]
      [`(lamo ([,ys ,_ ,es] ...) ((,ps ,_) ...) ,_ ,body)
       (define vs (ev-list es env))
       `(oclo ,(alloc! `(env ,(for/list ([y ys] [v vs]) (cons y (alloc! v #t))) ,ps ,body) #t))]
      [`(apply ,p ,args ...)
       (define ad (addr p env))
       (define f (read! ad))
       (when (eq? f 'moved) (raise (stuck "a call of a moved closure")))
       (apply-closure f (ev-list args env))]
      [`(box ,e1) `(own ,(alloc! (ev e1 env) #t))]
      [`(unbox ,e1)
       (match (ev e1 env)
         [`(own ,a)
          (define v (read! (cons a '())))
          (kill! a)
          v]
         [`(abox ,a)
          (define v (read! (cons a '())))
          (write! (cons a '()) 'moved)
          v])]
      ['(arena-new) `(arena ,(alloc! '(members) #t))]
      [`(abox ,p ,e1)
       (define v (ev e1 env))
       (match (read! (addr p env))
         [`(arena ,a)
          ;; making room changes the arena
          (log! a '() #t)
          (define m (alloc! v #t))
          (match (cell-v (live-cell a "allocation in"))
            [`(members . ,ms) (set-cell-v! (hash-ref store a) `(members ,@ms ,m))])
          `(abox ,m)]
         [x (raise (stuck (format "allocation in ~a" x)))])]
      [`(reset! ,p)
       (match (read! (addr p env))
         [`(arena ,a) (log! a '() #t) (empty-arena! a) 'unit]
         [x (raise (stuck (format "reset of ~a" x)))])]
      [`(,(or 'ref 'mut 'out 'addr) ,p) (let ([ad (addr p env)]) `(ptr ,(car ad) ,(cdr ad)))]
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
       (define fs (map cons (field-names τ) (ev-list es env)))
       (match τ
         [`(view ,V) #:when (view-drop V) `(rec (%drop . ,V) ,@fs)]
         [_ `(rec ,@fs)])]
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
      [`(spawn (call ,f ,_ ,args ...))
       (define vs (ev-list args env))
       (define outer-log log)
       (define outer-held held)
       (set! log (make-hash))
       (set! held '())
       (define v (with-handlers ([brk? (λ (_) (raise (stuck "a break with no loop around it")))])
                   (invoke (find 'defn f) vs)))
       (define mine log)
       (set! log outer-log)
       (set! held outer-held)
       ;; what the thread did is also done by whatever this is part of
       (when log (for ([k (in-hash-keys mine)]) (hash-set! log k #t)))
       (set! next (add1 next))
       (hash-set! tasks next (cons (by-cell mine) v))
       `(task ,next)]
      [`(spawn-fn ,e1)
       (define f (ev e1 env))
       (define outer-log log)
       (define outer-held held)
       (set! log (make-hash))
       (set! held '())
       (define v (with-handlers ([brk? (λ (_) (raise (stuck "a break with no loop around it")))])
                   (begin0 (apply-closure f '()) (drop-val! f))))
       (define mine log)
       (set! log outer-log)
       (set! held outer-held)
       (when log (for ([k (in-hash-keys mine)]) (hash-set! log k #t)))
       (set! next (add1 next))
       (hash-set! tasks next (cons (by-cell mine) v))
       `(task ,next)]
      [`(join ,e1) (match (ev e1 env) [`(task ,id) (finish! id)])]
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
                  [ret? (λ (_) (list 'stuck "a return outside a function"))]
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
