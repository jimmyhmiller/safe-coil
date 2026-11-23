#lang racket
;; What a program does, with every memory error made explicit.
;;
;; This file shares nothing with rules.rkt: no types, no loans. Every variable
;; and every box is a cell with an address; a reference is a bare address. A cell
;; dies when its scope ends or its owner is dropped. The machine is STUCK when a
;; program reads or writes a dead cell, reads a moved value, or frees twice:
;; those are the errors the rules exist to rule out.
(provide run (struct-out stuck))

(struct stuck (why) #:transparent)
(struct cell (v live? heap?) #:mutable)

;; -> (list 'ok value leaked-cells) | (list 'stuck why) | (list 'timeout)
(define (run prog [fuel 20000])
  (match-define `(program ,F ,main) prog)
  (define store (make-hasheqv))
  (define next 0)
  (define steps 0)
  (define (alloc! v heap?)
    (set! next (add1 next))
    (hash-set! store next (cell v #t heap?))
    next)
  (define (live-cell a what)
    (define c (hash-ref store a))
    (unless (cell-live? c) (raise (stuck (format "~a a dead cell" what))))
    c)
  (define (read! a)
    (define v (cell-v (live-cell a "read of")))
    (when (eq? v 'moved) (raise (stuck "read of a moved value")))
    v)
  (define (write! a v) (set-cell-v! (live-cell a "write to") v))
  (define (drop-val! v)
    (match v
      [`(own ,a)
       (define c (hash-ref store a))
       (unless (cell-live? c) (raise (stuck "double free")))
       (unless (eq? (cell-v c) 'moved) (drop-val! (cell-v c)))
       (set-cell-live?! c #f)]
      [_ (void)]))
  (define (end-scope! a)
    (define c (hash-ref store a))
    (unless (eq? (cell-v c) 'moved) (drop-val! (cell-v c)))
    (set-cell-live?! c #f))
  (define (addr p env)
    (match p
      [(? symbol? x) (hash-ref env x)]
      [`(* ,p2) (match (read! (addr p2 env))
                  [`(,(or 'own 'ptr) ,a) a]
                  [v (raise (stuck (format "dereference of ~a" v)))])]))
  (define (ev e env)
    (set! steps (add1 steps))
    (when (> steps fuel) (raise 'timeout))
    (match e
      [(? integer?) e]
      ['unit 'unit]
      [(or (? symbol?) `(* ,_))
       (define a (addr e env))
       (define v (read! a))
       ;; an owner is moved out of where it was; anything else is copied
       (when (and (pair? v) (eq? (car v) 'own)) (write! a 'moved))
       v]
      [`(let ([,x ,e1]) ,e2)
       (define a (alloc! (ev e1 env) #f))
       (define r (ev e2 (hash-set env x a)))
       (end-scope! a)
       r]
      [`(seq ,e1 ,e2) (drop-val! (ev e1 env)) (ev e2 env)]
      [`(box ,e1) `(own ,(alloc! (ev e1 env) #t))]
      [`(,(or 'ref 'mut) ,p) `(ptr ,(addr p env))]
      [`(set! ,p ,e1)
       (define v (ev e1 env))
       (define a (addr p env))
       (drop-val! (read! a))
       (write! a v)
       'unit]
      [`(if0 ,c ,t ,f) (if (eqv? (ev c env) 0) (ev t env) (ev f env))]
      [`(+ ,a ,b) (let* ([x (ev a env)] [y (ev b env)]) (+ x y))]
      [`(call ,f ,args ...)
       (match-define `(defn ,_ ,params ,_ ,body) (for/first ([fn F] #:when (eq? (cadr fn) f)) fn))
       (define vs (for/list ([a args]) (ev a env)))
       (define cells (for/list ([v vs]) (alloc! v #f)))
       (define r (ev body (for/fold ([h (hasheq)]) ([p params] [a cells]) (hash-set h (car p) a))))
       (for-each end-scope! (reverse cells))
       r]))
  (with-handlers ([stuck? (λ (s) (list 'stuck (stuck-why s)))]
                  [(λ (x) (eq? x 'timeout)) (λ (_) (list 'timeout))])
    (define v (ev main (hasheq)))
    (drop-val! v)
    (list 'ok v (for/sum ([(a c) store]) (if (and (cell-heap? c) (cell-live? c)) 1 0)))))
