#lang racket
;; Hand-written programs: each says whether the rules must take it, and the
;; machine says what happens when it runs. A rejected program that would have
;; gone wrong shows the rule earning its keep; an accepted one must never be stuck.
(require "rules.rkt" "machine.rkt")
(provide cases run-cases)

(define cases
  `(;; ---- accepted
    (accept "plain data"
     (program () (let ([a 1]) (+ a a))))
    (accept "an owner is dropped at the end of its scope"
     (program () (let ([b (box 7)]) (* b))))
    (accept "a move, then the new owner is used"
     (program () (let ([a (box 1)]) (let ([b a]) (* b)))))
    (accept "lend shared to a call"
     (program ((defn get ((r (ref int))) int (* r)))
              (let ([a (box 3)]) (call get (ref (* a))))))
    (accept "lend exclusively, then read the owner"
     (program ((defn bump ((r (mut int))) unit (set! (* r) (+ (* r) 1))))
              (let ([a (box 3)]) (seq (call bump (mut (* a))) (* a)))))
    (accept "a returned reference, used while its source is alive"
     (program ((defn inner ((r (ref (box int)))) (ref int) (ref (* (* r)))))
              (let ([a (box 3)]) (let ([r (call inner (ref a))]) (* r)))))
    (accept "two shared loans of one place"
     (program ((defn add ((x (ref int)) (y (ref int))) int (+ (* x) (* y))))
              (let ([a 4]) (call add (ref a) (ref a)))))
    (accept "exclusive loans of two different places"
     (program ((defn both ((x (mut int)) (y (mut int))) unit
                 (seq (set! (* x) 1) (set! (* y) 2))))
              (let ([a 0]) (let ([b 0]) (seq (call both (mut a) (mut b)) (+ a b))))))
    (accept "an exclusive reference reborrowed for a call"
     (program ((defn bump ((r (mut int))) unit (set! (* r) (+ (* r) 1)))
               (defn twice ((r (mut int))) unit
                 (seq (call bump (mut (* r))) (call bump (mut (* r))))))
              (let ([a 0]) (seq (call twice (mut a)) a))))
    (accept "replace a box through an exclusive reference"
     (program ((defn renew ((m (mut (box int)))) unit (set! (* m) (box 9))))
              (let ([a (box 1)]) (seq (call renew (mut a)) (* a)))))
    (accept "moved in one branch only: dropped where it ended up"
     (program ((defn eat ((b (box int))) int (* b)))
              (let ([a (box 1)]) (if0 0 (call eat a) 5))))

    ;; ---- rejected: the four holes found in today's Coil, and their relatives
    (reject "a reference to a local is returned from its scope"
     (program () (let ([r (let ([a (box 1)]) (ref (* a)))]) (* r))))
    (reject "a function returns a reference to its own parameter's storage"
     (program ((defn dangle ((b (box int))) (ref int) (ref (* b))))
              (let ([r (call dangle (box 1))]) (* r))))
    (reject "a reference is held across the move of its owner"
     (program ((defn eat ((b (box int))) int (* b)))
              (let ([a (box 1)])
                (let ([r (ref (* a))])
                  (seq (call eat a) (* r))))))
    (reject "one place lent exclusively twice in a call"
     (program ((defn both ((x (mut (box int))) (y (mut (box int)))) int
                 (let ([r (ref (* (* y)))])
                   (seq (set! (* x) (box 2)) (* r)))))
              (let ([a (box 1)]) (call both (mut a) (mut a)))))
    (reject "an element reference passed beside the exclusive loan that frees it"
     (program ((defn grow ((xs (mut (box int))) (x (ref int))) int
                 (seq (set! (* xs) (box 2)) (* x))))
              (let ([a (box 5)]) (call grow (mut a) (ref (* a))))))
    (reject "the owner is replaced while a reference into it is alive"
     (program () (let ([a (box 1)])
                   (let ([r (ref (* a))])
                     (seq (set! a (box 2)) (* r))))))
    (reject "use after move"
     (program () (let ([a (box 1)]) (let ([b a]) (* a)))))
    (reject "moved twice"
     (program ((defn eat ((b (box int))) int (* b)))
              (let ([a (box 1)]) (+ (call eat a) (call eat a)))))
    (reject "a write through a shared reference"
     (program ((defn poke ((r (ref int))) unit (set! (* r) 1)))
              (let ([a 0]) (seq (call poke (ref a)) a))))
    (reject "an exclusive reference used while it is reborrowed"
     (program ((defn take ((x (mut int)) (y (mut int))) unit unit))
              (let ([a 0]) (let ([r (mut a)]) (seq (call take (mut (* r)) r) a)))))
    (reject "the returned reference outlives the argument it came from"
     (program ((defn inner ((r (ref (box int)))) (ref int) (ref (* (* r)))))
              (let ([r (let ([a (box 3)]) (call inner (ref a)))]) (* r))))
    (reject "a reference inside a box is not a type"
     (program () (let ([a 1]) (let ([b (box (ref a))]) 0))))))

(define (run-cases)
  (define bad 0)
  (define caught 0)
  (for ([c cases])
    (match-define (list want name prog) c)
    (define got (if (check-program prog) 'accept 'reject))
    (define ran (run prog))
    (define wrong
      (cond [(not (eq? got want)) (format "the rules ~aed it" got)]
            [(and (eq? got 'accept) (not (equal? (car ran) 'ok))) (format "accepted, and it ran: ~a" ran)]
            [(and (eq? got 'accept) (not (eqv? (caddr ran) 0))) (format "accepted, and it leaked ~a" (caddr ran))]
            [else #f]))
    (when (and (eq? want 'reject) (eq? (car ran) 'stuck)) (set! caught (add1 caught)))
    (when wrong
      (set! bad (add1 bad))
      (printf "FAIL ~a: ~a\n" name wrong)))
  (printf "cases: ~a, failed: ~a; rejected programs that go wrong when run anyway: ~a of ~a\n"
          (length cases) bad caught (count (λ (c) (eq? (car c) 'reject)) cases))
  (zero? bad))

(module+ main (exit (if (run-cases) 0 1)))
