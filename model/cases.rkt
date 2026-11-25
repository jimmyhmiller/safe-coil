#lang racket
;; Hand-written programs: each says whether the rules must take it, and the
;; machine says what happens when it runs. A rejected program that would have
;; gone wrong shows the rule earning its keep; an accepted one must never be stuck.
;;
;;   accept         the rules take it; it runs to the end and frees everything
;;   accept-panic   the rules take it; a run-time check stops it
;;   accept-unsafe  the rules take it because of `unsafe`; what it does is its own affair
;;   reject         the rules refuse it
(require "rules.rkt" "machine.rkt")
(provide cases run-cases prelude)

(define prelude
  '((struct Pair () ((a (box int)) (b (box int))))
    (struct Pt () ((m int) (n int)))
    (struct Wrap (T) ((v T) (w int)))
    (sum Opt (T) ((None unit) (Some T)))
    (view Two ((l (ref (box int))) (r (mut int))))
    (view Peek ((s (ref int)) (i int)))
    (global g1 (box int) (box 0))
    (global g2 (Opt (box int)) (inj (Opt (box int)) Some (box 1)))))

(define (prog fns main) `(program (,@prelude ,@fns) ,main))

(define cases
  `(;; ================================================== owners and references
    (accept "plain data"
     ,(prog '() '(let ([a 1]) (+ a a))))
    (accept "an owner is dropped at the end of its scope"
     ,(prog '() '(let ([b (box 7)]) (* b))))
    (accept "a move, then the new owner is used"
     ,(prog '() '(let ([a (box 1)]) (let ([b a]) (* b)))))
    (accept "lend shared to a call"
     ,(prog '((defn get () ((r (ref int))) int (* r)))
            '(let ([a (box 3)]) (call get () (ref (* a))))))
    (accept "lend exclusively, then read the owner"
     ,(prog '((defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1))))
            '(let ([a (box 3)]) (seq (call bump () (mut (* a))) (* a)))))
    (accept "a returned reference, used while its source is alive"
     ,(prog '((defn inner () ((r (ref (box int)))) (ref int) (ref (* (* r)))))
            '(let ([a (box 3)]) (let ([r (call inner () (ref a))]) (* r)))))
    (accept "two shared loans of one place"
     ,(prog '((defn add () ((x (ref int)) (y (ref int))) int (+ (* x) (* y))))
            '(let ([a 4]) (call add () (ref a) (ref a)))))
    (accept "exclusive loans of two different places"
     ,(prog '((defn both () ((x (mut int)) (y (mut int))) unit
                (seq (set! (* x) 1) (set! (* y) 2))))
            '(let ([a 0]) (let ([b 0]) (seq (call both () (mut a) (mut b)) (+ a b))))))
    (accept "an exclusive reference reborrowed for a call"
     ,(prog '((defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1)))
              (defn twice () ((r (mut int))) unit
                (seq (call bump () (mut (* r))) (call bump () (mut (* r))))))
            '(let ([a 0]) (seq (call twice () (mut a)) a))))
    (accept "replace a box through an exclusive reference"
     ,(prog '((defn renew () ((m (mut (box int)))) unit (set! (* m) (box 9))))
            '(let ([a (box 1)]) (seq (call renew () (mut a)) (* a)))))
    (accept "moved in one branch only: dropped where it ended up"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (if0 0 (call eat () a) 5))))
    (accept "a moved variable is given a new value and used again"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (seq (call eat () a) (seq (set! a (box 2)) (* a))))))
    (accept "a variable is given what a call that took it returns"
     ,(prog '((defn same () ((b (box int))) (box int) b))
            '(let ([a (box 1)]) (seq (set! a (call same () a)) (* a)))))
    (accept "an outer owner moved inside a loop is given a new value in the same turn"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)])
               (let ([i 2])
                 (seq (while i (seq (call eat () a) (seq (set! a (box i)) (set! i (+ i -1)))))
                      (* a))))))
    (reject "a variable moved in one branch only is used after being given no value"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (seq (if0 0 (call eat () a) (seq (set! a (box 2)) 5)) (* a)))))
    ;; ================================================== a loan lasts while its holder is named
    (accept "a reference that is not named again no longer keeps its place lent"
     ,(prog '() '(let ([a 1]) (let ([r (ref a)]) (seq (* r) (seq (set! a 2) a))))))
    (accept "an exclusive reference that is not named again frees its place"
     ,(prog '() '(let ([a (box 1)])
                   (let ([m (mut a)]) (seq (set! (* m) (box 2)) (* a))))))
    (reject "a reference named later keeps its place lent"
     ,(prog '() '(let ([a (box 1)]) (let ([r (ref (* a))]) (seq (set! a (box 2)) (* r))))))
    (reject "a reference lent again keeps what its source borrowed"
     ,(prog '() '(let ([a (box 1)])
                   (let ([m (mut a)])
                     (let ([r (ref (* (* m)))]) (seq (set! a (box 2)) (* r)))))))
    (reject "a reference named in a loop is named by its next turn"
     ,(prog '() '(let ([a (box 1)])
                   (let ([r (ref (* a))])
                     (let ([i 2])
                       (seq (while i (seq (* r) (seq (set! a (box i)) (set! i (+ i -1)))))
                            0))))))
    (accept "an argument's reference ends with the call"
     ,(prog '((defn get () ((r (ref int))) int (* r)))
            '(let ([a 1]) (let ([r (ref a)]) (seq (call get () r) (seq (set! a 2) a))))))
    (accept "take an owner out of a box, leaving another in its place"
     ,(prog '() '(let ([a (box (box 1))]) (let ([old (take (* a) (box 2))]) (+ (* old) (* (* a)))))))
    (accept "unbox gives the contents and frees the box"
     ,(prog '() '(let ([a (box (box 4))]) (let ([c (unbox a)]) (* c)))))

    ;; the four holes found in today's Coil, and their relatives
    (reject "a reference to a local is returned from its scope"
     ,(prog '() '(let ([r (let ([a (box 1)]) (ref (* a)))]) (* r))))
    (reject "a function returns a reference to its own parameter's storage"
     ,(prog '((defn dangle () ((b (box int))) (ref int) (ref (* b))))
            '(let ([r (call dangle () (box 1))]) (* r))))
    (reject "a reference is held across the move of its owner"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)])
               (let ([r (ref (* a))])
                 (seq (call eat () a) (* r))))))
    (reject "one place lent exclusively twice in a call"
     ,(prog '((defn both () ((x (mut (box int))) (y (mut (box int)))) int
                (let ([r (ref (* (* y)))])
                  (seq (set! (* x) (box 2)) (* r)))))
            '(let ([a (box 1)]) (call both () (mut a) (mut a)))))
    (reject "an element reference passed beside the exclusive loan that frees it"
     ,(prog '((defn grow () ((xs (mut (box int))) (x (ref int))) int
                (seq (set! (* xs) (box 2)) (* x))))
            '(let ([a (box 5)]) (call grow () (mut a) (ref (* a))))))
    (reject "the owner is replaced while a reference into it is alive"
     ,(prog '() '(let ([a (box 1)])
                   (let ([r (ref (* a))])
                     (seq (set! a (box 2)) (* r))))))
    (reject "use after move"
     ,(prog '() '(let ([a (box 1)]) (let ([b a]) (* a)))))
    (reject "moved twice"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (+ (call eat () a) (call eat () a)))))
    (reject "a write through a shared reference"
     ,(prog '((defn poke () ((r (ref int))) unit (set! (* r) 1)))
            '(let ([a 0]) (seq (call poke () (ref a)) a))))
    (reject "an exclusive reference used while it is reborrowed"
     ,(prog '((defn pair () ((x (mut int)) (y (mut int))) unit unit))
            '(let ([a 0]) (let ([r (mut a)]) (seq (call pair () (mut (* r)) r) a)))))
    (reject "the returned reference outlives the argument it came from"
     ,(prog '((defn inner () ((r (ref (box int)))) (ref int) (ref (* (* r)))))
            '(let ([r (let ([a (box 3)]) (call inner () (ref a)))]) (* r))))
    (reject "a reference inside a box is not a type"
     ,(prog '() '(let ([a 1]) (let ([b (box (ref a))]) 0))))
    (reject "an owner cannot be moved out of a box by naming it"
     ,(prog '() '(let ([a (box (box 1))]) (let ([b (* a)]) (* b)))))
    (reject "take from a place that is lent"
     ,(prog '() '(let ([a (box (box 1))])
                   (let ([r (ref (* (* a)))])
                     (seq (take (* a) (box 2)) (* r))))))

    ;; ================================================== structs and fields
    (accept "two fields of one struct lent exclusively at once"
     ,(prog '((defn both () ((x (mut (box int))) (y (mut (box int)))) unit
                (seq (set! (* x) (box 5)) (set! (* y) (box 6)))))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (call both () (mut (: p a)) (mut (: p b)))
                    (+ (* (: p a)) (* (: p b)))))))
    (accept "a struct of plain data is copied"
     ,(prog '() '(let ([p (new (Pt) 1 2)]) (let ([q p]) (+ (: p m) (: q n))))))
    (accept "one field is written while another is lent"
     ,(prog '() '(let ([p (new (Pair) (box 1) (box 2))])
                   (let ([r (ref (* (: p a)))])
                     (seq (set! (: p b) (box 3)) (* r))))))
    (reject "a struct holding owners is moved, not copied"
     ,(prog '() '(let ([p (new (Pair) (box 1) (box 2))]) (let ([q p]) (* (: p a))))))
    (reject "a field is written while a reference into it is alive"
     ,(prog '() '(let ([p (new (Pair) (box 1) (box 2))])
                   (let ([r (ref (* (: p a)))])
                     (seq (set! (: p a) (box 3)) (* r))))))
    (reject "the whole struct is replaced while a field is lent"
     ,(prog '() '(let ([p (new (Pair) (box 1) (box 2))])
                   (let ([r (ref (* (: p a)))])
                     (seq (set! p (new (Pair) (box 3) (box 4))) (* r))))))
    (reject "the same field lent exclusively twice"
     ,(prog '((defn both () ((x (mut (box int))) (y (mut (box int)))) int
                (let ([r (ref (* (* y)))]) (seq (set! (* x) (box 2)) (* r)))))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (call both () (mut (: p a)) (mut (: p a))))))
    (reject "an owner cannot be moved out of a field by naming it"
     ,(prog '() '(let ([p (new (Pair) (box 1) (box 2))]) (let ([b (: p a)]) (* b)))))

    ;; ================================================== sums and match
    (accept "match by value: the arm owns the payload"
     ,(prog '() '(let ([o (inj (Opt (box int)) Some (box 4))])
                   (match o ((None u) 0) ((Some b) (* b))))))
    (accept "match by reference, then the sum is still there"
     ,(prog '() '(let ([o (inj (Opt (box int)) Some (box 4))])
                   (+ (match-ref o ((None u) 0) ((Some r) (* (* r))))
                      (match o ((None u) 0) ((Some b) (* b)))))))
    (accept "match by exclusive reference writes the payload"
     ,(prog '() '(let ([o (inj (Opt (box int)) Some (box 4))])
                   (seq (match-mut o ((None u) unit) ((Some r) (set! (* r) (box 8))))
                        (match o ((None u) 0) ((Some b) (* b)))))))
    (reject "the variant is replaced while an arm holds its payload"
     ,(prog '() '(let ([o (inj (Opt (box int)) Some (box 4))])
                   (match-ref o
                     ((None u) 0)
                     ((Some r) (seq (set! o (inj (Opt (box int)) None unit)) (* (* r))))))))
    (reject "the variant is replaced under an exclusive arm reference"
     ,(prog '() '(let ([o (inj (Opt int) Some 4)])
                   (match-mut o
                     ((None u) 0)
                     ((Some r) (seq (set! o (inj (Opt int) None unit)) (* r)))))))
    (reject "an arm's reference leaves the scope of the sum"
     ,(prog '() '(let ([r (let ([o (inj (Opt int) Some 4)])
                            (match-ref o ((None u) (ref o)) ((Some x) (ref o))))])
                   0)))
    (reject "the sum is used after a match by value consumed it"
     ,(prog '() '(let ([o (inj (Opt (box int)) Some (box 4))])
                   (+ (match o ((None u) 0) ((Some b) (* b)))
                      (match o ((None u) 0) ((Some b) (* b)))))))
    (reject "a match that leaves out a variant"
     ,(prog '() '(let ([o (inj (Opt int) Some 4)]) (match o ((Some b) b)))))
    (reject "an owner moved in one arm is used after the match"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)])
               (let ([o (inj (Opt int) Some 4)])
                 (seq (match o ((None u) 0) ((Some x) (call eat () a))) (* a))))))

    ;; ================================================== views
    (accept "a view is built from references and read through"
     ,(prog '() '(let ([a 5]) (let ([v (new (view Peek) (ref a) 0)]) (+ (* (: v s)) (: v i))))))
    (accept "a view with only shared references is copied"
     ,(prog '((defn peek () ((v (view Peek))) int (* (: v s))))
            '(let ([a 5]) (let ([v (new (view Peek) (ref a) 0)])
                            (+ (call peek () v) (call peek () v))))))
    (accept "a view's exclusive field is written through"
     ,(prog '() '(let ([a (box 1)])
                   (let ([c 0])
                     (seq (let ([v (new (view Two) (ref a) (mut c))])
                            (set! (* (: v r)) (* (* (: v l)))))
                          c)))))
    (accept "a function returns a view of its argument"
     ,(prog '((defn look () ((r (ref int))) (view Peek) (new (view Peek) r 1)))
            '(let ([a 5]) (let ([v (call look () (ref a))]) (* (: v s))))))
    (reject "a view outlives what it refers to"
     ,(prog '() '(let ([v (let ([a 5]) (new (view Peek) (ref a) 0))]) (* (: v s)))))
    (reject "what a view refers to is written while the view is alive"
     ,(prog '() '(let ([a (box 1)])
                   (let ([c 0])
                     (let ([v (new (view Two) (ref a) (mut c))])
                       (seq (set! a (box 2)) (* (* (: v l)))))))))
    (reject "a view with an exclusive reference is moved, not copied"
     ,(prog '((defn use () ((v (view Two))) unit (set! (* (: v r)) 1)))
            '(let ([a (box 1)])
               (let ([c 0])
                 (let ([v (new (view Two) (ref a) (mut c))])
                   (seq (call use () v) (call use () v)))))))
    (reject "a reference to a view's own field outlives the view"
     ,(prog '() '(let ([a 5])
                   (let ([r (let ([v (new (view Peek) (ref a) 7)]) (ref (: v i)))])
                     (* r)))))
    (reject "a view inside a box is not a type"
     ,(prog '() '(let ([a 5]) (let ([b (box (new (view Peek) (ref a) 0))]) 0))))
    (reject "a function returns a view of its own local"
     ,(prog '((defn look () ((a int)) (view Peek) (new (view Peek) (ref a) 1)))
            '(let ([v (call look () 5)]) (* (: v s)))))

    ;; ================================================== pools and handles
    (accept "insert, read through the handle, remove"
     ,(prog '() '(let ([pl (pool-new (box int))])
                   (let ([h (insert pl (box 3))])
                     (let ([n (* (at pl h))])
                       (let ([b (remove pl h)]) (+ n (* b))))))))
    (accept "a handle is plain data: copied, and stored in a box"
     ,(prog '() '(let ([pl (pool-new int)])
                   (let ([h (insert pl 3)])
                     (let ([b (box h)])
                       (let ([h2 (* b)]) (+ (at pl h) (at pl h2))))))))
    (accept "the pool is dropped with its elements"
     ,(prog '() '(let ([pl (pool-new (box int))])
                   (seq (insert pl (box 1)) (seq (insert pl (box 2)) 0)))))
    (accept-panic "a stale handle is caught when it is used"
     ,(prog '() '(let ([pl (pool-new (box int))])
                   (let ([h (insert pl (box 3))])
                     (seq (remove pl h) (* (at pl h)))))))
    (accept-panic "a handle outlives its pool and is used on another"
     ,(prog '() '(let ([h (let ([pl (pool-new int)]) (insert pl 1))])
                   (let ([pl2 (pool-new int)]) (at pl2 h)))))
    (reject "an element is removed while a reference to it is alive"
     ,(prog '() '(let ([pl (pool-new (box int))])
                   (let ([h (insert pl (box 3))])
                     (let ([r (ref (* (at pl h)))])
                       (seq (remove pl h) (* r)))))))
    (reject "the pool is replaced while an element is lent"
     ,(prog '() '(let ([pl (pool-new (box int))])
                   (let ([h (insert pl (box 3))])
                     (let ([r (ref (* (at pl h)))])
                       (seq (set! pl (pool-new (box int))) (* r)))))))
    (reject "an element reference passed beside the exclusive loan of its pool"
     ,(prog '((defn shrink () ((pl (mut (pool (box int)))) (h (handle (box int))) (x (ref int))) int
                (seq (remove (* pl) h) (* x))))
            '(let ([pl (pool-new (box int))])
               (let ([h (insert pl (box 3))])
                 (call shrink () (mut pl) h (ref (* (at pl h))))))))
    (reject "insert through a shared reference"
     ,(prog '((defn add () ((pl (ref (pool int)))) unit (seq (insert (* pl) 1) unit)))
            '(let ([pl (pool-new int)]) (call add () (ref pl)))))

    ;; ================================================== generics
    (accept "a generic function moves its argument through"
     ,(prog '((defn id (T) ((x T)) T x))
            '(let ([b (call id ((box int)) (box 3))]) (* b))))
    (accept "a generic container of owners"
     ,(prog '((defn wrap (T) ((x T)) (Wrap T) (new (Wrap T) x 0))
              (defn inside (T) ((w (ref (Wrap T)))) (ref T) (ref (: (* w) v))))
            '(let ([w (call wrap ((box int)) (box 3))])
               (let ([r (call inside ((box int)) (ref w))]) (* (* r))))))
    (reject "a value of a type parameter is used twice"
     ,(prog '((defn twice (T) ((x T)) (Wrap T) (seq (new (Wrap T) x 0) (new (Wrap T) x 1))))
            '(let ([w (call twice ((box int)) (box 3))]) 0)))
    (reject "a type parameter cannot be a reference"
     ,(prog '((defn id (T) ((x T)) T x))
            '(let ([a 1]) (let ([r (call id ((ref int)) (ref a))]) (* r)))))
    (reject "a type parameter cannot be a view"
     ,(prog '((defn id (T) ((x T)) T x))
            '(let ([a 1]) (let ([v (call id ((view Peek)) (new (view Peek) (ref a) 0))]) 0))))
    (reject "a type that is not declared"
     ,(prog '() '(let ([w (new (Nope) 1)]) 0)))

    ;; ================================================== loops
    (accept "a loop that borrows on each turn"
     ,(prog '((defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1))))
            '(let ([a (box 0)])
               (let ([i 3])
                 (seq (while i (seq (call bump () (mut (* a))) (set! i (+ i -1))))
                      (* a))))))
    (accept "a break leaves the loop and drops what the turn made"
     ,(prog '() '(let ([i 3])
                   (seq (while i (let ([b (box i)]) (seq (break) (set! i (+ i -1)))))
                        i))))
    (accept "an owner made and moved inside one turn"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([i 2])
               (seq (while i (let ([b (box i)]) (seq (call eat () b) (set! i (+ i -1)))))
                    i))))
    (reject "an outer owner is moved inside a loop"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)])
               (let ([i 2])
                 (seq (while i (seq (call eat () a) (set! i (+ i -1)))) 0)))))
    (reject "a break outside a loop"
     ,(prog '() '(seq (break) 0)))
    (reject "a break in a function called from a loop"
     ,(prog '((defn out () () unit (break)))
            '(let ([i 1]) (seq (while i (seq (call out ()) (set! i 0))) 0))))

    ;; ================================================== globals
    (accept "a global is read and written inside a with"
     ,(prog '() '(seq (with mut g1 x (set! (* (* x)) 5))
                      (with ref g1 x (* (* x))))))
    (accept "a function enters the global it needs"
     ,(prog '((defn bump () () unit (with mut g1 x (set! (* (* x)) (+ (* (* x)) 1)))))
            '(seq (call bump ()) (seq (call bump ()) (with ref g1 x (* (* x)))))))
    (accept "two shared entries at once"
     ,(prog '() '(with ref g1 x (with ref g1 y (+ (* (* x)) (* (* y)))))))
    (accept-panic "a global entered exclusively while it is already lent"
     ,(prog '((defn renew () () unit (with mut g1 y (set! (* y) (box 2)))))
            '(with ref g1 x
               (let ([r (ref (* (* x)))])
                 (seq (call renew ()) (* r))))))
    (reject "a reference to a global leaves its with"
     ,(prog '() '(let ([r (with ref g1 x (ref (* (* x))))]) (* r))))
    (reject "a reference derived from a global's reference leaves its with"
     ,(prog '((defn inner () ((r (ref (box int)))) (ref int) (ref (* (* r)))))
            '(let ([r (with ref g1 x (call inner () x))]) (* r))))
    (reject "a write through a shared entry"
     ,(prog '() '(with ref g1 x (seq (set! (* x) (box 1)) 0))))
    (reject "a global that is not declared"
     ,(prog '() '(with ref nope x 0)))

    ;; ================================================== threads
    (accept "two calls at once on two different places"
     ,(prog '((defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1))))
            '(let ([a 0]) (let ([b 0])
                            (seq (par (call bump () (mut a)) (call bump () (mut b)))
                                 (+ a b))))))
    (accept "two calls at once reading one place"
     ,(prog '((defn get () ((r (ref int))) int (* r)))
            '(let ([a 4]) (seq (par (call get () (ref a)) (call get () (ref a))) a))))
    (accept "two calls at once on two fields of one struct"
     ,(prog '((defn renew () ((r (mut (box int)))) unit (set! (* r) (box 9))))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (par (call renew () (mut (: p a))) (call renew () (mut (: p b))))
                    (+ (* (: p a)) (* (: p b)))))))
    (accept "each side of a par is given an owner"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(seq (par (call eat () (box 1)) (call eat () (box 2))) 0)))
    (accept "two calls at once that each enter a global"
     ,(prog '((defn bump () () unit (with mut g1 x (set! (* (* x)) (+ (* (* x)) 1)))))
            '(seq (par (call bump ()) (call bump ())) (with ref g1 x (* (* x))))))
    (reject "two calls at once writing one place"
     ,(prog '((defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1))))
            '(let ([a 0]) (seq (par (call bump () (mut a)) (call bump () (mut a))) a))))
    (reject "one call writes what the other reads"
     ,(prog '((defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1)))
              (defn get () ((r (ref int))) int (* r)))
            '(let ([a 0]) (seq (par (call bump () (mut a)) (call get () (ref a))) a))))
    (reject "one call is given the owner the other borrows"
     ,(prog '((defn eat () ((b (box int))) int (* b))
              (defn get () ((r (ref int))) int (* r)))
            '(let ([a (box 1)]) (seq (par (call get () (ref (* a))) (call eat () a)) 0))))

    ;; ================================================== threads
    (accept "a thread is given an owner, and joined for its result"
     ,(prog '((defn eat () ((b (box int))) int (+ (* b) 1)))
            '(let ([t (spawn (call eat () (box 1)))]) (+ (join t) 1))))
    (accept "a task that is dropped waits for its thread"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(seq (spawn (call eat () (box 1))) 0)))
    (accept "a thread returns an owner it made"
     ,(prog '((defn make () ((n int)) (box int) (box (+ n 1))))
            '(let ([t (spawn (call make () 1))]) (let ([b (join t)]) (* b)))))
    (accept "a thread and its parent each enter a global"
     ,(prog '((defn bump () () unit (with mut g1 x (set! (* (* x)) (+ (* (* x)) 1)))))
            '(let ([t (spawn (call bump ()))])
               (seq (with mut g1 x (set! (* (* x)) 5)) (seq (join t) 0)))))
    (accept "a task is an owner: it can be handed on and joined elsewhere"
     ,(prog '((defn eat () ((b (box int))) int (* b))
              (defn wait () ((t (task int))) int (join t)))
            '(call wait () (spawn (call eat () (box 3))))))
    (reject "a thread is given a reference"
     ,(prog '((defn get () ((r (ref int))) int (* r)))
            '(let ([a 0]) (let ([t (spawn (call get () (ref a)))]) (seq (set! a 1) (join t))))))
    (reject "a thread is given an exclusive reference"
     ,(prog '((defn bump () ((r (mut int))) unit (set! (* r) (+ (* r) 1))))
            '(let ([a 0]) (seq (spawn (call bump () (mut a))) a))))
    (reject "a thread is given a view"
     ,(prog '((defn peek () ((v (view Peek))) int (* (: v s))))
            '(let ([a 0]) (seq (spawn (call peek () (new (view Peek) (ref a) 1))) a))))
    (reject "a task is joined twice"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([t (spawn (call eat () (box 1)))]) (+ (join t) (join t)))))

    ;; ================================================== raw memory
    (accept "a raw pointer is plain data in safe code"
     ,(prog '() '(let ([a 1]) (let ([q (addr a)]) (let ([b (box q)]) a)))))
    (accept-unsafe "a raw pointer is followed inside unsafe"
     ,(prog '() '(let ([a 1]) (let ([q (addr a)]) (seq (unsafe (store q 5)) (unsafe (load q)))))))
    (accept-unsafe "raw allocation, freed by hand"
     ,(prog '() '(unsafe (let ([q (alloc 3)]) (let ([n (load q)]) (seq (free q) n))))))
    (accept-unsafe "unsafe can go wrong, and that is what it means"
     ,(prog '() '(let ([q (let ([a 1]) (addr a))]) (unsafe (load q)))))
    (reject "a raw pointer is followed outside unsafe"
     ,(prog '() '(let ([a 1]) (let ([q (addr a)]) (load q)))))
    (reject "raw allocation outside unsafe"
     ,(prog '() '(let ([q (alloc 3)]) 0)))
    (reject "unsafe does not switch the other rules off"
     ,(prog '() '(unsafe (let ([a (box 1)]) (let ([b a]) (* a))))))
    (reject "unsafe does not reach into a called function"
     ,(prog '((defn peek () ((q (ptr int))) int (load q)))
            '(let ([a 1]) (unsafe (call peek () (addr a))))))))

(define (run-cases)
  (define bad 0)
  (define caught 0)
  (for ([c cases])
    (match-define (list want name prog) c)
    (define got (if (check-program prog) 'accept 'reject))
    ;; a rejected program may not mean anything at all (an undeclared name)
    (define ran (if (eq? got 'reject)
                    (with-handlers ([exn:fail? (λ (_) '(meaningless))]) (run prog))
                    (run prog)))
    (define wrong
      (match* (want got ran)
        [('reject 'reject _) #f]
        [('reject 'accept _) "the rules accepted it"]
        [(_ 'reject _) "the rules rejected it"]
        [('accept _ (list 'ok _ 0)) #f]
        [('accept _ (list 'ok _ n)) (format "accepted, and it leaked ~a" n)]
        [('accept-panic _ (list 'panic _)) #f]
        [('accept-unsafe _ _) #f]
        [(_ _ _) (format "accepted, and it ran: ~a" ran)]))
    (when (and (eq? want 'reject) (eq? (car ran) 'stuck)) (set! caught (add1 caught)))
    (when wrong
      (set! bad (add1 bad))
      (printf "FAIL ~a: ~a\n" name wrong)))
  (printf "cases: ~a, failed: ~a; rejected programs that go wrong when run anyway: ~a of ~a\n"
          (length cases) bad caught (count (λ (c) (eq? (car c) 'reject)) cases))
  (zero? bad))

(module+ main (exit (if (run-cases) 0 1)))
