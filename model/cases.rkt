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
    (struct Holds () ((a arena)))
    (struct Tx () ((n int)))
    (linear Tx)
    (struct Deal () ((amt (box int)) (fee (box int))))
    (linear Deal)
    (view InArena ((r (ref arena))))
    (view Node ((next (abox int)) (n int)))
    (struct Pt () ((m int) (n int)))
    (struct Wrap (T) ((v T) (w int)))
    (sum Opt (T) ((None unit) (Some T)))
    (view Two ((l (ref (box int))) (r (mut int))))
    (view Peek ((s (ref int)) (i int)))
    ;; a lock: its drop reads what it holds, as a subscript's code after its yield does
    (view Lock ((r (mut (box int)))) unlock)
    (defn unlock () ((g (view Lock))) unit (seq (* (* (: g r))) unit))
    ;; a view that holds a view
    (view Nest ((in (view Peek)) (k (ref int))))
    ;; a view that is shared, whose drop reads what it holds
    (view Watch ((r (ref (box int)))) unwatch)
    (defn unwatch () ((w (view Watch))) unit (seq (* (* (: w r))) unit))
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
    (accept "an owner is moved out of a box by naming it; the box is freed empty"
     ,(prog '() '(let ([a (box (box 1))]) (let ([b (* a)]) (* b)))))
    (reject "what was moved out of a box is not there to read"
     ,(prog '() '(let ([a (box (box 1))]) (let ([b (* a)]) (* (* a))))))
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
    (accept "an owner is moved out of a field; the rest is dropped with the struct"
     ,(prog '() '(let ([p (new (Pair) (box 1) (box 2))]) (let ([b (: p a)]) (+ (* b) (* (: p b)))))))

    ;; ================================================== parts moved and given back
    (accept "a field moved out and given back, then the whole is used"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (call eat () (: p a)) (seq (set! (: p a) (box 3)) (let ([q p]) (* (: q a))))))))
    (reject "a struct with a field moved out is not moved whole"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (call eat () (: p a)) (let ([q p]) (* (: q a)))))))
    (reject "a struct with a field moved out is not lent whole"
     ,(prog '((defn eat () ((b (box int))) int (* b))
              (defn first () ((p (ref (Pair)))) int (* (: (* p) a))))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (call eat () (: p a)) (call first () (ref p))))))
    (accept "the other field of a struct with a field moved out is used"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (+ (call eat () (: p a)) (* (: p b))))))
    (reject "a field of what was moved out cannot be assigned"
     ,(prog '((defn eat () ((p (Wrap (Pair)))) int (* (: (: p v) b))))
            '(let ([w (new (Wrap (Pair)) (new (Pair) (box 1) (box 2)) 0)])
               (seq (call eat () w) (seq (set! (: (: w v) a) (box 5)) unit)))))
    (accept "a part moved out in one branch is given back after it"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (if0 0 (seq (call eat () (: p a)) unit) unit)
                    (seq (set! (: p a) (box 4)) (* (: p a)))))))
    (reject "a part moved out in one branch is not there after it"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (if0 0 (seq (call eat () (: p a)) unit) unit) (* (: p a))))))
    (accept "what an exclusive parameter refers to is moved out and put back"
     ,(prog '((defn eat () ((b (box int))) int (* b))
              (defn swap-in () ((m (mut (Pair)))) int
                (let ([old (: (* m) a)]) (seq (set! (: (* m) a) (box 7)) (call eat () old)))))
            '(let ([p (new (Pair) (box 1) (box 2))]) (seq (call swap-in () (mut p)) (* (: p a))))))
    (reject "what an exclusive parameter refers to is left with a part moved out"
     ,(prog '((defn eat () ((b (box int))) int (* b))
              (defn steal () ((m (mut (Pair)))) int (call eat () (: (* m) a))))
            '(let ([p (new (Pair) (box 1) (box 2))]) (seq (call steal () (mut p)) (* (: p a))))))
    (accept "an element of a pool is given a new value"
     ,(prog '() '(let ([p (pool-new (box int))])
                   (let ([h (insert p (box 1))]) (seq (set! (at p h) (box 2)) (* (at p h)))))))
    (reject "an owner is not moved out through a reference that is no parameter: nothing gives it back"
     ,(prog '() '(let ([i 2]) (while i (seq (with mut g1 v (seq (* v) unit)) (set! i (+ i -1)))))))
    (accept "a variable made with nothing in it is filled through an out parameter"
     ,(prog '((defn fill () ((r (out (box int)))) unit (set! (* r) (box 4))))
            '(let ([x (uninit (box int))]) (seq (call fill () (out x)) (* x)))))
    (reject "a variable with nothing in it is not read"
     ,(prog '() '(let ([x (uninit (box int))]) (* x))))
    (reject "an out parameter that is not filled"
     ,(prog '((defn skip () ((r (out (box int)))) unit unit))
            '(let ([x (uninit (box int))]) (seq (call skip () (out x)) (* x)))))
    (reject "an out parameter is not read before it is filled"
     ,(prog '((defn peek () ((r (out (box int)))) unit (seq (* (* r)) (set! (* r) (box 1)))))
            '(let ([x (uninit (box int))]) (seq (call peek () (out x)) (* x)))))
    (reject "a place that holds a value is not passed as an out parameter"
     ,(prog '((defn fill () ((r (out (box int)))) unit (set! (* r) (box 4))))
            '(let ([x (box 1)]) (seq (call fill () (out x)) (* x)))))
    (accept "a part moved out is filled again through an out parameter"
     ,(prog '((defn fill () ((r (out (box int)))) unit (set! (* r) (box 4)))
              (defn eat () ((b (box int))) int (* b)))
            '(let ([p (new (Pair) (box 1) (box 2))])
               (seq (call eat () (: p a)) (seq (call fill () (out (: p a))) (* (: p a)))))))

    ;; ================================================== break and return
    (accept "a loop moves a variable and then breaks; after it, the variable is gone"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (seq (while 1 (seq (call eat () a) (break))) 5))))
    (reject "what a loop moved before a break is not there after the loop"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (seq (while 1 (seq (call eat () a) (break))) (* a)))))
    (accept "a loop moves a variable before a break and gives it a value again"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (seq (while 1 (seq (call eat () a) (break))) (seq (set! a (box 2)) (* a))))))
    (reject "a loop that moves without breaking moves again on its next turn"
     ,(prog '((defn eat () ((b (box int))) int (* b)))
            '(let ([a (box 1)]) (let ([i 2]) (while i (seq (call eat () a) (set! i (+ i -1))))))))
    (accept "an early return"
     ,(prog '((defn pick () ((r (ref (box int))) (c int)) (ref int)
                (seq (if0 c (return (ref (* (* r))) unit) unit) (ref (* (* r))))))
            '(let ([a (box 3)]) (let ([r (call pick () (ref a) 0)]) (* r)))))
    (reject "an early return of a reference to a local"
     ,(prog '((defn bad () ((c int)) (ref int)
                (let ([x 3]) (seq (if0 c (return (ref x) unit) unit) (call bad () 1)))))
            '(let ([r (call bad () 0)]) (* r))))
    (reject "an early return leaves what an exclusive parameter refers to with a part moved out"
     ,(prog '((defn eat () ((b (box int))) int (* b))
              (defn steal () ((m (mut (Pair))) (c int)) int
                (let ([n (call eat () (: (* m) a))])
                  (seq (if0 c (return n unit) unit) (seq (set! (: (* m) a) (box 1)) n)))))
            '(let ([p (new (Pair) (box 1) (box 2))]) (seq (call steal () (mut p) 0) (* (: p a))))))
    (reject "an early return of a reference to a global"
     ,(prog '((defn leak () () (ref (box int)) (with ref g1 x (return x (ref (box int))))))
            '(let ([r (call leak ())]) (* (* r)))))

    ;; ================================================== closures
    (accept "a closure that borrows: called twice"
     ,(prog '()
            '(let ([n 1])
               (let ([f (lam ([r (mut int) (mut n)]) () unit (set! (* r) (+ (* r) 1)))])
                 (seq (apply f) (seq (apply f) n))))))
    (reject "what a closure captured exclusively is not read while it is used"
     ,(prog '()
            '(let ([n 1])
               (let ([f (lam ([r (mut int) (mut n)]) () unit (set! (* r) (+ (* r) 1)))])
                 (seq (apply f) (seq n (apply f)))))))
    (reject "a closure's capture cannot be freed under it"
     ,(prog '()
            '(let ([b (box 1)])
               (let ([f (lam ([r (ref int) (ref (* b))]) () int (* r))])
                 (seq (set! b (box 2)) (apply f))))))
    (reject "a closure cannot leave the scope of what it borrows"
     ,(prog '()
            '(let ([f (let ([x 3]) (lam ([r (ref int) (ref x)]) () int (* r)))]) (apply f))))
    (accept "a closure passed to a function that calls it"
     ,(prog '((defn twice () ((f (fnb mut () unit))) unit (seq (apply f) (apply f))))
            '(let ([n 0])
               (seq (call twice () (lam ([r (mut int) (mut n)]) () unit (set! (* r) (+ (* r) 1)))) n))))
    (reject "a closure's argument cannot reach what it captured exclusively"
     ,(prog '()
            '(let ([b (box 1)])
               (let ([f (lam ([m (mut (box int)) (mut b)]) ((r (ref int))) int (seq (set! (* m) (box 2)) (* r)))])
                 (apply f (ref (* b)))))))
    (reject "two results of a closure that captured exclusively are not alive at once"
     ,(prog '()
            '(let ([b (box 1)])
               (let ([f (lam ([m (mut (box int)) (mut b)]) () (mut (box int)) m)])
                 (let ([x (apply f)])
                   (let ([y (mut (* (* x)))])
                     (let ([z (apply f)]) (seq (set! (* z) (box 5)) (* y)))))))))
    (accept "a closure that owns what it captured, kept and called later"
     ,(prog '((defn run () ((f (fno () int))) int (+ (apply f) (apply f))))
            '(let ([f (lamo ([c (box int) (box 5)]) () int (seq (set! c (box (+ (* c) 1))) (* c)))])
               (call run () f))))
    (reject "a closure that owns what it captured cannot move it away"
     ,(prog '((defn eat () ((b (box int))) int (* b))
              (defn run () ((f (fno () int))) int (+ (apply f) (apply f))))
            '(call run () (lamo ([c (box int) (box 5)]) () int (call eat () c)))))
    (reject "a closure that owns what it captured cannot capture a reference"
     ,(prog '((defn run () ((f (fno () int))) int (apply f)))
            '(let ([f (let ([x 4]) (lamo ([r (ref int) (ref x)]) () int (* r)))]) (call run () f))))
    (accept "a closure that owns what it captured, run on a thread"
     ,(prog '() '(join (spawn-fn (lamo ([c (box int) (box 5)]) () int (* c))))))

    ;; ================================================== views that run code when dropped
    (accept "a lock whose drop reads what it holds"
     ,(prog '() '(let ([b (box 1)]) (seq (let ([g (new (view Lock) (mut b))]) unit) (* b)))))
    (reject "what a lock holds is not freed while the lock lives, even after its last use"
     ,(prog '() '(let ([b (box (box 1))])
                   (let ([g (new (view Lock) (mut (* b)))]) (set! b (box (box 2)))))))
    (reject "a reference from the later branch keeps what it refers into lent"
     ,(prog '() '(let ([n 5]) (let ([b (box 1)])
                   (let ([r (if0 1 (ref n) (ref (* b)))]) (seq (set! b (box 2)) (* r)))))))
    (reject "a later argument frees what an earlier one refers into"
     ,(prog '((defn first-of () ((r (ref int)) (n int)) int (* r)))
            '(let ([b (box 1)]) (call first-of () (ref (* b)) (seq (set! b (box 2)) 0)))))

    (reject "a reference into a global does not outlive its with, past a write to the global"
     ,(prog '() '(let ([r (with ref g1 v (ref (* (* v))))])
                   (seq (with mut g1 w (set! (* w) (box 5))) (* r)))))

    ;; ================================================== linear values
    (accept "a linear value is destroyed"
     ,(prog '() '(let ([t (new (Tx) 1)]) (seq (destroy t) 0))))
    (accept "a linear value is given to a function that destroys it"
     ,(prog '((defn finish () ((t (Tx))) int (seq (destroy t) 1)))
            '(let ([t (new (Tx) 1)]) (call finish () t))))
    (accept "a function makes a linear value and its caller destroys it"
     ,(prog '((defn open () () (Tx) (new (Tx) 5)))
            '(let ([t (call open ())]) (seq (destroy t) 0))))
    (accept "a linear value is destroyed on both ways of a branch"
     ,(prog '() '(let ([t (new (Tx) 1)]) (if0 0 (seq (destroy t) 1) (seq (destroy t) 2)))))
    (accept "destroying a linear struct drops what it holds"
     ,(prog '() '(let ([d (new (Deal) (box 3) (box 4))]) (seq (destroy d) 0))))
    (accept "a linear struct is taken apart, every field moved out of it"
     ,(prog '() '(let ([d (new (Deal) (box 3) (box 4))])
                   (let ([a (: d amt)]) (let ([f (: d fee)]) (+ (* a) (* f)))))))
    (accept "a type parameter passes a linear value through"
     ,(prog '((defn keep (T) ((x T)) T x))
            '(let ([t (call keep ((Tx)) (new (Tx) 1))]) (seq (destroy t) 0))))
    (accept "a linear value boxed, unboxed and destroyed"
     ,(prog '() '(let ([b (box (new (Tx) 1))]) (let ([t (unbox b)]) (seq (destroy t) 0)))))
    (accept "a linear value made in a loop is destroyed in it"
     ,(prog '() '(let ([i 0]) (seq (while (+ i 0) (let ([t (new (Tx) 1)]) (destroy t))) 0))))
    (reject "a linear value is not dropped when its scope ends"
     ,(prog '() '(let ([t (new (Tx) 1)]) 0)))
    (reject "a linear value is not thrown away"
     ,(prog '() '(seq (new (Tx) 1) 0)))
    (reject "a linear value is not overwritten"
     ,(prog '() '(let ([t (new (Tx) 1)]) (seq (set! t (new (Tx) 2)) (seq (destroy t) 0)))))
    (reject "a linear value destroyed on one way only is not assigned over"
     ,(prog '() '(let ([t (new (Tx) 1)])
                   (seq (if0 0 (destroy t) unit) (seq (set! t (new (Tx) 2)) (seq (destroy t) 0))))))
    (reject "a linear value is not destroyed on one way only"
     ,(prog '() '(let ([t (new (Tx) 1)]) (if0 0 (seq (destroy t) 1) 2))))
    (reject "a linear value is not given to a type parameter its function may drop"
     ,(prog '((defn toss (T) ((x T)) int 0) (droppable toss (T)))
            '(call toss ((Tx)) (new (Tx) 1))))
    (accept "a type parameter its function may drop takes what is not linear"
     ,(prog '((defn toss (T) ((x T)) int 0) (droppable toss (T)))
            '(call toss ((box int)) (box 1))))
    (reject "a function does not drop a value of a type parameter it does not say it may drop"
     ,(prog '((defn toss (T) ((x T)) int 0))
            '(let ([t (new (Tx) 1)]) (seq (destroy t) 0))))
    (reject "a linear parameter is not dropped"
     ,(prog '((defn lose () ((t (Tx))) int 0))
            '(call lose () (new (Tx) 1))))
    (reject "a linear value does not leave its scope by a break"
     ,(prog '() '(seq (while 1 (let ([t (new (Tx) 1)]) (break))) 0)))
    (reject "a linear value is not held by an owning closure"
     ,(prog '() '(let ([t (new (Tx) 1)]) (let ([f (lamo ([c (Tx) t]) () int 0)]) 0))))
    (reject "a linear value is moved, never copied"
     ,(prog '() '(let ([t (new (Tx) 1)]) (let ([u t]) (seq (destroy t) (seq (destroy u) 0))))))
    (reject "a linear struct taken apart in part still holds the rest"
     ,(prog '() '(let ([d (new (Deal) (box 3) (box 4))]) (let ([a (: d amt)]) (* a)))))
    (reject "a task whose result is linear is joined, not dropped"
     ,(prog '((defn open () () (Tx) (new (Tx) 5)))
            '(let ([k (spawn (call open ()))]) 0)))
    (reject "two calls at once give nothing back: neither returns a linear value"
     ,(prog '((defn open () () (Tx) (new (Tx) 5)) (defn zero () () int 0))
            '(seq (par (call open ()) (call zero ())) 0)))
    (reject "a return does not drop a linear local"
     ,(prog '((defn early () () int (let ([t (new (Tx) 1)]) (seq (return 0 unit) (seq (destroy t) 1)))))
            '(call early ())))
    (accept "a linear local destroyed before a return"
     ,(prog '((defn early () () int (let ([t (new (Tx) 1)]) (seq (destroy t) (seq (return 0 unit) 1)))))
            '(call early ())))
    (reject "a linear value is not in a box that is dropped"
     ,(prog '() '(let ([b (box (new (Tx) 1))]) 0)))

    ;; ================================================== arenas
    (accept "two boxes in one arena, and the arena reset once they are gone"
     ,(prog '() '(let ([a (arena-new)])
                   (seq (let ([x (abox a 1)]) (let ([y (abox a 2)]) (+ (* x) (* y))))
                        (seq (reset! a) 0)))))
    (accept "a box in an arena is changed through"
     ,(prog '() '(let ([a (arena-new)]) (let ([x (abox a 1)]) (seq (set! (* x) 5) (* x))))))
    (accept "what a box in an arena holds is moved out, and outlives a reset"
     ,(prog '() '(let ([a (arena-new)])
                   (let ([v (let ([x (abox a (new (Pt) 3 4))]) (unbox x))])
                     (seq (reset! a) (: v m))))))
    (reject "an owner is not put in an arena, which drops nothing it holds"
     ,(prog '() '(let ([a (arena-new)]) (let ([x (abox a (box 1))]) (* (* x))))))
    (reject "a view whose drop runs code is not put in an arena"
     ,(prog '() '(let ([n (box 1)]) (let ([a (arena-new)])
                   (let ([x (abox a (new (view Lock) (mut n)))]) 0)))))
    (accept "a box in an arena holds a view of another box in it"
     ,(prog '() '(let ([a (arena-new)])
                   (let ([leaf (abox a 7)])
                     (let ([top (abox a (new (view Node) leaf 1))])
                       (+ (* (: (* top) next)) (: (* top) n)))))))
    (reject "an arena is not reset while a box in it is used"
     ,(prog '() '(let ([a (arena-new)]) (let ([x (abox a 1)]) (seq (reset! a) (* x))))))
    (reject "a box in an arena does not outlive the arena"
     ,(prog '() '(let ([x (let ([a (arena-new)]) (abox a 1))]) (* x))))
    (reject "an arena is not reset while a box in it is still to be dropped"
     ,(prog '() '(let ([a (arena-new)]) (let ([x (abox a (box 1))]) (seq (* (* x)) (seq (reset! a) 0))))))
    (reject "a box in an arena is moved, not copied"
     ,(prog '() '(let ([a (arena-new)]) (let ([x (abox a (box 1))]) (let ([y x]) (* (* x)))))))
    (reject "two calls at once do not both allocate in one arena"
     ,(prog '((defn put () ((r (ref arena))) int (let ([x (abox (* r) 1)]) (* x))))
            '(let ([a (arena-new)]) (seq (par (call put () (ref a)) (call put () (ref a))) 0))))
    (accept "two calls at once allocate in two arenas"
     ,(prog '((defn put () ((r (ref arena))) int (let ([x (abox (* r) 1)]) (* x))))
            '(let ([a (arena-new)]) (let ([b (arena-new)])
               (seq (par (call put () (ref a)) (call put () (ref b))) 0)))))
    (reject "an arena inside a struct is not lent to both of two calls at once"
     ,(prog '((defn put () ((r (ref (Holds)))) int (let ([x (abox (: (* r) a) 1)]) (* x))))
            '(let ([h (new (Holds) (arena-new))]) (seq (par (call put () (ref h)) (call put () (ref h))) 0))))
    (reject "a view of an arena is not lent to one of two calls at once while the other has the arena"
     ,(prog '((defn put () ((r (ref arena))) int (let ([x (abox (* r) 1)]) (* x)))
              (defn put-via () ((v (ref (view InArena)))) int (let ([x (abox (* (: (* v) r)) 1)]) (* x))))
            '(let ([a (arena-new)])
               (let ([va (new (view InArena) (ref a))])
                 (seq (par (call put-via () (ref va)) (call put () (ref a))) 0)))))
    (accept "a box in an arena holds a view"
     ,(prog '() '(let ([n 4]) (let ([a (arena-new)])
                   (let ([x (abox a (new (view Peek) (ref n) 1))]) (* (: (* x) s)))))))
    (reject "what a view in an arena borrowed is not changed while the box lives"
     ,(prog '() '(let ([n 4]) (let ([a (arena-new)])
                   (let ([x (abox a (new (view Peek) (ref n) 1))]) (seq (set! n 5) (* (: (* x) s))))))))
    (reject "a box in an arena holding a view does not outlive what the view borrowed"
     ,(prog '() '(let ([a (arena-new)])
                   (let ([x (let ([n (box 4)]) (abox a (new (view Peek) (ref (* n)) 1)))]) (* (: (* x) s))))))
    (reject "a view moved out of a box in an arena keeps what it borrowed lent"
     ,(prog '() '(let ([n (box 4)]) (let ([a (arena-new)])
                   (let ([w (unbox (abox a (new (view Peek) (ref (* n)) 1)))])
                     (seq (set! n (box 5)) (* (: w s))))))))
    (reject "an arena is not moved while a box in it lives"
     ,(prog '() '(let ([a (arena-new)]) (let ([x (abox a 1)]) (let ([b a]) (* x))))))

    ;; ================================================== references to views
    (accept "a view lent exclusively where it lies, and changed through"
     ,(prog '((defn relock () ((k (mut (view Lock)))) unit (set! (* (: (* k) r)) (box 5))))
            '(let ([a (box 1)])
               (seq (let ([k (new (view Lock) (mut a))]) (call relock () (mut k))) (* a)))))
    (accept "two views a view holds, lent exclusively at once to the two sides of a par"
     ,(prog '((view Locks ((l (view Lock)) (r (view Lock))))
              (defn relock () ((k (mut (view Lock)))) unit (set! (* (: (* k) r)) (box 5))))
            '(let ([a (box 1)])
               (let ([b (box 2)])
                 (seq (let ([h (new (view Locks) (new (view Lock) (mut a)) (new (view Lock) (mut b)))])
                        (par (call relock () (mut (: h l))) (call relock () (mut (: h r)))))
                      (+ (* a) (* b)))))))
    (reject "one view a view holds, lent exclusively to both sides of a par"
     ,(prog '((view Locks ((l (view Lock)) (r (view Lock))))
              (defn relock () ((k (mut (view Lock)))) unit (set! (* (: (* k) r)) (box 5))))
            '(let ([a (box 1)])
               (let ([b (box 2)])
                 (let ([h (new (view Locks) (new (view Lock) (mut a)) (new (view Lock) (mut b)))])
                   (par (call relock () (mut (: h l))) (call relock () (mut (: h l)))))))))
    (reject "what a view borrowed is not used while a reference to the view is"
     ,(prog '((defn relock () ((k (mut (view Lock)))) unit (set! (* (: (* k) r)) (box 5))))
            '(let ([a (box 1)])
               (let ([k (new (view Lock) (mut a))])
                 (let ([r (mut k)])
                   (seq (set! a (box 2)) (call relock () r)))))))

    ;; ================================================== two-phase borrows
    (accept "a later argument reads what an earlier one lends exclusively"
     ,(prog '((defn put () ((m (mut (box int))) (n int)) unit (set! (* m) (box n))))
            '(let ([x (box 1)]) (seq (call put () (mut x) (+ (* x) 1)) (* x)))))
    (reject "a later argument borrows what an earlier one lends exclusively"
     ,(prog '((defn alias () ((m (mut (box int))) (r (ref int))) int (seq (set! (* m) (box 5)) (* r))))
            '(let ([x (box 1)]) (call alias () (mut x) (ref (* x))))))
    (reject "a later argument writes what an earlier one lends exclusively"
     ,(prog '((defn put () ((m (mut (box int))) (n int)) unit (set! (* m) (box n))))
            '(let ([x (box 1)]) (seq (call put () (mut x) (seq (set! x (box 2)) 1)) (* x)))))

    ;; ================================================== what a result borrows from
    (accept "a result its borrows says comes from one argument leaves the other free"
     ,(prog '((defn first-of () ((a (ref int)) (b (ref int))) (ref int) a)
              (borrows first-of (a)))
            '(let ([x (box 1)])
               (let ([y (box 2)])
                 (let ([r (call first-of () (ref (* x)) (ref (* y)))])
                   (seq (set! y (box 3)) (* r)))))))
    (reject "without a borrows, the result borrows from every reference argument"
     ,(prog '((defn first-of () ((a (ref int)) (b (ref int))) (ref int) a))
            '(let ([x (box 1)])
               (let ([y (box 2)])
                 (let ([r (call first-of () (ref (* x)) (ref (* y)))])
                   (seq (set! y (box 3)) (* r)))))))
    (reject "a result keeps the argument its borrows names lent"
     ,(prog '((defn first-of () ((a (ref int)) (b (ref int))) (ref int) a)
              (borrows first-of (a)))
            '(let ([x (box 1)])
               (let ([y (box 2)])
                 (let ([r (call first-of () (ref (* x)) (ref (* y)))])
                   (seq (set! x (box 3)) (* r)))))))
    (reject "a function returns what a parameter its borrows leaves out was lent"
     ,(prog '((defn second-of () ((a (ref int)) (b (ref int))) (ref int) b)
              (borrows second-of (a)))
            '(let ([x (box 1)])
               (let ([y (box 2)])
                 (let ([r (call second-of () (ref (* x)) (ref (* y)))])
                   (seq (set! y (box 3)) (* r)))))))
    (reject "a function returns early what a parameter its borrows leaves out was lent"
     ,(prog '((defn second-of () ((a (ref int)) (b (ref int))) (ref int)
                (seq (return b (ref int)) a))
              (borrows second-of (a)))
            '(let ([x (box 1)])
               (let ([y (box 2)])
                 (let ([r (call second-of () (ref (* x)) (ref (* y)))])
                   (seq (set! y (box 3)) (* r)))))))
    (reject "a borrows names a parameter that takes no reference"
     ,(prog '((defn pick () ((a (ref int)) (n int)) (ref int) a)
              (borrows pick (n)))
            '(let ([x (box 1)]) (* (* (call pick () (ref (* x)) 0))))))
    (accept "a borrows of an exclusive reference keeps it lent exclusively, the other argument free"
     ,(prog '((defn grab () ((a (mut int)) (b (ref int))) (mut int) a)
              (borrows grab (a)))
            '(let ([x (box 1)])
               (let ([y (box 2)])
                 (let ([r (call grab () (mut (* x)) (ref (* y)))])
                   (seq (set! y (box 3)) (seq (set! (* r) 4) (* x))))))))

    (accept "a shared view whose drop reads what it holds"
     ,(prog '() '(let ([b (box (box 1))])
                   (seq (let ([w (new (view Watch) (ref (* b)))]) unit) (* (* b))))))
    (reject "what a shared view with a drop holds is not freed while the view lives, even after its last use"
     ,(prog '() '(let ([b (box (box 1))])
                   (let ([w (new (view Watch) (ref (* b)))]) (set! b (box (box 2)))))))
    (accept "a view that holds a view"
     ,(prog '() '(let ([a 1]) (let ([b 2])
                   (let ([n (new (view Nest) (new (view Peek) (ref a) 0) (ref b))])
                     (+ (* (: (: n in) s)) (* (: n k))))))))
    (reject "a view that holds a view keeps the inner one's loans"
     ,(prog '() '(let ([a (box 1)]) (let ([b 2])
                   (let ([n (new (view Nest) (new (view Peek) (ref (* a)) 0) (ref b))])
                     (seq (set! a (box 3)) (* (: (: n in) s))))))))

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
