# safe-coil

A memory-safe mode for Coil, as a metaprogram that restricts the language.

- `src/check.coil` is the checker. A program compiled with `--use safe.check` (or
  that imports `safe.check`, or lists it under `[metaprograms] use` in its
  `Coil.toml`) has every function of its own modules checked.
- `src/` also holds the small library safe code is written with. The checker
  checks the library too: what it does with raw memory sits inside `(unsafe …)`.
- `model/` is where the rules were worked out first, in PLT Redex, and the
  checker is tested against it.

```coil
(module example.main)
(import "safe.box" :use [Box])
(defstruct Pt [(x i64) (y i64)])
(defn bump [(p (mut Pt))] (-> void) (set! (.x p) (+ (.x p) 1)))
(defn main [] (-> i64)
  (let [(mut b) (Box::new (Pt :x 1 :y 2))
        r (Box::get b)]
    (bump (mut (Box::get-mut (mut b))))     ; refused: b is lent to r
    (.x r)))
```

```
$ coil check example.coil --use safe.check
error: safe: this is lent exclusively while it is lent
```

## What the checker enforces

The compiler already refuses a use of a moved owner, a write through a shared
reference, and a reference stored in a struct, a sum or a container. The checker
adds the rest of the model:

- **Loans.** A reference holds a loan on the place it came from for as long as
  the name bound to it is still used: until its last use, not the end of its
  scope. A name used in a loop counts as used for the whole loop. A place is
  not read while lent exclusively, and not written, moved, or lent exclusively
  while lent at all. Two fields of one struct are separate places. Two things
  keep a loan past its holder's last use: a reference borrowed through the
  holder that is itself still used, and a view that is dropped (a held lock, an
  exclusive slice), which keeps its loans until its scope ends because its
  drop may use what it borrowed.
- **Arguments.** Each argument's loans are alive while the later ones are
  evaluated. One lent exclusively is only reserved meanwhile (two-phase
  borrows): the later arguments may read what it lends, so `(set! (mut v) i (+
  (get v i) 1))` and `(Vec::push! (mut v) (len v))` are fine, and may not change
  or move it; when the call begins, no other argument may still hold a loan on
  it, so `(f (mut p) (borrow p))` is refused. Plain data passed by value is read
  where it lies for the length of the call, so it counts as lent shared.
- **No escape.** A reference cannot leave the scope of the local it refers to: not
  as the value of a `let`, a `block`, a `break` or a function, and not as a
  reference to a temporary.
- **Results.** A reference a call returns borrows from every argument the call
  took by reference, unless the function says which with `:safe/borrows`:
  `(defn lookup :safe/borrows "doc" [(doc (ref Json)) (path (ref (Vec Str)))]
  (-> (Maybe Json)) …)` borrows from `doc` alone, so the path can be a temporary.
  The body is held to it: it may give back nothing the other parameters were
  lent. `Map::at` borrows from the map, not the key.
- **Temporaries.** Coil keeps a temporary that owns something until the
  statement it was made in ends, and a `let` bound to a reference keeps the
  temporaries of its initializer for as long as the `let` runs. So
  `(primitive/load (Box::get (Box::new 1)))` reads a live box, and a lock taken
  and read in one expression is held for the read. A reference into such a
  temporary must not leave its statement: it is not a function's result, not
  the value of a `block` or a `break`, and not held by a view that a `let`
  binds, since a `let` bound to anything but a reference ends its
  initializer's temporaries. A temporary of plain data lives as long as the
  function's frame.
- **Match.** A `match` on a name lends the parts of the payload that own something
  to the arm, where they lie. The matched place stays lent to those names while
  they are used, so the variant cannot be replaced under them; an arm whose
  names are not used again may move what it matched, as `(match o (Some [_] o)
  (None [] …))` does. `(match (move x) …)` consumes x instead.
- **Names.** A later use is a use of the same binding: a `let` or an arm that
  binds the name again starts another, and the one outside is no longer used
  inside it. A `let` copies plain data, a number or a struct of plain data, so
  `(let [next (.next (Pool::at p h))] …)` holds no loan on `p`.
- **Views.** A struct marked `(impl View TYPE)` stands for the references it was
  made from, as a held lock or a slice of a list does. A call that returns one
  keeps what it took by reference lent for as long as the view lives. A view is
  a local, an argument or a result: it is not stored in a struct, a variant or
  a place, and not passed for a type parameter, so it reaches no container and
  no other thread. A view made from an exclusive reference gives exclusive
  access, so its type must be one that is moved (one with a `Drop`), never
  copied.
- **Closures.** A closure that borrows (`safe.fn`'s `lambda`) is a view over
  what it captured: it keeps each capture lent, shared or exclusively, until
  its last use, and is moved, never copied. Its body is a function of its own
  whose captures are reference parameters, checked as any function is. A
  closure that owns what it captured (`lambda-own`) holds no reference, so it can
  be stored, returned and sent to another thread.
- **What a view type says.** Only the module that declares a view may say of it:
  `QuietDrop`, its drop uses nothing it borrowed, so its loans end at its last
  use; `SharedView`, it gives only shared access, so it may be copied even when
  made from an exclusive reference (a function taking `(mut c)` may give back a
  `Maybe`, as Rust's `fn get(&mut self) -> Option<&V>` does); `CrossThread`, it
  may be lent to `par`'s other thread. A view that gives exclusive access is
  moved, never copied, and a field of a view that is itself a view is a place of
  its own, lent like any other.
- **Views the program declares.** `defview` and `defsubscript` make views with
  no `unsafe` in the program: the generated code follows the raw pointers, and
  the code the program writes (a subscript's code before and after its yield)
  is checked as functions of its own. A view may hold a view. A view's drop that
  uses nothing it borrowed is marked `QuietDrop` by the module that declares the
  view (and only that module), so its loans end at its last use; any other
  view keeps them until its scope ends.
- **Trait objects.** A `(dyn Trait)` is an exclusive reference to what it was
  made from: made from `(mut place)` (from a raw pointer only inside `unsafe`),
  lent exclusively wherever it is used, never stored or passed for a type
  parameter. A trait's method that takes what it works on as `(ptr Self)` is
  checked as though that were an exclusive reference, with no `unsafe`, so a raw
  pointer is given to one only inside `unsafe`, and its fields are places behind
  that reference. One a call gives back keeps what the call took lent: `(Own::get-mut
  (mut s))` keeps `s`. An owned trait object is `safe.own`'s `(Own (dyn Trait))`.
- **Loads.** `(primitive/load …)` of an owner makes a second owner of the same
  thing, so safe code does not load one: it names a variable to move it, or
  takes it out of a place with `replace!`.
- **Raw fields.** A struct or variant with a field that is itself raw memory is
  built only inside `unsafe`, and such a field is changed only there. So a type
  like `Box` holds the pointer its own code put in it, never one safe code made up.
- **Raw memory.** A raw pointer is plain data anywhere. It is followed only inside
  `(unsafe …)`: a load, a store, a field behind one, a reference made from one, a
  call of an `extern`, a call through a function pointer or a trait object.
- **Library code.** A function of the standard library is called freely unless it
  takes raw memory, which includes slices, arrays and anything holding a pointer
  (so `ArrayList` and `HashMap`). Those calls need `unsafe`. Safe code meets a
  slice only as a string literal, or a parameter given one, which lives as long
  as the program and never changes: it reads one through `size`, `nth` and `(for
  (ref x) s …)`, which check every index (Coil's own `get` does only under
  `--debug-checks`), and prints it. Safe code cannot free one, so none it holds
  goes stale. A method of a trait declared in checked code is checked
  code wherever it is implemented, since Coil's own modules cannot name such a
  trait. The code `print`, `println`, `panic`, `unreachable` and `assert` expand
  to is trusted; raw memory the program made must not be handed to it.
- **Anything else is refused.** A form the rules do not cover (`defer`, a
  destructuring `let`, an array literal, a primitive not listed as safe) is an
  error outside `unsafe`.

Inside `(unsafe …)` every rule about loans still applies. Only the raw
operations are allowed.

## The library

| Module | What it gives |
|---|---|
| `safe.core` | `unsafe`; `borrow` and `borrow-mut`, a reference as a value; `replace!`, which swaps an owner out of a place; `move`; `each` and `each-mut`, a loop over a list, a slice or a string; `size` and `nth`, a `(slice T)` read with every index checked; the traits `View`, `QuietDrop`, `SharedView` and `CrossThread`; the annotation `:safe/borrows` |
| `safe.loop` | `(for (ref x) xs …)` and `(for (mut x) xs …)` over a safe collection, each element by reference; any other `for` is Coil's |
| `safe.fn` | `(deffn NAME [T…] [PARAM-TYPE…] RESULT)` declares a closure type; `(lambda NAME [(ref x) (mut y) (z (ref PLACE))…] [params…] body…)` makes one that borrows what it captures, `(lambda-own NAME [x (y VALUE)…] [params…] body…)` one of `NAME-own` that owns them; `(NAME::run (mut f) args…)` calls either; `(NAME-own::call-once f args…)` calls one and frees it, so `(spawn (NAME-own::call-once f))` runs it on a thread |
| `safe.view` | `(defview NAME [T…] [(field TYPE)…])`, a view whose fields may be references or views: `NAME::new`, `NAME::field`, `NAME::field-mut`. `(defsubscript NAME [T…] [params…] (-> (ref R) or (mut R)) before… (yield PLACE) after…)`: `NAME::open` runs `before` and gives a view of `PLACE`, read with `NAME::get` and `NAME::get-mut`; `after` runs when the view is dropped |
| `safe.box` | `(Box T)`, an owner of one heap value: `Box::new`, `get`, `get-mut`, `into` |
| `safe.own` | `(own Trait value)` makes an `(Own (dyn Trait))`, an owned trait object: a value of any type that implements the trait, on the heap, dropped as its own type drops. `(Own::get-mut (mut o))` lends the `(dyn Trait)` |
| `safe.maybe` | `(Maybe T)` and `(MaybeMut T)`: a reference or nothing, for a lookup's result (Coil keeps references out of `Option`). `Maybe::found`, `Maybe::nothing`, `found?`, `get`; `(if-found [x m] then else)`, `when-found`, `if-found-mut`. It is a view: it keeps what it was found in lent |
| `safe.pool` | `(Pool T)`, a collection that owns its elements, and `(Handle T)`, plain data checked when it is used: `insert!`, `remove!`, `at`, `at-mut`, `live?`, `len`, `handles` |
| `safe.global` | `defglobal`, `with-ref`, `with-mut`: a global lent for a scope, with exclusivity checked when the scope is entered |
| `safe.vec` | `(Vec T)`, a growable list that owns its elements: `push!`, `pop!`, `at`, `at-mut`, `swap!`, `insert!`, `remove!`, `clear!`; `(len v)`, `(get v i)` (a copy, for plain data) and `(set! (mut v) i x)` as for Coil's own collections. `(Vec::slice v from to)` is a `(Slice T)`, part of the list lent shared: `len`, `at`, `part`. `(Vec::slice-mut (mut v) from to)` is a `(SliceMut T)`, part of it lent exclusively: `len`, `at`, `at-mut`, `get`, `part`, `part-mut`, and `split`, which gives `(Halves T)`: `left` and `right`, both lent exclusively at once. An index out of range stops the program |
| `safe.str` | `Str`, text that owns its bytes: `Str::from "…"`, `len`, `byte`, `push!`, `push-text!`, `push-int!`, `append!`, `eq?`, `copy`; `Str::slice` is a `(Slice u8)` of its bytes, with `from-slice` and `push-slice!` to copy one. It prints with `{}`. `(str-of "x={} y={}" x y)` is a new `Str` formatted as `println` formats, and `(str-push! (mut s) "…" args…)` adds to one |
| `safe.map` | `(Map K V)`, a hash table that owns its keys and values; K needs `Hash` and `Eq`: `insert!`, `remove!`, `has?`, `at`, `at-mut`, `len`; `(each-entry [key value table] …)` walks it, as `first`/`next`/`key-at`/`value-at` do by hand |
| `safe.par` | `(par (f a…) (g b…))`: two calls at once, on two threads |
| `safe.thread` | `(spawn (f a…))` starts a thread and gives a `(Task R)`: `Task::join`, `Task::detach`. `(spawn-do (f a…))` starts a function that returns nothing and gives a `(Task Done)` |
| `safe.sync` | `(Arc T)`, an owner with many holders; `(Mutex T)` and `with-lock`; `(RwLock T)`, read by many or written by one: `read`, `write`; `Condvar`: `Guard::wait`, `notify-one`, `notify-all`; `(Channel T)`, a queue between threads: `send!`, `recv`, `close!`, `clone` |
| `safe.local` | `(deflocal NAME TYPE INIT)`, a value each thread has its own of; `with-local` and `with-local-ref` lend this thread's |

`Vec`, `Str`, `Box`, `Map` and `Arc` implement `Clone` (element by element, or for
`Arc` another holder), so `(derive Clone T)` works on a type built from them.

A stale handle, an index out of range, a key a `Map` does not hold, a lock asked
for by the thread that holds it, and a global or a thread-local entered while it
is already lent stop the program with a message. They are the checks made at
run time.

Each module exports only what safe code may call. The functions it uses inside
(the ones that trust their arguments) cannot be named from outside it. Every
type works for an element with no size, such as a struct with no fields:
`safe.mem` is the allocation the library shares, and it gives such a type an
address nothing is read from.

### Loops

```coil
(each [x v] (set! sum (+ sum (primitive/load x))))       ; x is a reference to each element
(each-mut [x v] (set! x (* 2 (primitive/load x))))       ; x is an exclusive reference
(each-entry [name age ages] (println "{} {}" name (primitive/load age)))
```

`each` works on a `Vec`, a `Slice`, a `SliceMut` and a `Str` (its bytes);
`each-mut` on a `Vec` and a `SliceMut`. The collection is lent for the whole of
each turn, so the body cannot add to it or take from it. With `safe.loop`,
`(for (ref x) v …)` and `(for (mut x) v …)` are the same loops written as Coil's
`for`.

### Closures

```coil
(deffn Bump [(mut i64)] void)           ; a closure type: takes (mut i64), gives nothing

(defn twice [(x (mut i64)) (f (mut Bump))] (-> void)
  (Bump::run (mut f) (mut x))
  (Bump::run (mut f) (mut x)))

(let [(mut total) 0
      step 10
      (mut x) 1
      (mut f) (lambda Bump [(mut total) (ref step)] [v]
                (set! total (+ total v))
                (set! v (+ v step)))]
  (twice (mut x) (mut f))
  (println "{} {}" total x))            ; 12 21: total and step are free again once f is done
```

Inside the body, `total` is an exclusive reference and `step` a shared one; the
closure keeps `total` lent exclusively and `step` shared until its last use.
`lambda-own` captures by moving: `(lambda-own Count [n] [] (set! n (+ n 1)) n)`
is a counter that can be returned, stored, or given to `spawn` through
`Count-own::call-once`. A closure gives back a value, never a reference into
what it captured.

### Views and subscripts

```coil
(defsubscript Clamped [(x (mut i64)) (hi i64)] (-> (mut i64))
  (yield x)
  (when (> x hi) (set! x hi)))           ; runs when the view is dropped

(let [(mut v) 3]
  (let [(mut c) (Clamped::open (mut v) 10)]
    (set! (Clamped::get-mut (mut c)) 50))
  v)                                     ; 10
```

### Moving parts out

Coil lets a field be moved out of a struct, and what a `(mut T)` parameter
refers to be moved out until the function gives it back; `(out T)` parameters
fill a place that holds nothing, such as a variable made with `(uninit [T])`.
The compiler tracks which parts are gone (see the Coil language guide); the
checker's loans work on the same places.

An owner, or a part of one, may be moved on some ways through an `if`, a
`match` or a loop's exits and not on others: after they meet it counts as moved,
and on the ways that kept it Coil still drops it, at the end of its scope or when
`set!` replaces it, by a flag set at run time (Rust's drop flags).

### Owned trait objects

```coil
(deftrait Shape [Self] (area [(self (ptr Self))] (-> i64)))
(let [(mut shapes) (Vec::new [(Own (dyn Shape))])]
  (Vec::push! (mut shapes) (own Shape (Square :side 3)))
  (Vec::push! (mut shapes) (own Shape (Rect :w 2 :h 5)))
  (for (mut s) shapes (println "{}" (area (Own::get-mut (mut s))))))
```

An `Own` keeps no `(dyn Trait)` in it: `get-mut` makes one each time, lent
exclusively from the `Own`, so the `Own` is not moved, dropped or used again while
it is in use.

## Programs

`examples/` holds programs written in safe Coil, none with `unsafe` in it. Each runs
clean under `--sanitize=address`:

| Program | What it uses |
|---|---|
| `calc.coil` | Coil's calculator example: a lexer, a recursive-descent parser into a boxed tree, an evaluator |
| `lisp.coil` | a Lisp: a reader, closures over shared environments (`Arc`, `Mutex`, `Map`), errors as results |
| `json.coil` | a JSON parser, printer and path query: a recursive sum of `Vec`s and `Map`s, `Maybe`, `:safe/borrows` |
| `graph.coil` | a generic binary heap, Dijkstra, a topological order, union-find: generics with trait bounds, two-phase borrows |
| `shapes.coil` | a scene of owned trait objects, one a group of others |
| `pipeline.coil` | generic `map`, `filter`, `fold` and sort taking closures; a list of stored rules, each an owning closure |
| `sim.coil` | rabbits and foxes in a `Pool`: entities naming each other by handle, removed while others hold handles |
| `lru.coil` | a least-recently-used cache: a doubly linked list in a `Pool`, linked by handle, and a `Map` of keys to entries |
| `msort.coil` | a parallel merge sort: a slice split into halves sorted on two threads with `par` |
| `vm.coil` | a tiny language compiled to bytecode and run on a stack machine: trees of boxed sums, jumps patched after the fact, a call stack |
| `wordcount.coil` | words counted on four threads into a shared table, through a channel |

### par

`(par (fill (mut p) (borrow base) (Box::new 10) 2) (count-up (mut n) 1000))`
runs the first call on a new thread and the second on this one, and returns when
both have. An argument is written as the callee takes it: `(mut place)`,
`(borrow place)`, or a value, which is moved or copied to its call. Every
argument of both calls is bound to a name before either starts, so the checker
sees their loans together, as the arguments of one call: nothing lent
exclusively to one call can reach the other. A global's borrow count is atomic.

### Threads

```coil
(defn add-many [(total (Arc (Mutex i64))) (times i64)] (-> i64)
  (for i (range 0 times)
    (with-lock (Arc::get total) n
      (set! n (+ n 1))))
  0)

(let [total (Arc::new (Mutex::new 0))
      a (spawn (add-many (Arc::clone total) 20000))
      b (spawn (add-many (Arc::clone total) 20000))]
  (Task::join a)
  (Task::join b)
  (with-lock (Arc::get total) n (println "{}" n)))      ; 40000
```

`(spawn (f a b))` runs `(f a b)` on a new thread. The thread owns what it is
given: `f` takes every argument by value, so each is moved or copied to the
thread and no reference crosses. The thread calls `f` through a pointer, so `f`
may be a method, `Type::method`, such as a closure's `call-once`. Coil itself refuses a reference where a value
is asked for, and the checker refuses a view. `Task::join` waits for what `f`
returns and hands it back. A function that returns nothing is started with
`spawn-do`. A task that is dropped waits for its thread; `Task::detach` lets the
thread run on.

What threads share is one of these, and each keeps the rule that a place is
changed only by whoever has it exclusively:

- an `(Arc T)` lends its value shared only, to every holder;
- a `(Mutex T)` gives one thread at a time an exclusive reference, for the body
  of `with-lock`. The held lock is a view: the mutex stays lent to it, and the
  reference cannot leave the body. `(Guard::wait (mut guard) condvar)` gives the
  lock up while it sleeps; the guard is lent exclusively to the call, so no
  reference to the value is kept across the wait;
- an `(RwLock T)` gives many threads a shared reference at once (`read`), or
  one an exclusive reference (`write`). Both results are views;
- a `(Channel T)` moves a value from the sender to the receiver;
- a global, as before, is lent for a scope and checked when entered.

A thread-local (`safe.local`) is shared with nobody: `(NAME)` is a view of this
thread's value, so it cannot be stored or sent, and the value is dropped when
its thread ends.

So every type is safe to send and safe to share, with no marker traits. This
holds because safe code has no way to change memory through a shared
reference. Code inside `unsafe` that does so must do it atomically or under a
lock, as `safe.sync` and `safe.global` do.

`examples/wordcount.coil` counts words on four threads into one shared `Map`.

## Testing

```sh
python3 tests/run.py            # hand-written Coil cases: ok_* must pass, bad_* must be refused by the checker, no_* by the compiler
python3 tests/diff.py 4000 7    # the checker against the model, on N random programs from a seed
python3 tests/teeth.py          # each checker rule weakened in turn: diff.py must notice
```

`tests/diff.py` is the main check. `model/to-coil.rkt` writes a model program as
Coil; the model's hand-written cases and N random programs are compiled with the
checker, and the checker must accept exactly what the model accepts. A program
the compiler itself refuses is set aside, because the checker never saw it. The
run fails if the checker accepts anything the model refuses.

`tests/teeth.py` is the check on that check: it removes one rule from the
checker at a time and requires `diff.py` to find a program the weakened checker
wrongly accepts.

On the model's 161 cases and 4000 random programs (seed 7), 3396 can be written
as Coil; 765 use something Coil cannot express (most often a closure that
returns a reference, or one that owns a capture that is not a borrow). The
compiler refuses 1460 of them itself. On the other 1933 the checker accepts
nothing the model refuses: 1327 accepted by both, 580 refused by both, and 26
refused only by the checker, each for one of the differences below. All 25
weakenings are caught, 24 by a hand-written case and one by the differential
run.

`tests/run.py` has 125 hand-written cases. Every `ok_` case and both examples
also run clean under `--sanitize=address` and `--sanitize=thread`.

### Where Coil and the model differ

Found by the differential run:

- **An exclusive reference is never moved.** The model moves one when it is
  named, and refuses a later use. Coil lends through it again each time, and the
  checker holds that loan, so it accepts some programs the model refuses for
  that reason alone. `diff.py` counts them apart (`reborrow`).

- **The compiler's move rule is stricter.** An `if` or `match` whose branches do
  not move the same owners is refused by the compiler; the model treats the owner
  as moved afterwards.
- **Taking an address reads.** The model's `addr` of a place inside a box does
  not read the box. Its Coil form goes through `Box::get`, which does, so the
  checker refuses it while the box is lent exclusively.
- **A discarded name is not a move.** The model moves an owner that is named and
  thrown away; Coil leaves it alone. The translation writes `(move x)`.
- **Plain data passed by value counts as lent for the call.** The model copies
  it. Coil passes a pointer to the caller's storage.

- **A view's references are read through functions.** The model's view is a
  struct of references. Coil refuses a reference in a struct, so the Coil form
  is a struct of raw pointers marked `View`, with a function for each field
  that lends what it points at. The checker ties what such a function returns
  to the view it was given. The model knows the reference came from what the
  view was made from, so it lets that reference outlive the view, and treats two
  fields of one view as two places. The checker refuses both.

- **A closure has one kind.** The model copies a closure that captured only
  shared references, and so will not take one that captured something
  exclusively where such a closure is asked for. Coil never copies a closure and
  runs one only through an exclusive reference to it, so it takes either. The
  checker may accept a program the model refuses for that alone; `diff.py`
  counts them apart (`closure-kind`).
- **`par` takes a view only by reference, and only one that may cross
  threads.** The model lets a view be an argument of a `par` call. `safe.par`
  passes each argument through a type parameter, which the checker never lets a
  view be, except that its own expansion may hand its helpers `(mut v)` or
  `(borrow v)` for a view whose module says it is `CrossThread` (`Slice`,
  `SliceMut`, `Halves`; not a held lock).
- **A shared match on a plain-data payload reads a copy.** Coil copies such a
  payload into the arm, so the Coil form lends the copy. The checker refuses a
  reference to it that leaves the arm; the model lets a reference to the
  payload itself leave.

Model programs Coil cannot express, which `diff.py` skips: `match-mut` on a
plain-data payload (a write would change the copy), and an exclusive reference
read out of a view's field as a value.

## The model

A small language with everything the rules are about:

| In the model | Stands for |
|---|---|
| `(box σ)` | an owner: a heap allocation freed when its owner leaves scope |
| `(ref σ)`, `(mut σ)` | shared and exclusive references: a local, an argument or a result, never stored |
| `(view V)` | a struct with reference fields (a slice, an iterator): treated as a reference. A view may hold a view, and may name a function its drop runs (a lock, a subscript's code after its yield), which keeps its loans until its scope ends |
| `(lam ([x τ e] …) params τ body)`, `(fnb k (τ…) τ)` | a closure that borrows what it captures: a view of those loans, exclusive when it captured something exclusively; `(apply f args…)` calls it |
| `(lamo ([x σ e] …) params τ body)`, `(fno (τ…) τ)` | a closure that owns what it captured: storable; `(spawn-fn f)` runs one on a thread |
| `(: x a)` moved, `(set! (: x a) v)` | parts moved out of a variable, or out of what an exclusive parameter refers to, and given back |
| `(out σ)`, `(out p)`, `(uninit σ)` | a parameter that fills a place holding nothing; a variable made with nothing in it |
| `(return e τ)` | leaving a function early |
| `struct`, `sum`, `match`, `match-ref`, `match-mut` | structs with separately lent fields; sums whose payload reference keeps the variant in place |
| `(pool σ)`, `(handle σ)`, `(at p h)` | a collection that owns its elements, and plain-data handles checked when used |
| type parameters | generics: a parameter may be an owner and can never be a reference |
| `while`, `break` | loops; what is moved before a break is moved after the loop |
| `(with ref g x …)`, `(with mut g x …)` | a global, lent for a scope, with exclusivity checked on entry |
| `(par (call …) (call …))` | two calls running at once |
| `(spawn (call …))`, `(join e)`, `(task σ)` | a call on a thread that runs on; the task is an owner, and no argument is a reference |
| `(unsafe …)`, `(ptr σ)`, `addr`, `load`, `store`, `alloc`, `free` | raw memory: a raw pointer is plain data anywhere and is followed only inside `unsafe` |

| File | What it is |
|---|---|
| `model/rules.rkt` | The rules, as a Redex judgment: `(chk Σ Γ Λ e τ L Γ′)` |
| `model/machine.rkt` | What a program does. It knows no types and no loans |
| `model/cases.rkt` | Hand-written programs the rules must accept or reject |
| `model/search.rkt` | Random programs, looking for one the rules accept that goes wrong |
| `model/to-coil.rkt`, `model/diff.rkt` | A model program as Coil, for `tests/diff.py` |

The machine is **stuck** on what the rules exist to rule out: a read or write of
dead memory, a read of a moved value, a double free, a reference into a variant
or pool element that is gone, and a data race between the two sides of a `par`.
It **panics**, which is a defined stop, on the two checks made at run time: a
stale handle, and a global entered while it is already lent.

The property: a program the rules accept, with no `unsafe` in it, is never stuck
and frees everything it allocated.

```sh
raco pkg install --auto redex-lib   # once
racket model/cases.rkt
racket model/search.rkt             # 20000 programs
racket model/search.rkt 100000 7    # N programs from a seed
racket model/search.rkt teeth       # each rule weakened in turn: the search must find a failure
racket model/search.rkt teeth 20000 no-union par-split   # only those weakenings
```

`teeth` is the check on the search itself. `rules.rkt` lists 35 ways to weaken
one rule (`mutants`), and the machine can drop its run-time check on globals.
`teeth` fails unless a hand-written case or the search finds a program that goes
wrong under each one.
The programs a seed gives depend on the rules, because a function body the
rules refuse is generated again, so `teeth` looks through four seeds before it
says a weakening was not found.

Four seeds of 20000 programs find no counterexample under the rules as they
are. All 36 weakenings are found: 34 at 5000 programs a seed, and two (an
exclusive reference copied, a later branch's loans forgotten) at 20000.

## What the rules are stricter about than they need to be

These are sound and simple. The model should be relaxed first, then the checker.

- A returned reference borrows from every argument the call took by reference.
- Every element of a pool is one place: two elements cannot be lent exclusively at once.
- An owner is moved out of a field or out of what an exclusive *parameter* refers
  to, never through any other reference (a `with` of a global, a `let` bound to
  one): only a function's exits check that what was moved out is given back.
  `replace!` swaps an owner out of anywhere.
- A closure that captured only shared references is still moved, never copied,
  in Coil (the model copies one).
- A reference that is thrown away still may not outlive what it refers to.

## What is left out

- Coil's own arrays, and slices other than read: an array literal needs
  `unsafe`, and so do `ArrayList` and `HashMap`; `Vec`, `Slice`, `SliceMut`, `Map`
  and `Str` are the safe collections. A `(slice T)` is read with `size`, `nth`
  and `for`.
- Coil's `for` over a `Vec` or a `Map`. Its iterator protocol hands each element
  out as a value of a type parameter, which a reference can never be; `each`,
  `each-mut` and `each-entry` are the loops.
- A thread that holds a read lock and asks to write the same `RwLock` waits for
  ever. That is a hang, not a memory error.
- Function pointers: `fnptr-of` and a call through one stay `unsafe`-only. A
  closure with no captures (`lambda-own` with an empty capture list) is the
  safe function value.
- A closure that returns a reference: as in Hylo, a closure gives back a value.
- What is inside `unsafe`: the rules say which operations need it and that the
  other rules still hold there, and make no claim about a program that uses it.
