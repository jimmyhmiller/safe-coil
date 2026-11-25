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
  the name bound to it is in scope. A place is not read while lent exclusively,
  and not written, moved, or lent exclusively while lent at all. Two fields of
  one struct are separate places.
- **Arguments.** Each argument's loans are alive while the later ones are
  evaluated, so `(f (mut p) p)` is refused. Plain data passed by value is read
  where it lies for the length of the call, so it counts as lent shared.
- **No escape.** A reference cannot leave the scope of the local it refers to: not
  as the value of a `let`, a `block`, a `break` or a function, and not as a
  reference to a temporary.
- **Results.** A reference a call returns borrows from every argument the call
  took by reference.
- **Temporaries.** Coil drops a temporary that owns something as soon as the
  call it was passed to returns. So a call's result may not borrow from one:
  `(Box::get (Box::new 1))` is refused, and so is reading through a lock taken
  and given up in one expression. Bind the temporary to a name first. A
  temporary of plain data lives as long as the function's frame.
- **Match.** A `match` on a name lends the parts of the payload that own something
  to the arm, where they lie. The matched place stays lent to those names, so the
  variant cannot be replaced under them. `(match (move x) …)` consumes x instead.
- **Views.** A struct marked `(impl View TYPE)` stands for the references it was
  made from, as a held lock or a slice of a list does. A call that returns one
  keeps what it took by reference lent for as long as the view lives. A view is
  a local, an argument or a result: it is not stored in a struct, a variant or
  a place, and not passed for a type parameter, so it reaches no container and
  no other thread.
- **Raw fields.** A struct or variant with a field that is itself raw memory is
  built only inside `unsafe`, and such a field is changed only there. So a type
  like `Box` holds the pointer its own code put in it, never one safe code made up.
- **Raw memory.** A raw pointer is plain data anywhere. It is followed only inside
  `(unsafe …)`: a load, a store, a field behind one, a reference made from one, a
  call of an `extern`, a call through a function pointer or a trait object.
- **Library code.** A function of the standard library is called freely unless it
  takes raw memory, which includes slices, arrays and anything holding a pointer
  (so `ArrayList` and `HashMap`). Those calls need `unsafe`. The code `print`,
  `println`, `panic`, `unreachable` and `assert` expand to is trusted; raw memory
  the program made must not be handed to it.
- **Anything else is refused.** A form the rules do not cover (`defer`, a
  destructuring `let`, an array literal, a primitive not listed as safe) is an
  error outside `unsafe`.

Inside `(unsafe …)` every rule about loans still applies. Only the raw
operations are allowed.

## The library

| Module | What it gives |
|---|---|
| `safe.core` | `unsafe`; `borrow` and `borrow-mut`, a reference as a value; `replace!`, which swaps an owner out of a place; `move` |
| `safe.box` | `(Box T)`, an owner of one heap value: `Box::new`, `get`, `get-mut`, `into` |
| `safe.pool` | `(Pool T)`, a collection that owns its elements, and `(Handle T)`, plain data checked when it is used: `insert!`, `remove!`, `at`, `at-mut` |
| `safe.global` | `defglobal`, `with-ref`, `with-mut`: a global lent for a scope, with exclusivity checked when the scope is entered |
| `safe.vec` | `(Vec T)`, a growable list that owns its elements: `push!`, `pop!`, `len`, `at`, `at-mut`. `(Vec::slice v from to)` is a `(Slice T)`, part of the list lent shared: `len`, `at`, `part`. An index out of range stops the program |
| `safe.str` | `Str`, text that owns its bytes: `Str::from "…"`, `len`, `byte`, `push!`, `push-text!`, `push-int!`, `append!`, `eq?`, `copy`. It prints with `{}` |
| `safe.map` | `(Map K V)`, a hash table that owns its keys and values; K needs `Hash` and `Eq`: `insert!`, `remove!`, `has?`, `at`, `at-mut`, `len`, and `first`/`next`/`key-at`/`value-at` to walk it |
| `safe.par` | `(par (f a…) (g b…))`: two calls at once, on two threads |
| `safe.thread` | `(spawn (f a…))` starts a thread and gives a `(Task R)`: `Task::join`, `Task::detach` |
| `safe.sync` | `(Arc T)`, an owner with many holders; `(Mutex T)` and `with-lock`; `(Channel T)`, a queue between threads: `send!`, `recv`, `close!`, `clone` |

A stale handle, an index out of range, a key a `Map` does not hold, a lock asked
for by the thread that holds it and a global entered while it is already lent
stop the program with a message. They are the checks made at run time.

Each module exports only what safe code may call. The functions it uses inside
(the ones that trust their arguments) cannot be named from outside it.

`examples/calc.coil` is Coil's calculator example (a lexer, a recursive-descent
parser into a boxed tree, an evaluator) in safe Coil, with no `unsafe` in it.

### par

`(par (fill (mut p) (borrow base) (Box::new 10) 2) (count-up (mut n) 1000))`
runs the first call on a new thread and the second on this one, and returns when
both have. An argument is written as the callee takes it: `(mut place)`,
`(borrow place)`, or a value, which is moved or copied to its call. Every
argument of both calls is bound to a name before either starts, so the checker
sees their loans together, as the arguments of one call: nothing lent
exclusively to one call can reach the other. A global's borrow count is atomic.
The first call takes at most eight arguments.

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
thread and no reference crosses. Coil itself refuses a reference where a value
is asked for, and the checker refuses a view. `f` returns a value (0 if it has
nothing to say), which `Task::join` waits for and hands back. A task that is
dropped waits for its thread; `Task::detach` lets the thread run on.

What threads share is one of three things, and each keeps the rule that a
place is changed only by whoever has it exclusively:

- an `(Arc T)` lends its value shared only, to every holder;
- a `(Mutex T)` gives one thread at a time an exclusive reference, for the body
  of `with-lock`. The held lock is a view: the mutex stays lent to it, and the
  reference cannot leave the body;
- a `(Channel T)` moves a value from the sender to the receiver;
- a global, as before, is lent for a scope and checked when entered.

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

On the model's 108 cases and 4000 random programs (seed 7), 3359 can be written
as Coil. The compiler refuses 1155 of them itself. On the other 2204 the checker
accepts nothing the model refuses: 1618 accepted by both, 584 refused by both,
one refused only by the checker (below), and one that is the exclusive-reference
case below. All fifteen weakenings are caught, by a hand-written case or by the
differential run.

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

Model programs Coil cannot express, which `diff.py` skips: views (Coil refuses a
reference in a struct) and `match-ref`/`match-mut` on a plain-data payload (Coil
copies it into the arm).

## The model

A small language with everything the rules are about:

| In the model | Stands for |
|---|---|
| `(box σ)` | an owner: a heap allocation freed when its owner leaves scope |
| `(ref σ)`, `(mut σ)` | shared and exclusive references: a local, an argument or a result, never stored |
| `(view V)` | a struct with reference fields (a slice, an iterator): treated as a reference |
| `struct`, `sum`, `match`, `match-ref`, `match-mut` | structs with separately lent fields; sums whose payload reference keeps the variant in place |
| `(pool σ)`, `(handle σ)`, `(at p h)` | a collection that owns its elements, and plain-data handles checked when used |
| type parameters | generics: a parameter may be an owner and can never be a reference |
| `while`, `break` | loops |
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

`teeth` is the check on the search itself. `rules.rkt` lists 22 ways to weaken
one rule (`mutants`), and the machine can drop its run-time check on globals.
`teeth` fails unless the search finds a program that goes wrong under each one.

## What the rules are stricter about than they need to be

These are sound and simple. The model should be relaxed first, then the checker.

- Loans are lexical: one lives until its holder's scope ends, not until its last use.
- A returned reference borrows from every argument the call took by reference.
- Every element of a pool is one place: two elements cannot be lent exclusively at once.
- Only a whole variable can be moved. `replace!` swaps an owner out of a field, a
  box or a pool element.
- A loop body cannot move a variable from outside the loop, even just before a `break`.
- A reference that is thrown away still may not outlive what it refers to.

## What is left out

- Coil's own slices and arrays as safe types. They are raw memory to the
  checker, so the library's `ArrayList` and `HashMap` need `unsafe`; `Vec`,
  `Slice`, `Map` and `Str` are the safe ones. There is no exclusive slice and
  no slice of a `Str` yet.
- Views in the differential test. The model's view is a struct of references,
  which Coil refuses; the checker's view is a marked struct of raw pointers.
  `diff.py` still skips the model's view programs, so the checker's view rule
  is tested by hand-written cases and by `teeth.py` only.
- A `for` over a `Vec` or a `Map`. Walk one by index or by cursor.
- Read-write locks, condition variables, thread-local values, a `spawn` of a
  function that returns nothing, and more than eight arguments to a thread.
- `return` from the middle of a function, trait objects and
  function pointers: outside the model, and refused or `unsafe`-only in the checker.
- What is inside `unsafe`: the rules say which operations need it and that the
  other rules still hold there, and make no claim about a program that uses it.
