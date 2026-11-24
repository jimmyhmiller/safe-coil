# safe-coil

A memory-safe mode for Coil, as a metaprogram that restricts the language. The
metaprogram is not written yet. `model/` is where its rules are worked out and
tested first, in PLT Redex.

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
| `(unsafe …)`, `(ptr σ)`, `addr`, `load`, `store`, `alloc`, `free` | raw memory: a raw pointer is plain data anywhere and is followed only inside `unsafe` |

| File | What it is |
|---|---|
| `model/rules.rkt` | The rules, as a Redex judgment: `(chk Σ Γ Λ e τ L Γ′)` |
| `model/machine.rkt` | What a program does. It knows no types and no loans |
| `model/cases.rkt` | Hand-written programs the rules must accept or reject |
| `model/search.rkt` | Random programs, looking for one the rules accept that goes wrong |

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
A search that passes the real rules means little until it catches every
weakened one.

## What the rules are stricter about than they need to be

These are sound and simple; the metaprogram may relax them later, and the model
should be relaxed first.

- Loans are lexical: one lives until its holder's scope ends, not until its last use.
- A returned reference borrows from every reference argument of the call.
- Every element of a pool is one place: two elements cannot be lent exclusively at once.
- Only a whole variable can be moved. `take` swaps an owner out of a field, a
  box or a pool element.
- A loop body cannot move a variable from outside the loop, even just before a `break`.

## What the model leaves out

- `return` from the middle of a function.
- Detached threads. `par` is two calls that both finish before anything else runs.
- Arrays and slices as such: a pool with handles stands for indexed storage, and
  a view for a slice.
- Trait objects and function pointers.
- What is inside `unsafe`: the model says which operations need it and that the
  other rules still hold there, and makes no claim about a program that uses it.
