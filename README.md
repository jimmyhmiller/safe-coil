# safe-coil

A memory-safe mode for Coil, as a metaprogram that restricts the language. The
metaprogram is not written yet. `model/` is where its rules are worked out and
tested first, in PLT Redex.

## The model

The calculus has owners (a box is a heap allocation freed when its owner leaves
scope), moves, and second-class references: a reference can be a local, an
argument or a result, and can never be stored.

| File | What it is |
|---|---|
| `model/rules.rkt` | The rules, as a Redex judgment: `(chk F Γ Λ e τ L Γ′)` |
| `model/machine.rkt` | What a program does. It knows no types and no loans, and is stuck on a read or write of dead memory, a read of a moved value, or a double free |
| `model/cases.rkt` | Hand-written programs the rules must accept or reject |
| `model/search.rkt` | Random programs, looking for one the rules accept that gets stuck or leaks |

```sh
raco pkg install --auto redex-lib   # once
racket model/cases.rkt
racket model/search.rkt             # 20000 programs
racket model/search.rkt 100000 7    # N programs from a seed
racket model/search.rkt teeth       # each rule weakened in turn: the search must find a failure
```

`teeth` is the check on the search itself. It switches off each of three rules,
then applies each of eight smaller mutations, and fails unless the search finds a
program that goes wrong every time. A search that passes the real rules means
little until it catches every weakened one.

## What the model leaves out

Loops, structs and fields (so no disjoint-field borrows), sums and `match`,
generics, view types, handles, globals, threads and `unsafe`. Loans are lexical:
one lives until its holder's scope ends, not until its last use.
