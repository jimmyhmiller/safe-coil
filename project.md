# safe-coil

## Summary

A memory-safe Coil, written as a metaprogram that restricts ordinary Coil. Owners are moved,
references are second-class and end at their last use, a call may not take two exclusive
references to the same place, and raw memory is reached only inside `(unsafe …)`. The rules
are modelled first in PLT Redex (`model/`); the checker (`src/check.coil`, used with
`coil check FILE --use safe.check`) follows the model and is tested against it on generated
programs. The library (`safe.vec`, `safe.str`, `safe.map`, `safe.sync`, `safe.thread`, …) is
built from unsafe Coil behind safe interfaces. See README.md.
