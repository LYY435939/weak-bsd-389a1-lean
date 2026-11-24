# Weak BSD for 389.a1 in Lean

This project formalizes the rank part of the Birch–Swinnerton-Dyer conjecture for the elliptic curve `y² + y = x³ + x² − 2x` over `ℚ` (LMFDB 389.a1). The result is a known individual case: `ord_{s=1} L(E,s) = rank E(ℚ) = 2`. The full leading-coefficient formula and finiteness of Sha are outside this result.

The terminal statement is `BSD.RankTwo.FLTAdapter.weakBSD389` in `RankPart389.lean`. The arithmetic rank statement is `BSD.RankTwo389.rational_finrank_eq_two`. Lean 4.33.1 checked the declarations using `propext`, `Classical.choice`, and `Quot.sound`.

The `BSD/` directory contains selected proof dependencies from research commit `2880d18`. `ExactWitness.lean` and `ExternalDataBridge.lean` adapt six modularity results from the fixed external FLT library. Dependency revisions and the checked Stoll compatibility patch are documented in `verification/flt-389-compat/README.md` and `verification/flt-long-twist/README.md`.

The recorded validation rebuilt 37 affected modules and reused cached dependencies. A portable clean build of this repository has not yet been verified. The independent checker replay was in progress when this repository was prepared. The included Lake configuration alone does not set up the external FLT dependency and compatibility build; see the verification documents for the historical commands and limitations. No general proof of BSD is claimed.
