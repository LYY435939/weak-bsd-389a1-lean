# Weak BSD for 389.a1 in Lean

This repository contains the Lean formalization of the rank part of the Birch–Swinnerton-Dyer conjecture for the elliptic curve `y² + y = x³ + x² − 2x` over `ℚ` (LMFDB 389.a1). The established statement is `ord_{s=1} L(E,s) = rank E(ℚ) = 2`. This is an individual known case of weak BSD. The full leading-coefficient formula and finiteness of Sha are outside this result.

The top-level Lean statement is `BSD.RankTwo.FLTAdapter.weakBSD389` in `verification/flt-389-compat/RankPart389.lean`. The arithmetic rank statement is `BSD.RankTwo389.rational_finrank_eq_two`. The Lean 4.33.1 checks for these declarations and the modularity witness succeeded with axioms `propext`, `Classical.choice`, and `Quot.sound`.

`source-389a1.zip` contains a selection of BSD source dependencies from research commit `2880d18`, the external FLT adapter, and the checked compatibility patch. Dependency revisions and precise historical verification boundaries are in the included `verification/flt-389-compat/README.md` and `verification/flt-long-twist/README.md`.

The recorded verification rebuilt 37 affected modules and reused cached dependencies. A portable clean build from this exported archive has not yet been verified. The independent checker replay was in progress when this package was prepared. The included Lake configuration alone does not set up the external FLT dependency and compatibility build. No general proof of BSD is claimed.
