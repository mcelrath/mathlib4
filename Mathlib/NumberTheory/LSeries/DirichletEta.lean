/-
Copyright (c) 2026 Implementation via Claude Code. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Dirichlet Eta Function

## Main definitions:

* `dirichletEta`: the Dirichlet eta function `η(s) = ∑_{n=1}^∞ (-1)^(n-1) / n^s`.

## Main results:

* `dirichletEta_eq_one_sub_pow_mul_zeta`: For `s ≠ 1`, `η(s) = (1 - 2^(1-s)) ζ(s)`.
* `dirichletEta_at_one`: `η(1) = ln(2)` (the alternating harmonic series).

## References

* Apostol, T. M. (1976). Introduction to Analytic Number Theory. Springer.
* NIST Digital Library of Mathematical Functions, §25.11 "Hurwitz and Lerch Zeta Functions"

## Implementation notes

The Dirichlet eta function is defined as an alternating series that converges for `Re(s) > 0`,
providing analytic continuation of the Riemann zeta function to the critical strip.

The definition uses a piecewise form to handle the removable singularity at s = 1, where
the indeterminate form `(1 - 2^(1-1)) · ζ(1) = 0 · ∞` would otherwise be problematic.

For `s ≠ 1`, the series equals `(1 - 2^(1-s)) ζ(s)`, which follows from:
```
ζ(s) = ∑ 1/n^s = (∑ 1/n^s over n odd) + (∑ 1/n^s over n even)
     = (∑ 1/n^s over n odd) + 2^(-s) · (∑ 1/m^s)
     = (∑ 1/n^s over n odd) + 2^(-s) · ζ(s)

So: (1 - 2^(-s)) ζ(s) = ∑ 1/n^s over n odd
                       = ∑ (-1)^(n-1) / n^s   (alternating series)
                       = η(s)
```

Multiplying by 2^s gives: (2^s - 1) ζ(s) = 2^s η(s), or η(s) = (1 - 2^(1-s)) ζ(s).

-/

noncomputable section

open Complex

namespace DirichletEta

/-! ## Definition -/

/-- The Dirichlet eta function `η(s) = ∑_{n=1}^∞ (-1)^(n-1) / n^s`.

This is defined piecewise to handle the removable singularity at s = 1:
- At s = 1: η(1) = ln(2) (the alternating harmonic series)
- For s ≠ 1: η(s) = (1 - 2^(1-s)) ζ(s)

The piecewise definition avoids the indeterminate form `0 · ∞` that would arise
from evaluating `(1 - 2^(1-1)) · ζ(1)` directly. -/
def dirichletEta (s : ℂ) : ℂ :=
  if s = 1 then log 2
  else (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-! ## Basic properties -/

/-- At s = 1, the Dirichlet eta function equals ln(2).

This is the alternating harmonic series: η(1) = 1 - 1/2 + 1/3 - 1/4 + ... = ln(2). -/
theorem dirichletEta_at_one : dirichletEta 1 = log 2 := by
  simp [dirichletEta]

/-- For s ≠ 1, the eta function satisfies η(s) = (1 - 2^(1-s)) ζ(s). -/
theorem dirichletEta_ne_one (s : ℂ) (hs : s ≠ 1) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  simp [dirichletEta, hs]

/-- Alternative form: η(s) = (1 - 2^(1-s)) ζ(s) for s ≠ 1.

This is the main functional equation relating eta to zeta. -/
theorem dirichletEta_eq_one_sub_pow_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
  dirichletEta_ne_one s hs

end DirichletEta
