/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivative of the Gaussian Poisson summation formula (DRAFT — work in progress)

`Real.tsum_exp_neg_mul_int_sq` provides the bosonic Jacobi inversion

`∑' (n : ℤ), exp (-π * a * n ^ 2) = a ^ (-1/2) * ∑' (n : ℤ), exp (-π / a * n ^ 2)`

for real `a > 0`. Differentiating both sides with respect to `a` produces a closed
form for the `n²`-weighted sum

`∑' (n : ℤ), n ^ 2 * exp (-π * a * n ^ 2)`

in terms of the dual sum. This file is intended to package that derivative
identity, which is needed for heat-kernel and spectral-zeta applications
(e.g. derivatives of the Jacobi theta function in the modular parameter).

## Status

DRAFT. The statements below are the intended API. Proofs of
`hasDerivAt_tsum_exp_neg_pi_mul_int_sq` and the closed-form identity require:

1. A clean ℤ-indexed dominator for `n² · exp(-π a n²)` (proof is the
   symmetrization of the standard `summable_pow_mul_geometric_of_norm_lt_one`
   ℕ-result; bookkeeping of `Int.natAbs` is fiddly).
2. Application of `hasDerivAt_tsum_of_isPreconnected` on `Set.Ioi (a/2)`
   with the geometric majorant from (1) — at the order of `n² · π · n² ·
   exp(-π · (a/2) · n²)` for the derivative bound.
3. Differentiation of the RHS via product / chain rule on
   `a ↦ a^(-1/2) · F(1/a)` where `F(b) := ∑' n, exp(-π b n²)`.
4. Algebraic rearrangement to obtain the closed form.

The statements compile (modulo `sorry`); the proofs are the substantive content.

## Main results (intended)

* `Real.summable_n_sq_exp_neg_pi_mul_int_sq` — summability of `n² · exp(-π a n²)`
  over `ℤ` for `a > 0`.
* `Real.hasDerivAt_tsum_exp_neg_pi_mul_int_sq` — term-by-term differentiation
  of `a ↦ ∑' n, exp(-π a n²)`, giving derivative `-π ∑' n, n² exp(-π a n²)`.
* `Real.tsum_n_sq_exp_neg_pi_mul_int_sq_eq` — closed-form expression obtained
  by differentiating the bosonic Poisson inversion formula.
-/

open scoped Real Topology
open Real Filter Set

namespace Real

/-! ### Summability of `n² · exp(-π a n²)` -/

/-- For `a > 0`, the `n²`-weighted Gaussian series is summable over `ℤ`. -/
theorem summable_n_sq_exp_neg_pi_mul_int_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2)) := by
  sorry

/-! ### Term-by-term derivative of the bosonic Gaussian sum -/

/-- Term-by-term differentiation: for `a > 0`,
`d/da [∑' n, exp(-π a n²)] = -π · ∑' n, n² · exp(-π a n²)`. -/
theorem hasDerivAt_tsum_exp_neg_pi_mul_int_sq {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b : ℝ => ∑' n : ℤ, Real.exp (-π * b * (n : ℝ) ^ 2))
      (-π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2)) a := by
  sorry

/-! ### Closed-form derivative of the bosonic Poisson inversion -/

/-- Differentiated Poisson summation formula: closed form for the `n²`-weighted
Gaussian sum, obtained by differentiating both sides of
`Real.tsum_exp_neg_mul_int_sq` and rearranging.

For `a > 0`,
$$
\pi \sum_{n \in \mathbb{Z}} n^2 \, e^{-\pi a n^2}
\;=\; \tfrac{1}{2}\, a^{-3/2}\, \sum_{n \in \mathbb{Z}} e^{-\pi n^2 / a}
\;-\; \pi\, a^{-5/2} \sum_{n \in \mathbb{Z}} n^2 \, e^{-\pi n^2 / a}.
$$
-/
theorem tsum_n_sq_exp_neg_pi_mul_int_sq_eq {a : ℝ} (ha : 0 < a) :
    π * (∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2))
      = (1 / 2) * a ^ (-(3 / 2 : ℝ)) *
          (∑' n : ℤ, Real.exp (-π / a * (n : ℝ) ^ 2))
        - π * a ^ (-(5 / 2 : ℝ)) *
          (∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π / a * (n : ℝ) ^ 2)) := by
  sorry

end Real
