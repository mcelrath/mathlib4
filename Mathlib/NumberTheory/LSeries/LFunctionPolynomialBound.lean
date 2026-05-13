/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Polynomial growth of `L'/L` in vertical strips

For a Dirichlet character `χ`, the logarithmic derivative `-L'(χ, s)/L(χ, s)` grows at most
polynomially in `|Im s|` as `|Im s| → ∞`, uniformly in any vertical strip
`σ_min ≤ Re s ≤ σ_max` that avoids zeros of `L(χ, ·)` (and the pole at `s = 1` when `χ` is
trivial).

This bound is the analytic input used in the **Weil explicit formula** (residue identity
applied to `−L'/L`): the rectangular contour can be closed because the integrand decays as
`|Im s| → ∞`.

## Main statements

* `DirichletCharacter.LFunction_logDeriv_polynomial_bound` (nontrivial `χ`).
* `DirichletCharacter.LFunctionTrivChar₁_logDeriv_polynomial_bound` (trivial-twist case,
  using the pole-removed `LFunctionTrivChar₁`).

## References

* Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12 (Hadamard factorisation and
  the bound `L'/L(s) = O(log² |Im s|)` in fixed vertical strips).
* Iwaniec–Kowalski, *Analytic Number Theory*, §5.6 (functional equation and convexity bounds).

## Implementation notes

A full proof requires (i) the **Hadamard factorisation** of an entire function of order 1
applied to the entire function `(s−1) · L(χ, s)` (resp. `L(χ, s)` for nontrivial `χ`), and
(ii) zero-counting bounds for `L(χ, ·)` in horizontal strips. Neither ingredient is currently
available in Mathlib, so the result is stated with `sorry` and consumed downstream. The
classical bound is `‖-L'(χ, s)/L(χ, s)‖ ≤ C · (log (2 + |Im s|))^2`, which is `O(|Im s|^ε)`
for every `ε > 0`; we give the weaker polynomial form to keep the statement elementary.
-/

open Complex

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- **Polynomial bound on `-L'/L` in a vertical strip** (nontrivial character).

If `χ` is a nontrivial Dirichlet character mod `N`, then on any vertical strip
`σ_min ≤ Re s ≤ σ_max` whose intersection with the zero set of `L(χ, ·)` is bounded away
from the line at imaginary infinity (concretely: stays at distance `≥ δ > 0` from every
zero), the logarithmic derivative `-L'(χ, s)/L(χ, s)` is bounded by a polynomial in
`|Im s|`.

This is the analytic input used to close the rectangular contour in the Weil explicit
formula. Classical reference: Davenport, *Multiplicative Number Theory*, Ch. 12. -/
theorem LFunction_logDeriv_polynomial_bound (hχ : χ ≠ 1)
    (σ_min σ_max : ℝ) (hσ : σ_min ≤ σ_max) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ s : ℂ,
      σ_min ≤ s.re → s.re ≤ σ_max →
      (∀ ρ : ℂ, LFunction χ ρ = 0 → δ ≤ ‖s - ρ‖) →
      ‖-deriv (LFunction χ) s / LFunction χ s‖ ≤ C * (1 + |s.im|) ^ k := by
  sorry

/-- **Polynomial bound on `-L'/L` in a vertical strip** (trivial-twist case).

For the trivial character (and any character via `LFunctionTrivChar₁`, which removes the
pole at `s = 1`), the function `s ↦ (s − 1) · L(χ, s)` is entire, and its logarithmic
derivative is polynomially bounded on vertical strips at positive distance from its
zeros. -/
theorem LFunctionTrivChar₁_logDeriv_polynomial_bound (n : ℕ) [NeZero n]
    (σ_min σ_max : ℝ) (hσ : σ_min ≤ σ_max) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ s : ℂ,
      σ_min ≤ s.re → s.re ≤ σ_max →
      (∀ ρ : ℂ, LFunctionTrivChar₁ n ρ = 0 → δ ≤ ‖s - ρ‖) →
      ‖-deriv (LFunctionTrivChar₁ n) s / LFunctionTrivChar₁ n s‖ ≤ C * (1 + |s.im|) ^ k := by
  sorry

end DirichletCharacter
