/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Polynomial bounds on `riemannZeta` in vertical strips

In the half-plane of absolute convergence `Re s > 1`, the Dirichlet series
`ζ(s) = ∑ 1/n^s` is uniformly bounded on any vertical line by the corresponding sum of
absolute values of the terms at `Re s`. This yields a trivial (constant in `t`)
polynomial bound for `‖ζ(σ + i t)‖` in any closed right half-plane `Re s ≥ σ > 1`,
which is the analytic input needed to close a rectangular contour in the right
half-plane when proving Mellin–Barnes / Perron-style identities for arithmetic
functions whose generating series factor through `ζ`.

## Main statements

* `riemannZeta_norm_le_tsum_norm_term`: for `1 < σ` and `σ ≤ Re s`,
  `‖ζ(s)‖ ≤ ∑' n, ‖term 1 (σ : ℂ) n‖`. The right-hand side is a finite positive real
  depending only on `σ` (it equals `∑ 1/n^σ`, i.e. the real value of `ζ(σ)`).
* `riemannZeta_norm_le_polynomial_of_one_lt_re`: the same bound restated as a
  polynomial bound `‖ζ(s)‖ ≤ C * (1 + |Im s|)^0` (independent of `Im s`) on the closed
  half-plane `Re s ≥ σ` for any `σ > 1`.

The genuine Lindelöf-type bound `‖ζ(σ + i t)‖ = O(|t|^{(1-σ)/2 + ε})` in the critical
strip `0 < σ ≤ 1` requires Phragmén–Lindelöf interpolation and is **not** treated here;
see the references for the classical proof. The bounds in this file suffice for any
Mellin–Barnes argument whose contour stays in `Re s > 1`.

## References

* Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §5.1.
* Iwaniec–Kowalski, *Analytic Number Theory*, §5.1.
-/

open Complex LSeries

namespace RiemannZeta

/-- **Trivial bound on `ζ` in the half-plane of absolute convergence.**

For `1 < σ` and `σ ≤ Re s`,
`‖ζ(s)‖ ≤ ∑' n, ‖LSeries.term 1 (σ : ℂ) n‖`.

The right-hand side is a finite positive real (it equals the real value of `ζ(σ)`,
which is the convergent Dirichlet series `∑ 1/n^σ`). -/
theorem riemannZeta_norm_le_tsum_norm_term
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : (σ : ℂ).re ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ := by
  have hσs : 1 < s.re := lt_of_lt_of_le (by simpa using hσ) hs
  have hσc : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [← LSeries_one_eq_riemannZeta hσs]
  have hsum_s : Summable (fun n => ‖term (1 : ℕ → ℂ) s n‖) :=
    (LSeriesSummable_one_iff.mpr hσs).norm
  have hsum_σ : Summable (fun n => ‖term (1 : ℕ → ℂ) (σ : ℂ) n‖) :=
    (LSeriesSummable_one_iff.mpr hσc).norm
  have h_termwise : ∀ n,
      ‖term (1 : ℕ → ℂ) s n‖ ≤ ‖term (1 : ℕ → ℂ) (σ : ℂ) n‖ :=
    fun n => norm_term_le_of_re_le_re (1 : ℕ → ℂ) hs n
  calc ‖LSeries 1 s‖
      ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ := norm_tsum_le_tsum_norm hsum_s
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) (σ : ℂ) n‖ :=
          hsum_s.tsum_le_tsum h_termwise hsum_σ

/-- **Polynomial (constant) bound on `ζ` in any closed right half-plane `Re s ≥ σ` with
`σ > 1`.**

The bound is independent of `Im s`, equivalently a polynomial bound of degree `0`. This
is the form consumed by Mellin–Barnes correction-integral estimates whose contour stays
in `Re s > 1`. -/
theorem riemannZeta_norm_le_polynomial_of_one_lt_re
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ ≤ s.re → ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (0 : ℕ) := by
  refine ⟨∑' n, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖, ?_, ?_⟩
  · exact tsum_nonneg (fun _ => norm_nonneg _)
  · intro s hs
    have hcast : ((σ : ℂ)).re ≤ s.re := by simpa using hs
    simpa using riemannZeta_norm_le_tsum_norm_term hσ hcast

end RiemannZeta
