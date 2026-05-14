/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.VerticalBounds
public import Mathlib.Analysis.Complex.PhragmenLindelof

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

private lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  rw [cos]
  have h1 : ‖(exp (z * I) + exp (-z * I)) / 2‖ ≤
      (‖exp (z * I)‖ + ‖exp (-z * I)‖) / 2 := by
    rw [norm_div]
    simp only [norm_ofNat]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) two_pos.le
  have h2 : ‖exp (z * I)‖ = Real.exp (-z.im) := by
    rw [norm_exp, mul_I_re]
  have h3 : ‖exp (-z * I)‖ = Real.exp z.im := by
    rw [norm_exp]
    simp
  rw [h2, h3] at h1
  calc ‖(exp (z * I) + exp (-z * I)) / 2‖
      ≤ (Real.exp (-z.im) + Real.exp z.im) / 2 := h1
    _ = Real.cosh z.im := by rw [Real.cosh_eq]; ring
    _ ≤ Real.exp |z.im| := by
        rw [Real.cosh_eq]
        rcases lt_or_ge z.im 0 with h | h
        · rw [abs_of_neg h]
          have : Real.exp z.im ≤ Real.exp (-z.im) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith [Real.exp_pos (-z.im)]
        · rw [abs_of_nonneg h]
          have : Real.exp (-z.im) ≤ Real.exp z.im :=
            Real.exp_le_exp.mpr (by linarith)
          linarith [Real.exp_pos z.im]

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

/-- Exponential-type bound for `riemannZeta s * (s - 1)`.

The function `s ↦ riemannZeta s * (s - 1)` is entire (the simple pole of `riemannZeta`
at `s = 1` with residue 1 is cancelled by the zero of `s - 1`) and satisfies a uniform
exponential-type estimate `‖riemannZeta s * (s - 1)‖ ≤ exp(C * ‖s‖)`.

*Proof sketch (uses existing Mathlib primitives, derivation not yet formalized)*:
- For `Re s ≥ 3/2`: `‖ζ(s)‖ ≤ ζ(3/2)` (Dirichlet series), so
  `‖ζ(s)(s-1)‖ ≤ ζ(3/2) * (‖s‖ + 1) ≤ exp(C ‖s‖)`.
- For `Re s < 3/2`: invert `riemannZeta_one_sub` to write `ζ(s)` in terms of `ζ(1-s)`
  (which has `Re(1-s) > -1/2`, bounded by the right-half-plane case), multiplied by
  `2(2π)^{s-1} Γ(1-s) cos(π(1-s)/2)`.  By `Complex.Gamma_vertical_bound`,
  `|Γ(1-s)| ≤ C(1+|t|)^{1-σ} exp(-π|t|/2)`, and `|cos(π(1-s)/2)| ≤ exp(π|t|/2)`.
  The exponential factors cancel leaving `|ζ(s)| ≤ C exp(C|s|)`.

This lemma is the **only missing primitive** for the proof of
`riemannZeta_norm_le_polynomial_in_vertical_strip`; all other steps
(`PhragmenLindelof.vertical_strip`, `Gamma_vertical_bound`, `riemannZeta_one_sub`,
`riemannZeta_norm_le_polynomial_of_one_lt_re`) are already in Mathlib. -/
private lemma riemannZeta_mul_sub_one_norm_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖riemannZeta s * (s - 1)‖ ≤ Real.exp (C * ‖s‖) := by
  sorry

/-!
## Vertical-strip polynomial bound (Phragmén–Lindelöf interpolation)

The bound `riemannZeta_norm_le_polynomial_of_one_lt_re` covers only the right half-plane
`Re s > 1`. The cl44 / Mellin–Barnes correction-integral estimates additionally require a
polynomial bound on `‖ζ(σ + i t)‖` in a vertical strip that crosses `Re s = 1`, in
particular through the critical line `Re s = 1/2`.

The classical proof has three ingredients:

1. **Right edge** (`Re s = 1 + δ`): `‖ζ(s)‖` is uniformly bounded (constant in `Im s`),
   from `riemannZeta_norm_le_polynomial_of_one_lt_re`.
2. **Left edge** (`Re s = -δ`): via the functional equation
   `ζ(1 - s) = 2 (2π)^{-s} Γ(s) cos(π s / 2) ζ(s)` (Mathlib: `riemannZeta_one_sub`),
   together with the Stirling vertical bound `Complex.Gamma_vertical_bound` and the
   trivial estimate `|cos(π s / 2)| ≤ exp(π |Im s| / 2)`. The exponential decay of `Γ`
   on vertical lines (factor `exp(-π |t| / 2)`) cancels the exponential growth of `cos`,
   leaving a polynomial bound `‖ζ(-δ + i t)‖ = O((1 + |t|)^{1 + δ})`.
3. **Interpolation**: apply `PhragmenLindelof.vertical_strip` to the auxiliary function
   `g(s) := ζ(s) · (s - 1) / (1 + s)^k` for a suitable integer `k`, which absorbs both
   edge bounds into a single constant majorant. The conclusion transfers back to `ζ`
   via the polynomial factor `(1 + s)^k / (s - 1)`.

The statement below packages the result needed by Mellin–Barnes shift arguments that
cross the critical line. The proof is left as `sorry` pending the three ingredient
lemmas above; each ingredient corresponds to a Mathlib primitive that already exists
(items 1, 2, 3 cited inline), and the assembly is a one-step PL application.

This level of generality (some polynomial bound) is sufficient for the cl44 axiom
discharge: the Mellin–Barnes correction integrand carries a Schwartz test function
which provides rapid decay, so any polynomial bound on `ζ` closes the estimate.
-/

/-- **Polynomial bound on `ζ` in a vertical strip crossing the critical line.**

For any `δ > 0`, there exist constants `C ≥ 0` and `k : ℕ` such that
`‖ζ(s)‖ ≤ C · (1 + |Im s|)^k` for all `s` with `-δ ≤ Re s ≤ 1 + δ` and `|s - 1| ≥ δ`
(the exclusion of a neighborhood of the pole at `s = 1` is necessary).

This is the Phragmén–Lindelöf interpolation between the trivial bound at `Re s = 1 + δ`
(from `riemannZeta_norm_le_polynomial_of_one_lt_re`) and the bound at `Re s = -δ`
derived from the functional equation `riemannZeta_one_sub` and the Stirling vertical
bound `Complex.Gamma_vertical_bound`.

Load-bearing for cl44 Mellin–Barnes correction-integral axioms (MellinBarnesShift line
220, EtaResidue line 372) which require a polynomial bound to absorb against the rapid
decay of a Schwartz test function on the critical-line contour. -/
theorem riemannZeta_norm_le_polynomial_in_vertical_strip
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s : ℂ,
      -δ ≤ s.re → s.re ≤ 1 + δ → δ ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ k := by
  -- Use the exponential-type bound via `riemannZeta_mul_sub_one_norm_le_exp`
  -- to verify the Phragmen-Lindelof sub-exponential hypothesis on g(s) = ζ(s)*(s-1)/(s+2),
  -- then apply `PhragmenLindelof.vertical_strip` with constant edge bounds.
  -- All steps reduce to existing Mathlib primitives once
  -- `riemannZeta_mul_sub_one_norm_le_exp` is available.
  obtain ⟨C_exp, _, hC_exp_bound⟩ := riemannZeta_mul_sub_one_norm_le_exp
  obtain ⟨C_R, hC_R_nn, hC_R_bound⟩ :=
    riemannZeta_norm_le_polynomial_of_one_lt_re (σ := 1 + δ + 1) (by linarith)
  -- Full assembly via PhragmenLindelof.vertical_strip pending the edge-bound
  -- computations using riemannZeta_one_sub + Gamma_vertical_bound on the left edge.
  sorry

/-- **Critical-line specialization.**

`‖ζ(1/2 + i t)‖` is bounded by a polynomial in `|t|` for `|t| ≥ 1` (the lower bound on
`|t|` keeps `s` away from the pole at `s = 1`). Immediate corollary of
`riemannZeta_norm_le_polynomial_in_vertical_strip` with `δ = 1/2`. -/
theorem riemannZeta_norm_le_polynomial_on_critical_line :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (1/2 + t * Complex.I)‖ ≤ C * (1 + |t|) ^ k := by
  obtain ⟨C, k, hC, hbd⟩ :=
    riemannZeta_norm_le_polynomial_in_vertical_strip (δ := (1 : ℝ) / 2) (by norm_num)
  refine ⟨C, k, hC, fun t ht => ?_⟩
  have hs_re : (1/2 + (t : ℂ) * Complex.I).re = 1/2 := by simp
  have hs_im : (1/2 + (t : ℂ) * Complex.I).im = t := by simp
  rw [show |t| = |(1/2 + (t : ℂ) * Complex.I).im| from by rw [hs_im]]
  apply hbd
  · rw [hs_re]; norm_num
  · rw [hs_re]; norm_num
  · -- ‖(1/2 + t I) - 1‖ = ‖-1/2 + t I‖ ≥ 1/2, using |t| ≥ 1 ≥ 1/2 hence
    -- ‖-1/2 + t I‖² = 1/4 + t² ≥ 1/4 + 1 ≥ 1/4
    have h1 : (1/2 + (t : ℂ) * Complex.I) - 1 = -(1/2 : ℂ) + (t : ℂ) * Complex.I := by ring
    rw [h1]
    have hre : (-(1/2 : ℂ) + (t : ℂ) * Complex.I).re = -(1/2) := by simp
    have him : (-(1/2 : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have habs : (1/2 : ℝ) ≤ ‖(-(1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h := Complex.abs_re_le_norm (-(1/2 : ℂ) + (t : ℂ) * Complex.I)
      rw [hre] at h
      have : |(-(1/2 : ℝ))| = 1/2 := by norm_num
      linarith [h, this.symm ▸ h]
    exact habs

end RiemannZeta
