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
public import Mathlib.Analysis.Complex.RemovableSingularity

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
* `riemannZeta_norm_le_polynomial_in_vertical_strip`: for any `δ > 0` there exist
  `C ≥ 0` and `k : ℕ` such that `‖ζ(s)‖ ≤ C * (1 + |Im s|)^k` for all `s` with
  `-δ ≤ Re s ≤ 1 + δ` and `‖s - 1‖ ≥ δ`.

## References

* Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §5.1.
* Iwaniec–Kowalski, *Analytic Number Theory*, §5.1.
-/

open Complex LSeries MeasureTheory Set Filter

open scoped Topology Real

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
    rw [norm_exp]; simp
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

/-!
## Helper lemmas for the vertical-strip bound
-/

/-- `‖Γ(σ + it)‖ ≤ Γ(σ)` for `σ > 0`. Proved via the Euler integral representation:
`|∫ exp(-x) * x^(σ+it-1) dx| ≤ ∫ exp(-x) * x^(σ-1) dx = Γ(σ)`,
using `|x^it| = 1` for real `x > 0`. -/
private lemma norm_Gamma_le_realGamma {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖Complex.Gamma (↑σ + ↑t * I)‖ ≤ Real.Gamma σ := by
  have hre : (↑σ + ↑t * I : ℂ).re = σ := by simp
  rw [Complex.Gamma_eq_integral (by rw [hre]; exact hσ)]
  rw [Real.Gamma_eq_integral hσ]
  calc ‖Complex.GammaIntegral (↑σ + ↑t * I)‖
      ≤ ∫ x : ℝ in Ioi 0,
          ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ ((↑σ + ↑t * I) - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (σ - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx_pos : (0 : ℝ) < x := hx
        show ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ ((↑σ + ↑t * I : ℂ) - 1)‖ =
            Real.exp (-x) * x ^ (σ - 1)
        have hexp_norm : ‖(↑(Real.exp (-x)) : ℂ)‖ = Real.exp (-x) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        have hcpow_norm : ‖(↑x : ℂ) ^ ((↑σ + ↑t * I : ℂ) - 1)‖ = x ^ (σ - 1) := by
          rw [show (↑σ + ↑t * I : ℂ) - 1 = ↑(σ - 1) + ↑t * I from by push_cast; ring]
          rw [norm_cpow_eq_rpow_re_of_pos hx_pos]
          simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                Complex.ofReal_im, Complex.I_im]
        rw [norm_mul, hexp_norm, hcpow_norm]

/-- **Polynomial bound on `ζ` in a vertical strip crossing the critical line.**

For any `δ > 0`, there exist constants `C ≥ 0` and `k : ℕ` such that
`‖ζ(s)‖ ≤ C · (1 + |Im s|)^k` for all `s` with `-δ ≤ Re s ≤ 1 + δ` and `|s - 1| ≥ δ`.

**Proof outline (for the pending formalization)**:
1. Define the auxiliary entire function `g(s) := ζ(s)*(s-1) / (s + (δ+2))^N` where
   `N = ⌊1+δ⌋₊ + 1`. The `s-1` factor removes the pole of `ζ`; the denominator absorbs
   polynomial growth.
2. **Right edge** `Re s = δ+2 > 1`: `|ζ(s)| ≤ C_R` by `riemannZeta_norm_le_polynomial_of_one_lt_re`.
3. **Left edge** `Re s = -δ-1`: via `riemannZeta_one_sub` (Mathlib FE), `Re(1-s) = 2+δ > 1`,
   so `|ζ(1-s)| ≤ C_R`; the FE bound gives `|ζ(s)| ≤ C_L (1+|t|)^N` using
   `Gamma_vertical_bound` + `norm_cos_le_exp_abs_im` (exponential factors cancel).
4. **PL IsBigO condition**: `(1+|t|)^N ≤ exp(N/c · exp(c·|t|))` for any `c > 0`
   (since `(1+|t|) ≤ exp(|t|)` and `|t| ≤ exp(c·|t|)/c`).
5. Apply `PhragmenLindelof.vertical_strip` on `{-δ-1 ≤ Re s ≤ δ+2}` to bound `g`,
   recover `ζ` via `|ζ(s)| = |g(s)| * |s+(δ+2)|^N / |s-1| ≤ (C/δ) * (max-norm)^N`.

All ingredients exist in Mathlib; the assembly is routine but requires ~80 Lean lines of
algebraic glue involving `differentiableOn_update_limUnder_of_bddAbove` (for the entirety
of `ζ(s)*(s-1)`) and `Asymptotics.IsBigO.of_bound` (for the IsBigO step).

This sorry is the only remaining obligation in this file. The `norm_Gamma_le_realGamma`
helper (proved above) is the hardest new ingredient; all others cite existing Mathlib lemmas. -/
theorem riemannZeta_norm_le_polynomial_in_vertical_strip
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s : ℂ,
      -δ ≤ s.re → s.re ≤ 1 + δ → δ ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ k := by
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
  · have h1 : (1/2 + (t : ℂ) * Complex.I) - 1 = -(1/2 : ℂ) + (t : ℂ) * Complex.I := by ring
    rw [h1]
    have hre : (-(1/2 : ℂ) + (t : ℂ) * Complex.I).re = -(1/2) := by simp
    have habs : (1/2 : ℝ) ≤ ‖(-(1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h := Complex.abs_re_le_norm (-(1/2 : ℂ) + (t : ℂ) * Complex.I)
      rw [hre] at h
      have : |(-(1/2 : ℝ))| = 1/2 := by norm_num
      linarith [h, this.symm ▸ h]
    exact habs

end RiemannZeta
