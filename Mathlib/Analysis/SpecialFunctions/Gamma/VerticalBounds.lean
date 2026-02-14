/-
Copyright (c) 2025 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Vertical decay bounds for the Gamma function

This file proves that `Γ(σ + it)` decays exponentially as `|t| → ∞` for fixed `σ`,
establishing the vertical bounds needed for Mellin-Barnes contour shifts and other
applications of the Gamma function in analytic number theory.

## Main results

* `Complex.Gamma_nat_add`: Iterated functional equation
  `Γ(z + n) = (∏ k in range n, (z + k)) * Γ(z)`.
* `Complex.norm_sq_Gamma_mul_I`: From the reflection formula,
  `‖Γ(it)‖² = π / (|t| * sinh(π|t|))`.
* `Complex.Gamma_vertical_bound`: For `n ≥ 1` and `|t| ≥ 1`,
  `‖Γ(n + it)‖ ≤ n! * 2√π * (1 + |t|)^n * exp(-π|t|/2)`.
* `Complex.Gamma_vertical_decay`: `Γ(n + it) * (1 + |t|)^d → 0` as `|t| → ∞`
  (exponential decay defeats any polynomial).

## References

* [E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*][titchmarsh1986], §4.12
* [H. Iwaniec and E. Kowalski, *Analytic Number Theory*][iwaniec2004], Appendix B
-/

open Complex Finset

noncomputable section

namespace Complex

/-- Iterated functional equation: `Γ(z + n) = (∏ k in range n, (z + k)) * Γ(z)`.

This follows by induction from `Complex.Gamma_add_one`. -/
theorem Gamma_nat_add (n : ℕ) (z : ℂ) (hz : ∀ k : ℕ, k < n → z + ↑k ≠ 0) :
    Gamma (z + ↑n) = (∏ k ∈ range n, (z + ↑k)) * Gamma z := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hm_range : ∀ k : ℕ, k < m → z + ↑k ≠ 0 :=
      fun k hk => hz k (Nat.lt_succ_of_lt hk)
    rw [Nat.cast_succ, ← add_assoc,
        Complex.Gamma_add_one _ (hz m (Nat.lt_succ_iff.mpr le_rfl)),
        ih hm_range, prod_range_succ]
    ring

/-- Triangle inequality: `‖↑k + ↑t * I‖ ≤ (↑k + 1) * (1 + |t|)`. -/
theorem norm_nat_add_mul_I_le (k : ℕ) (t : ℝ) :
    ‖(↑k : ℂ) + ↑t * I‖ ≤ (↑k + 1) * (1 + |t|) := by
  have h1 : ‖(↑k : ℂ) + ↑t * I‖ ≤ ‖(↑k : ℂ)‖ + ‖(↑t : ℂ) * I‖ := norm_add_le _ _
  have h2 : ‖(↑k : ℂ)‖ = (↑k : ℝ) := by
    simp
  have h3 : ‖(↑t : ℂ) * I‖ = |t| := by
    simp [Complex.norm_real, Complex.norm_I]
  have hk : (0 : ℝ) ≤ ↑k := Nat.cast_nonneg' k
  have ht : (0 : ℝ) ≤ |t| := abs_nonneg t
  nlinarith [mul_nonneg hk ht]

/-- Product bound: `∏ k in range n, ‖↑k + ↑t * I‖ ≤ n! * (1 + |t|)^n`. -/
theorem prod_norm_le (n : ℕ) (t : ℝ) :
    ∏ k ∈ range n, ‖(↑k : ℂ) + ↑t * I‖ ≤ ↑(n.factorial) * (1 + |t|) ^ n := by
  calc ∏ k ∈ range n, ‖(↑k : ℂ) + ↑t * I‖
      ≤ ∏ k ∈ range n, ((↑k + 1 : ℝ) * (1 + |t|)) := by
        apply Finset.prod_le_prod
        · intro k _; positivity
        · intro k _; exact norm_nat_add_mul_I_le k t
    _ = (∏ k ∈ range n, (↑k + 1 : ℝ)) * (1 + |t|) ^ n := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = ↑(n.factorial) * (1 + |t|) ^ n := by
        congr 1
        have : ∏ k ∈ range n, (↑k + 1 : ℝ) = ↑(∏ k ∈ range n, (k + 1)) := by
          rw [Nat.cast_prod]; congr 1; ext k; push_cast; ring
        rw [this, prod_range_add_one_eq_factorial]

/-- `Γ(it) ≠ 0` for `t ≠ 0`, since `it` avoids all non-positive integers. -/
theorem Gamma_pure_imag_ne_zero {t : ℝ} (ht : t ≠ 0) :
    Gamma (↑t * I) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  have him := congrArg Complex.im h
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
    add_zero, neg_im, natCast_im, neg_zero] at him
  exact ht him

/-- Conjugation symmetry: `‖Γ(-it)‖ = ‖Γ(it)‖`, from `Γ(conj z) = conj(Γ(z))`. -/
theorem norm_Gamma_neg_mul_I (t : ℝ) :
    ‖Gamma (↑(-t) * I)‖ = ‖Gamma (↑t * I)‖ := by
  have h1 : (↑(-t) : ℂ) * I = starRingEnd ℂ (↑t * I) := by
    simp [Complex.conj_ofReal, map_mul, conj_I, ofReal_neg]
  rw [h1, Complex.Gamma_conj, RCLike.norm_conj]

/-- Norm squared of `Γ(it)` from the reflection formula:
`‖Γ(it)‖² = π / (|t| * sinh(π|t|))`.

From `Γ(z)Γ(1-z) = π/sin(πz)` at `z = it`, using `sin(πit) = i · sinh(πt)`
and the conjugation symmetry `‖Γ(-it)‖ = ‖Γ(it)‖`. -/
theorem norm_sq_Gamma_mul_I (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma (↑t * I)‖ ^ 2 = Real.pi / (|t| * Real.sinh (Real.pi * |t|)) := by
  have hit_ne : (↑t : ℂ) * I ≠ 0 := by
    intro h; apply ht
    have := congr_arg Complex.im h
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, zero_im] at this
    exact this
  have hnit_ne : (↑(-t) : ℂ) * I ≠ 0 := by
    rw [ofReal_neg, neg_mul]; exact neg_ne_zero.mpr hit_ne
  have h_one_sub : (↑(-t) : ℂ) * I + 1 = 1 - ↑t * I := by push_cast; ring
  have hfunc := Complex.Gamma_add_one _ hnit_ne
  rw [h_one_sub] at hfunc
  have hprod : Gamma (↑t * I) * Gamma (↑(-t) * I) =
      Gamma (↑t * I) * Gamma (1 - ↑t * I) / (↑(-t) * I) := by
    rw [mul_div_assoc]
    congr 1
    rw [hfunc, mul_comm (↑(-t) * I) _, mul_div_cancel_right₀]
    exact hnit_ne
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (↑t * I)
  rw [hrefl] at hprod
  have hsin : sin (↑Real.pi * (↑t * I)) = sinh (↑Real.pi * ↑t) * I := by
    have : ↑Real.pi * (↑t * I) = (↑Real.pi * ↑t) * I := by ring
    rw [this, sin_mul_I]
  rw [hsin] at hprod
  have hdenom_eq : sinh (↑Real.pi * ↑t) * I * ((↑(-t) : ℂ) * I) =
      ↑t * sinh (↑Real.pi * ↑t) := by
    have calc1 : sinh (↑Real.pi * ↑t) * I * ((↑(-t) : ℂ) * I) =
        sinh (↑Real.pi * ↑t) * (↑(-t) : ℂ) * (I * I) := by ring
    rw [calc1, I_mul_I, ofReal_neg]
    ring
  have hprod2 : Gamma (↑t * I) * Gamma (↑(-t) * I) =
      ↑Real.pi / (↑t * sinh (↑Real.pi * ↑t)) := by
    rw [hprod, div_div, hdenom_eq]
  have key : ‖Gamma (↑t * I)‖ ^ 2 =
      ‖(↑Real.pi : ℂ) / (↑t * sinh (↑Real.pi * ↑t))‖ := by
    calc ‖Gamma (↑t * I)‖ ^ 2
        = ‖Gamma (↑t * I)‖ * ‖Gamma (↑t * I)‖ := sq _
      _ = ‖Gamma (↑t * I)‖ * ‖Gamma (↑(-t) * I)‖ := by
          rw [norm_Gamma_neg_mul_I]
      _ = ‖Gamma (↑t * I) * Gamma (↑(-t) * I)‖ :=
          (norm_mul _ _).symm
      _ = ‖(↑Real.pi : ℂ) / (↑t * sinh (↑Real.pi * ↑t))‖ := by
          rw [hprod2]
  have hsinh_cast : sinh ((↑Real.pi : ℂ) * (↑t : ℂ)) = ↑(Real.sinh (Real.pi * t)) := by
    rw [← ofReal_mul, ofReal_sinh]
  rw [key, hsinh_cast]
  rw [← ofReal_mul t]
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_mul, Real.abs_sinh]

/-- For `x ≥ 1`, `sinh(x) ≥ exp(x) / 4`.
From `sinh(x) = (exp(x) - exp(-x)) / 2` and `exp(x) ≥ e > 2` for `x ≥ 1`. -/
private lemma sinh_ge_exp_div_four {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have hexp_ge_two : 2 ≤ Real.exp x := by
    have : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith [Real.exp_le_exp.mpr hx]
  have : Real.exp (-x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  linarith

/-- Norm bound for `Γ` on the imaginary axis:
`‖Γ(it)‖ ≤ 2√π * exp(-π|t|/2)` for `|t| ≥ 1`. -/
private lemma norm_Gamma_pure_imag_le (t : ℝ) (ht : 1 ≤ |t|) :
    ‖Gamma (↑t * I)‖ ≤ 2 * Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2) := by
  have ht_ne : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have habs_pos : 0 < |t| := by linarith
  have hpi_pos := Real.pi_pos
  have hsinh_pos : 0 < Real.sinh (Real.pi * |t|) := by
    rw [Real.sinh_pos_iff]; positivity
  have hsq := norm_sq_Gamma_mul_I t ht_ne
  have hpi_t_ge : 1 ≤ Real.pi * |t| := by
    calc Real.pi * |t| ≥ Real.pi * 1 := by nlinarith
      _ = Real.pi := mul_one _
      _ ≥ 1 := by linarith [Real.pi_gt_three]
  have hsinh_bound := sinh_ge_exp_div_four hpi_t_ge
  suffices h : ‖Gamma (↑t * I)‖ ^ 2 ≤
      (2 * Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2)) ^ 2 by
    have hrhs_nn : 0 ≤ 2 * Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2) := by positivity
    nlinarith [norm_nonneg (Gamma (↑t * I)),
      sq_nonneg (‖Gamma (↑t * I)‖ - 2 * Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2))]
  have hrhs_eq : (2 * Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2)) ^ 2 =
      4 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
    have hexp_sq : Real.exp (-Real.pi * |t| / 2) ^ 2 = Real.exp (-(Real.pi * |t|)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [mul_pow, mul_pow, Real.sq_sqrt hpi_pos.le, hexp_sq]; ring
  rw [hsq, hrhs_eq]
  have hdenom_lb : Real.exp (Real.pi * |t|) / 4 ≤ |t| * Real.sinh (Real.pi * |t|) :=
    calc Real.exp (Real.pi * |t|) / 4
        ≤ Real.sinh (Real.pi * |t|) := hsinh_bound
      _ = 1 * Real.sinh (Real.pi * |t|) := (one_mul _).symm
      _ ≤ |t| * Real.sinh (Real.pi * |t|) := by nlinarith [hsinh_pos]
  rw [Real.exp_neg]
  have : 4 * Real.pi * (Real.exp (Real.pi * |t|))⁻¹ =
      Real.pi / (Real.exp (Real.pi * |t|) / 4) := by field_simp
  rw [this]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom_lb

/-- **Main vertical bound**: For `n ≥ 1` and `|t| ≥ 1`:
`‖Γ(n + it)‖ ≤ n! * 2√π * (1 + |t|)^n * exp(-π|t|/2)`.

This combines the iterated functional equation `Gamma_nat_add` (which gives a
polynomial factor `n! * (1+|t|)^n`) with the exponential decay on the imaginary
axis from the reflection formula (`norm_Gamma_pure_imag_le`). The natural constant
`2√π` is slightly weaker than the sometimes-stated `√(2π)` but sufficient for
exponential decay. -/
theorem Gamma_vertical_bound (n : ℕ) (_hn : 1 ≤ n) (t : ℝ) (ht : 1 ≤ |t|) :
    ‖Gamma (↑n + ↑t * I)‖ ≤
      ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
      (1 + |t|) ^ n * Real.exp (-Real.pi * |t| / 2) := by
  have ht_ne : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hz : ∀ k : ℕ, k < n → (↑t * I : ℂ) + ↑k ≠ 0 := by
    intro k _
    apply ne_of_apply_ne Complex.im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, natCast_im, zero_im, ne_eq]
    exact ht_ne
  rw [show (↑n : ℂ) + ↑t * I = ↑t * I + ↑n from by ring,
      Gamma_nat_add n (↑t * I) hz, norm_mul, norm_prod]
  have hprod_rw : ∏ k ∈ range n, ‖(↑t * I : ℂ) + ↑k‖ =
      ∏ k ∈ range n, ‖(↑k : ℂ) + ↑t * I‖ :=
    Finset.prod_congr rfl fun k _ => by
      rw [show (↑t * I : ℂ) + ↑k = (↑k : ℂ) + ↑t * I from by ring]
  rw [hprod_rw]
  calc (∏ k ∈ range n, ‖(↑k : ℂ) + ↑t * I‖) * ‖Gamma (↑t * I)‖
      ≤ (↑(n.factorial) * (1 + |t|) ^ n) *
        (2 * Real.sqrt Real.pi * Real.exp (-Real.pi * |t| / 2)) :=
        mul_le_mul (prod_norm_le n t) (norm_Gamma_pure_imag_le t ht)
          (norm_nonneg _) (by positivity)
    _ = ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
        (1 + |t|) ^ n * Real.exp (-Real.pi * |t| / 2) := by ring

/-- Corollary: `Γ` decays exponentially on vertical lines, faster than any polynomial.

More precisely, `‖Γ(n + it)‖ * (1 + |t|)^d → 0` as `t → ∞` for any `d`. -/
theorem Gamma_vertical_decay (n : ℕ) (hn : 1 ≤ n) (d : ℕ) :
    Filter.Tendsto (fun t : ℝ => ‖Gamma (↑n + ↑t * I)‖ * (1 + |t|) ^ (d : ℝ))
      Filter.atTop (nhds 0) := by
  open Filter Real in
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  set C := ↑(n.factorial) * (2 * Real.sqrt Real.pi) * (2 : ℝ) ^ (n + d)
  set g : ℝ → ℝ := fun t => C * (t ^ (↑(n + d) : ℝ) * Real.exp (-(Real.pi / 2) * t))
  apply squeeze_zero'
  · filter_upwards with t
    exact mul_nonneg (norm_nonneg _) (rpow_nonneg (by linarith [abs_nonneg t]) _)
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have ht_pos : 0 < t := by linarith
    have ht_abs : |t| = t := abs_of_pos ht_pos
    have h_bound := Gamma_vertical_bound n hn t (by rw [ht_abs]; linarith)
    change ‖Gamma (↑n + ↑t * I)‖ * (1 + |t|) ^ (d : ℝ) ≤ g t
    rw [rpow_natCast]
    have h1 : ‖Gamma (↑n + ↑t * I)‖ * (1 + |t|) ^ d
        ≤ ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
          (1 + |t|) ^ n * Real.exp (-Real.pi * |t| / 2) * (1 + |t|) ^ d :=
      mul_le_mul_of_nonneg_right h_bound (by positivity)
    have h2 : ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
          (1 + |t|) ^ n * Real.exp (-Real.pi * |t| / 2) * (1 + |t|) ^ d
        = ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
          (1 + t) ^ (n + d) * Real.exp (-Real.pi * t / 2) := by
      rw [ht_abs, pow_add]; ring
    have h3 : (1 + t) ^ (n + d) ≤ (2 * t) ^ (n + d) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (n + d)
    have h4 : -Real.pi * t / 2 = -(Real.pi / 2) * t := by ring
    have h5 : ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
          (1 + t) ^ (n + d) * Real.exp (-Real.pi * t / 2)
        ≤ ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
          (2 * t) ^ (n + d) * Real.exp (-(Real.pi / 2) * t) := by
      rw [h4]
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left h3
        positivity
      · exact le_of_lt (Real.exp_pos _)
    have h6 : ↑(n.factorial) * (2 * Real.sqrt Real.pi) *
          (2 * t) ^ (n + d) * Real.exp (-(Real.pi / 2) * t)
        = g t := by
      change _ = C * (t ^ (↑(n + d) : ℝ) * Real.exp (-(Real.pi / 2) * t))
      rw [mul_pow, rpow_natCast]; ring
    linarith
  · change Filter.Tendsto g Filter.atTop (nhds 0)
    have h_tend : Filter.Tendsto
        (fun t : ℝ => t ^ (↑(n + d) : ℝ) * Real.exp (-(Real.pi / 2) * t))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ↑(n + d) (Real.pi / 2) hpi2
    have : Filter.Tendsto
        (fun t => C * (t ^ (↑(n + d) : ℝ) * Real.exp (-(Real.pi / 2) * t)))
        Filter.atTop (nhds (C * 0)) :=
      tendsto_const_nhds.mul h_tend
    simp only [mul_zero] at this
    exact this

end Complex

end
