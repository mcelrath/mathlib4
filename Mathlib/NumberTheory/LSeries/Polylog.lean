/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.DirichletEta
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Polylogarithm Function

## Main definitions:

* `polylog`: the polylogarithm function `Li_s(z) = ∑_{n=1}^∞ z^n / n^s` for `s ∈ ℂ`, `z ∈ ℂ`.
## Main results:

* `polylog_convergent_of_norm_lt_one`: absolute convergence for `‖z‖ < 1` and all `s`.
* `polylog_convergent_of_one_lt_re`: absolute convergence for `1 < re s` and `‖z‖ ≤ 1`.
* `polylog_minus_one_eq_neg_dirichletEta`: `Li_s(-1) = -η(s)` for `1 < re s`.

## References

* Zagier, D. (2007). "The Dilogarithm Function". In Cartier et al., Frontiers in Number Theory,
  Physics, and Geometry II.
* Lewin, L. (1981). Polylogarithms and Associated Functions. North-Holland.
* NIST Digital Library of Mathematical Functions, §25.12 "Polylogarithm"

## Implementation notes

This file provides the classical complex-analytic polylogarithm, defined via power series.
Analytic continuation to the full complex plane is deferred to a future PR.

The polylogarithm generalizes the Riemann zeta function via `Li_s(1) = ζ(s)` for `1 < re s`.

For `z = -1`, the series becomes an alternating series and reduces to the Dirichlet eta function,
giving absolute convergence for `1 < re s`.

-/

noncomputable section

open Complex Filter Topology

/-! ## Definition -/

/-- The polylogarithm function `Li_s(z) = ∑_{n=1}^∞ z^n / n^s`.

This is defined as a formal power series for now. Convergence is proven separately. -/
def polylog (s z : ℂ) : ℂ := ∑' (n : ℕ+), z ^ (n : ℕ) / (n : ℂ) ^ s

/-! ## Basic properties -/

/-- The polylogarithm as an explicit `tsum`. -/
@[simp] lemma polylog_eq_tsum (s z : ℂ) :
    polylog s z = ∑' (n : ℕ+), z ^ (n : ℕ) / (n : ℂ) ^ s := rfl

/-! ## Convergence -/

/-- Absolute convergence of polylog for `‖z‖ < 1` and any `s`. -/
theorem summable_polylog_of_norm_lt_one {s z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ+ => ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖ := by
  -- Pick r with ‖z‖ < r < 1 for the geometric bound
  obtain ⟨r, hz_r, hr_one⟩ := exists_between hz
  have geom : Summable (fun n : ℕ+ => r ^ (n : ℕ)) := by
    have hr_pos : 0 < r := by linarith [norm_nonneg z, hz_r]
    have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr_pos.le]
    exact (summable_geometric_of_norm_lt_one hr_norm).comp_injective PNat.coe_injective
  have : Summable (fun n : ℕ+ => z ^ (n : ℕ) / (n : ℂ) ^ s) := by
    by_cases h : 0 ≤ s.re
    · -- Case Re s ≥ 0: bound holds for all n ≥ 1
      refine .of_norm_bounded geom ?_
      intro n
      have norm_cpow : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
        norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr n.pos) s
      calc ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖
          = ‖z‖ ^ (n : ℕ) / ‖(n : ℂ) ^ s‖ := by rw [norm_div, norm_pow]
        _ = ‖z‖ ^ (n : ℕ) / (n : ℝ) ^ s.re := by rw [norm_cpow]
        _ ≤ ‖z‖ ^ (n : ℕ) / 1 := by
            refine div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg z) _) zero_lt_one ?_
            have hn_ge_one : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr n.property
            exact Real.one_le_rpow hn_ge_one h
        _ = ‖z‖ ^ (n : ℕ) := div_one _
        _ ≤ r ^ (n : ℕ) := pow_le_pow_left₀ (norm_nonneg z) hz_r.le (n : ℕ)
    · -- Case Re s < 0: polynomial growth in n beaten by geometric decay of ‖z‖^n
      push_neg at h
      let k := Nat.ceil (-s.re)
      -- n^k * ‖z‖^n is summable (polynomial × geometric with ‖z‖ < 1)
      have hz_norm : ‖‖z‖‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg z)]
      have sum_nat : Summable (fun n : ℕ => (n : ℝ) ^ k * ‖z‖ ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one k hz_norm
      have sum_pnat : Summable (fun n : ℕ+ => (n : ℝ) ^ k * ‖z‖ ^ (n : ℕ)) :=
        sum_nat.comp_injective PNat.coe_injective
      -- Pointwise bound: ‖z^n / n^s‖ = ‖z‖^n * n^(-Re s) ≤ n^k * ‖z‖^n
      refine Summable.of_norm_bounded sum_pnat fun n => ?_
      have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr n.pos
      calc ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖
          = ‖z‖ ^ (n : ℕ) / ‖(n : ℂ) ^ s‖ := by rw [norm_div, norm_pow]
        _ = ‖z‖ ^ (n : ℕ) / (n : ℝ) ^ s.re := by
            congr 1; exact norm_cpow_eq_rpow_re_of_pos hn_pos s
        _ = ‖z‖ ^ (n : ℕ) * (n : ℝ) ^ (-s.re) := by
            rw [div_eq_mul_inv, Real.rpow_neg hn_pos.le]
        _ ≤ ‖z‖ ^ (n : ℕ) * (n : ℝ) ^ k := by
            exact mul_le_mul_of_nonneg_left (by
              have := Real.rpow_le_rpow_of_exponent_le
                (Nat.one_le_cast.mpr n.pos) (Nat.le_ceil (-s.re))
              rwa [Real.rpow_natCast] at this) (pow_nonneg (norm_nonneg z) _)
        _ = (n : ℝ) ^ k * ‖z‖ ^ (n : ℕ) := mul_comm _ _
  exact summable_norm_iff.mpr this

/-- Absolute convergence of polylog for `1 < re s` and `‖z‖ ≤ 1`. -/
theorem summable_polylog_of_one_lt_re {s z : ℂ} (hs : 1 < s.re) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ+ => ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖ := by
  have p_series_pnat : Summable (fun n : ℕ+ => 1 / ‖(n : ℂ) ^ s‖) := by
    have h_nat : Summable (fun m : ℕ => 1 / (m : ℂ) ^ s) := Complex.summable_one_div_nat_cpow.mpr hs
    have h_pnat : Summable (fun n : ℕ+ => 1 / (n : ℂ) ^ s) := by
      have := h_nat.comp_injective PNat.coe_injective
      convert this using 1
    convert summable_norm_iff.mpr h_pnat using 1
    ext n
    simp
  have : Summable (fun n : ℕ+ => z ^ (n : ℕ) / (n : ℂ) ^ s) := by
    refine .of_norm_bounded p_series_pnat ?_
    intro n
    have step1 : ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖ = ‖z‖ ^ (n : ℕ) / ‖(n : ℂ) ^ s‖ := by
      rw [norm_div, norm_pow]
    have step2 : ‖z‖ ^ (n : ℕ) ≤ 1 := by
      refine pow_le_one₀ (norm_nonneg z) hz
    rw [step1]
    exact div_le_div_of_nonneg_right step2 (norm_nonneg _)
  exact summable_norm_iff.mpr this

/-! ## Connection to Riemann Zeta -/

/-- At `z = 1`, the polylog reduces to the Riemann zeta function for `1 < re s`. -/
theorem polylog_one_eq_zeta (s : ℂ) (hs : 1 < s.re) :
    polylog s 1 = riemannZeta s := by
  rw [polylog_eq_tsum, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  simp only [one_pow, one_div]
  symm
  convert Equiv.pnatEquivNat.symm.tsum_eq (fun (n : ℕ+) => 1 / (n : ℂ) ^ s) using 2
  · funext n; simp [Equiv.pnatEquivNat]
  · funext n; rw [one_div]

/-! ## Special value at z = -1 (Dirichlet eta) -/

/-- The Dirichlet eta function equals the alternating series for Re(s) > 1.

    For Re(s) > 1, both the alternating series and the Dirichlet eta function converge
    absolutely and equal (1 - 2^(1-s)) ζ(s). -/
private theorem dirichletEta_eq_alternating_series (s : ℂ) (hs : 1 < s.re) :
    DirichletEta.dirichletEta s = ∑' (n : ℕ+), (-1) ^ ((n : ℕ) - 1) / (n : ℂ) ^ s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [DirichletEta.dirichletEta_ne_one s hs1]
  exact (DirichletEta.alternating_zeta_formula hs).symm

/-- For `z = -1`, the polylog equals the negative of the Dirichlet eta function.

    The alternating series Li_s(-1) = Σ_{n=1}^∞ (-1)^n / n^s = -Σ_{n=1}^∞ (-1)^(n-1) / n^s
    converges absolutely for Re(s) > 1 and equals -η(s), where η is the Dirichlet eta function.

    Equivalently: Li_s(-1) = (2^(1-s) - 1) ζ(s) for Re(s) > 1. -/
theorem polylog_minus_one_eq_neg_dirichletEta (s : ℂ) (hs : 1 < s.re) :
    polylog s (-1) = -DirichletEta.dirichletEta s := by
  rw [dirichletEta_eq_alternating_series s hs, polylog_eq_tsum, ← tsum_neg]
  refine tsum_congr fun n => ?_
  have : (-1 : ℂ) ^ (n : ℕ) = (-1) ^ ((n : ℕ) - 1) * (-1) := by
    have h := pow_succ (-1 : ℂ) ((n : ℕ) - 1)
    convert h using 2
    have := n.pos; omega
  simp [this, neg_div]
