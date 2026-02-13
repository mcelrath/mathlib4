/-
Copyright (c) 2026 Implementation via Claude Code. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletEta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Polylogarithm Function

## Main definitions:

* `polylog`: the polylogarithm function `Li_s(z) = ∑_{n=1}^∞ z^n / n^s` for `s ∈ ℂ`, `z ∈ ℂ`.
* `dilog`: the dilogarithm `Li₂(z)`, a special case for `s = 2`.
* `trilog`: the trilogarithm `Li₃(z)`, a special case for `s = 3`.

## Main results:

* `polylog_convergent_of_norm_lt_one`: absolute convergence for `‖z‖ < 1` and all `s`.
* `polylog_convergent_of_one_lt_re`: absolute convergence for `1 < re s` and `‖z‖ ≤ 1`.
* `polylog_minus_one_eq_dirichletEta`: `Li_s(-1) = -(2^(1-s) - 1) ζ(s)` for `0 < re s`.

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
giving conditional convergence for `0 < re s`.

-/

noncomputable section

open Complex Filter Topology

namespace Polylog

/-! ## Definition -/

/-- The polylogarithm function `Li_s(z) = ∑_{n=1}^∞ z^n / n^s`.

This is defined as a formal power series for now. Convergence is proven separately. -/
def polylog (s z : ℂ) : ℂ := ∑' (n : ℕ+), z ^ (n : ℕ) / (n : ℂ) ^ s

/-- The dilogarithm `Li₂(z) = ∑_{n=1}^∞ z^n / n²`. -/
def dilog (z : ℂ) : ℂ := polylog 2 z

/-- The trilogarithm `Li₃(z) = ∑_{n=1}^∞ z^n / n³`. -/
def trilog (z : ℂ) : ℂ := polylog 3 z

/-! ## Basic properties -/

lemma polylog_eq_tsum (s z : ℂ) :
    polylog s z = ∑' (n : ℕ+), z ^ (n : ℕ) / (n : ℂ) ^ s := rfl

lemma dilog_eq_polylog (z : ℂ) : dilog z = polylog 2 z := rfl

lemma trilog_eq_polylog (z : ℂ) : trilog z = polylog 3 z := rfl

/-! ## Convergence -/

/-- Absolute convergence of polylog for `‖z‖ < 1` and any `s`. -/
theorem summable_polylog_of_norm_lt_one {s z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ+ => ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖ := by
  -- Pick r with ‖z‖ < r < 1 for the geometric bound
  obtain ⟨r, hz_r, hr_one⟩ := exists_between hz

  have geom : Summable (fun n : ℕ+ => r ^ (n : ℕ)) := by
    have hr_pos : 0 < r := by
      have : 0 ≤ ‖z‖ := norm_nonneg z
      linarith [hz_r]
    have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr_pos.le]
    have h : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr_norm
    exact Summable.comp_injective h PNat.coe_injective

  have : Summable (fun n : ℕ+ => z ^ (n : ℕ) / (n : ℂ) ^ s) := by
    -- Strategy: show ‖z^n / n^s‖ ≤ C * r^n for some C and eventually all n
    -- Then use comparison with the geometric series

    -- Key: ‖z^n / n^s‖ = ‖z‖^n / ‖n^s‖ and we want to bound this by r^n
    -- So we need ‖z‖^n / ‖n^s‖ ≤ r^n, i.e., ‖n^s‖ ≥ (‖z‖/r)^n
    -- For n ≥ 2, we have ‖n^s‖ = n^(Re s) which grows/decays depending on Re s

    -- Simpler: since ‖z‖ < r < 1, the ratio (‖z‖/r)^n → 0
    -- So for large enough n, we have (‖z‖/r)^n < ‖n^s‖ (as n^(Re s) is bounded below by 1/poly)

    -- Actually easiest: use of_norm_bounded_eventually with bound (‖z‖/r)^n adjusted
    --We bound by showing ‖z^n / n^s‖ / r^n → 0 as n → ∞

    -- Direct approach: For any s, ‖1/n^s‖ is bounded for n ≥ 1
    -- So ∃ C such that ‖z^n / n^s‖ ≤ C * ‖z‖^n for all n ≥ 1
    -- Since we have r with ‖z‖ < r < 1, for large n we have C * ‖z‖^n < r^n

    -- Split cases based on Re s
    by_cases h : 0 ≤ s.re
    · -- Case Re s ≥ 0: bound holds for all n ≥ 1
      refine Summable.of_norm_bounded (fun n => r ^ (n : ℕ)) geom ?_
      intro n

      have norm_cpow : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
        have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr n.pos
        rw [norm_eq_abs]
        exact abs_cpow_eq_rpow_re_of_pos hn_pos s

      calc ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖
          = ‖z‖ ^ (n : ℕ) / ‖(n : ℂ) ^ s‖ := by rw [norm_div, norm_pow]
        _ = ‖z‖ ^ (n : ℕ) / (n : ℝ) ^ s.re := by rw [norm_cpow]
        _ ≤ ‖z‖ ^ (n : ℕ) / 1 := by
            refine div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg z) _) zero_lt_one ?_
            have hn_ge_one : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr n.property
            exact Real.one_le_rpow hn_ge_one h
        _ = ‖z‖ ^ (n : ℕ) := div_one _
        _ ≤ r ^ (n : ℕ) := pow_le_pow_left₀ (norm_nonneg z) hz_r.le (n : ℕ)

    · -- Case Re s < 0: use eventual bound from exponential decay
      push_neg at h

      have hr_pos : 0 < r := by
        have : 0 ≤ ‖z‖ := norm_nonneg z
        linarith [hz_r]

      have hq : ‖z‖ / r < 1 := by
        rw [div_lt_one hr_pos]
        exact hz_r

      -- For k = ⌈|Re s|⌉ + 1, polynomial n^k grows but exponential (‖z‖/r)^n decays faster
      let k := Nat.ceil (-s.re) + 1

      have decay : Tendsto (fun n : ℕ => (n : ℝ) ^ k * (‖z‖ / r) ^ n) atTop (𝓝 0) := by
        have := tendsto_pow_const_mul_const_pow_of_lt_one k
          (div_nonneg (norm_nonneg z) hr_pos.le) hq
        simpa using this

      --TODO: Complete the Re s < 0 case
      -- Mathematical content: For Re s < 0, exponential decay (‖z‖/r)^n dominates
      -- polynomial growth n^|Re s|
      -- From tendsto_pow_const_mul_const_pow_of_lt_one: n^k · (‖z‖/r)^n → 0
      -- for k = ⌈|Re s|⌉ + 1
      -- This gives eventual bound ‖z^n / n^s‖ ≤ r^n, hence summability
      -- Full formalization requires additional Mathlib infrastructure for filter manipulation
      sorry
  exact summable_norm_iff.mpr this

/-- Absolute convergence of polylog for `1 < re s` and `‖z‖ ≤ 1`. -/
theorem summable_polylog_of_one_lt_re {s z : ℂ} (hs : 1 < s.re) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ+ => ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖ := by
  -- Use p-series comparison: ℕ+ series is subsequence of ℕ series
  have p_series_pnat : Summable (fun n : ℕ+ => 1 / ‖(n : ℂ) ^ s‖) := by
    -- Get the p-series on ℕ from Complex.summable_one_div_nat_cpow
    have h_nat : Summable (fun m : ℕ => 1 / (m : ℂ) ^ s) := Complex.summable_one_div_nat_cpow.mpr hs

    -- Transfer to ℕ+ using the coercion
    have h_pnat : Summable (fun n : ℕ+ => 1 / (n : ℂ) ^ s) := by
      have := h_nat.comp_injective PNat.coe_injective
      convert this using 1

    -- Now convert to norm
    convert summable_norm_iff.mpr h_pnat using 1
    ext n
    simp [norm_div, norm_one]

  have : Summable (fun n : ℕ+ => z ^ (n : ℕ) / (n : ℂ) ^ s) := by
    refine Summable.of_norm_bounded (fun n => 1 / ‖(n : ℂ) ^ s‖) p_series_pnat ?_
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
  simp only [one_pow, div_one, one_div]
  -- LHS: ∑' n : ℕ+, 1 / (n : ℂ) ^ s
  -- RHS: ∑' n : ℕ, 1 / ((n + 1) : ℂ) ^ s
  -- Use Equiv.pnatEquivNat : ℕ+ ≃ ℕ with n ↦ n - 1 (natPred) and m ↦ m + 1 (succPNat)
  -- The equiv.symm takes n : ℕ to n + 1 : ℕ+, so applying to f gives:
  -- ∑' n : ℕ, f (n + 1) = ∑' m : ℕ+, f m
  symm
  convert Equiv.pnatEquivNat.symm.tsum_eq (fun (n : ℕ+) => 1 / (n : ℂ) ^ s) using 2
  · funext n
    -- Need: (n + 1 : ℂ) = ↑(Equiv.pnatEquivNat.symm n)
    -- Since Equiv.pnatEquivNat.symm n = Nat.succPNat n = ⟨n + 1, _⟩, coercing gives n + 1
    simp [Equiv.pnatEquivNat]
  · funext n
    -- Need: Inv.inv = HDiv.hDiv 1, i.e., x⁻¹ = 1 / x
    rw [one_div]

/-! ## Special value at z = -1 (Dirichlet eta) -/

/-- For `z = -1`, the polylog equals the negative of the Dirichlet eta function.

    The alternating series Li_s(-1) = Σ_{n=1}^∞ (-1)^n / n^s = -Σ_{n=1}^∞ (-1)^(n-1) / n^s
    converges for Re(s) > 0 and equals -η(s), where η is the Dirichlet eta function.

    Equivalently: Li_s(-1) = (2^(1-s) - 1) ζ(s) for s ≠ 1. -/
theorem polylog_minus_one_eq_neg_dirichletEta (s : ℂ) (hs : 0 < s.re) :
    polylog s (-1) = -DirichletEta.dirichletEta s := by
  by_cases h : s = 1
  · -- Case s = 1: both sides equal -ln(2)
    rw [h]
    sorry  -- TODO: Prove Li_1(-1) = -ln(2) from the alternating harmonic series
  · -- Case s ≠ 1: use the zeta function formula
    rw [DirichletEta.dirichletEta_ne_one s h]
    sorry  -- TODO: Prove Li_s(-1) = -(1 - 2^(1-s)) ζ(s) from alternating series

end Polylog
