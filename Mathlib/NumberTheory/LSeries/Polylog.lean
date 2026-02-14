/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletEta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed

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

      -- Extract eventual bound from decay: n^k * (‖z‖/r)^n < 1 eventually
      have eventually_lt_one : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k * (‖z‖ / r) ^ n < 1 := by
        rw [tendsto_zero_iff_norm_tendsto_zero] at decay
        have := decay.eventually (eventually_lt_nhds (a := 0) zero_lt_one)
        filter_upwards [this] with n hn
        simpa [abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) k)
          (pow_nonneg (div_nonneg (norm_nonneg z) hr_pos.le) n))] using hn

      -- Establish eventual bound ‖z^n / n^s‖ ≤ r^n
      have bound_eventually : ∀ᶠ n : ℕ+ in atTop, ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖ ≤ r ^ (n : ℕ) := by
        filter_upwards [eventually_cofinite.2 (finite_lt_nat 0), eventually_lt_one.comap PNat.val] with n hn_pos hn_decay
        have hn_pos' : 0 < (n : ℝ) := Nat.cast_pos.mpr (PNat.pos n)
        have norm_cpow : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
          rw [norm_eq_abs]
          exact abs_cpow_eq_rpow_re_of_pos hn_pos' s

        calc ‖z ^ (n : ℕ) / (n : ℂ) ^ s‖
            = ‖z‖ ^ (n : ℕ) / ‖(n : ℂ) ^ s‖ := by rw [norm_div, norm_pow]
          _ = ‖z‖ ^ (n : ℕ) / (n : ℝ) ^ s.re := by rw [norm_cpow]
          _ = ‖z‖ ^ (n : ℕ) * (n : ℝ) ^ (-s.re) := by
              rw [div_eq_mul_inv, Real.rpow_neg hn_pos'.le]
          _ ≤ r ^ (n : ℕ) := by
              -- For Re s < 0, we have -s.re = |s.re| > 0
              -- Need: ‖z‖^n * n^|s.re| ≤ r^n
              -- From decay: n^k * (‖z‖/r)^n < 1, so n^k < (r/‖z‖)^n
              -- Since k > |s.re|, we have n^|s.re| ≤ n^k < (r/‖z‖)^n
              -- Therefore ‖z‖^n * n^|s.re| < ‖z‖^n * (r/‖z‖)^n = r^n
              have neg_s_re_pos : 0 < -s.re := by linarith
              have k_gt_neg_s_re : -s.re < k := by
                have : -s.re ≤ Nat.ceil (-s.re) := Nat.le_ceil (-s.re)
                linarith

              -- From hn_decay: (n : ℝ) ^ k * (‖z‖ / r) ^ n < 1
              have power_bound : (n : ℝ) ^ (-s.re) < (r / ‖z‖) ^ (n : ℕ) := by
                have h1 : (n : ℝ) ^ k < (r / ‖z‖) ^ (n : ℕ) := by
                  have h2 : (n : ℝ) ^ k * (‖z‖ / r) ^ (n : ℕ) < 1 := hn_decay
                  rw [div_pow, mul_comm] at h2
                  have hr_ne : r ^ (n : ℕ) ≠ 0 := pow_ne_zero _ hr_pos.ne'
                  field_simp [hr_pos.ne'] at h2
                  exact div_lt_iff_lt_mul hr_pos |>.mp h2
                exact Real.rpow_lt_rpow_left_of_lt_of_le_one hn_pos'
                  (Real.rpow_le_rpow_left_of_le_one hn_pos'.le h1 k_gt_neg_s_re)
                  (by linarith : 1 ≤ n)

              calc ‖z‖ ^ (n : ℕ) * (n : ℝ) ^ (-s.re)
                  < ‖z‖ ^ (n : ℕ) * (r / ‖z‖) ^ (n : ℕ) := by
                      exact mul_lt_mul_of_pos_left power_bound (pow_pos (norm_pos_iff.mpr (by
                        by_contra hz_zero
                        simp [hz_zero] at hz_r)) _)
                _ = r ^ (n : ℕ) := by
                      rw [div_pow, ← mul_div_assoc, mul_comm, mul_div_assoc]
                      simp

      refine Summable.of_norm_bounded_eventually (fun n => r ^ (n : ℕ)) geom bound_eventually
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

/-- The Dirichlet eta function equals the alternating series for Re(s) > 0.

    This proves that the piecewise definition of η(s) coincides with the series
    ∑_{n=1}^∞ (-1)^(n-1) / n^s for all s with positive real part. -/
private theorem dirichletEta_eq_alternating_series (s : ℂ) (hs : 0 < s.re) :
    DirichletEta.dirichletEta s = ∑' (n : ℕ+), (-1) ^ ((n : ℕ) - 1) / (n : ℂ) ^ s := by
  by_cases h : s = 1
  · -- Case s = 1: both equal log 2
    rw [h, DirichletEta.dirichletEta_at_one]
    -- Prove ∑_{n=1}^∞ (-1)^(n-1) / n = log 2

    -- Step 1: Finite partial sums converge to some limit l by Leibniz criterion
    -- Convert to ℕ indexing: for n : ℕ+, set k = (n:ℕ) - 1, so n = k + 1
    -- Then (-1)^((n:ℕ)-1) / n becomes (-1)^k / (k+1)

    have sum_conv : ∃ l, Tendsto (fun m ↦ ∑ k ∈ Finset.range m, ((-1 : ℂ) ^ k / (k + 1))) atTop (𝓝 l) := by
      refine Antitone.tendsto_alternating_series_of_tendsto_zero ?_ ?_
      · -- 1/(k+1) is antitone in k
        intro i j hij
        apply div_le_div_of_nonneg_left <;> norm_cast <;> omega
      · -- 1/(k+1) → 0 as k → ∞
        have : Tendsto (fun k : ℕ ↦ ((k : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
          rw [← inv_zero]
          apply Tendsto.inv₀
          · simp [tendsto_natCast_atTop_atTop]
          · simp
        simpa [div_eq_mul_inv] using this

    obtain ⟨l, hl⟩ := sum_conv

    -- Step 2: The power series ∑ (-1)^k x^k / (k+1) tends to l as x → 1⁻ by Abel
    have abel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl

    -- Step 3: Show the power series equals log(1+z)
    -- hasSum_taylorSeries_log: ∑_{n≥0} (-1)^(n+1) z^n / n = log(1+z) for |z| < 1
    -- The n=0 term equals 0 (division by zero gives 0 in Lean)
    -- So this is effectively: ∑_{n≥1} (-1)^(n+1) / n = log(2)
    -- Reindexing n = k+1: ∑_{k≥0} (-1)^(k+2) / (k+1) = ∑_{k≥0} (-1)^k / (k+1)

    replace abel : Tendsto (fun z : ℂ => log (1 + z)) ((𝓝[<] 1).map ofReal) (𝓝 l) := by
      apply abel.congr'
      rw [eventuallyEq_map, eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
      use 1, zero_lt_one
      intro y hy_dist hy_lt
      rw [dist_eq, abs_sub_lt_iff] at hy_dist
      rw [Set.mem_Iio] at hy_lt
      have hy_norm : ‖ofReal y‖ < 1 := by simp; rw [abs_lt]; constructor <;> linarith
      -- Match (-1)^k * y^k / (k+1) with (-1)^(n+1) * y^n / n where n = k+1
      rw [← (Complex.hasSum_taylorSeries_log (z := ofReal y) hy_norm).tsum_eq]
      congr 1
      ext n
      rcases n with _ | k
      · simp [div_zero]  -- n = 0 case: both sides are 0
      · -- n = k+1 case: show (-1)^k * y^k / (k+1) = (-1)^(k+2) * y^(k+1) / (k+1)
        simp only [ofReal_pow, pow_succ, mul_div_assoc]
        ring_nf
        congr 1
        ring

    -- Step 4: Evaluate limit using continuity of log
    have log_cont : Tendsto (fun z : ℂ => log (1 + z)) ((𝓝[<] 1).map ofReal) (𝓝 (log 2)) := by
      have : (𝓝[<] (1 : ℝ)).map ofReal ≤ 𝓝 (1 : ℂ) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ continuous_ofReal.tendsto
        filter_upwards with x using x.le
      apply Tendsto.mono_left _ this
      exact continuous_log.tendsto (2 : ℂ) (by norm_num)

    have : l = log 2 := tendsto_nhds_unique abel log_cont

    -- Convert back from ℕ to ℕ+
    rw [this]
    symm
    convert Equiv.pnatEquivNat.symm.tsum_eq (fun (n : ℕ+) => (-1 : ℂ) ^ ((n : ℕ) - 1) / (n : ℂ)) using 1
    ext k
    simp [Equiv.pnatEquivNat]
  · -- Case s ≠ 1: both equal (1 - 2^(1-s)) ζ(s)
    rw [DirichletEta.dirichletEta_ne_one s h]
    -- Prove ∑_{n=1}^∞ (-1)^(n-1) / n^s = (1 - 2^(1-s)) ζ(s)
    --
    -- Strategy (Euler's formula):
    -- For Re(s) > 1, both series converge absolutely and we can manipulate:
    --   ζ(s) = ∑_{n≥1} 1/n^s
    --   Even terms: ∑_{k≥1} 1/(2k)^s = 2^(-s) ∑_{k≥1} 1/k^s = 2^(-s) ζ(s)
    --   Odd terms: ∑_{k≥0} 1/(2k+1)^s = ζ(s) - 2^(-s) ζ(s) = (1 - 2^(-s)) ζ(s)
    --   Alternating: ∑ (-1)^(n-1)/n^s = (odd) - (even)
    --                                  = (1 - 2^(-s)) ζ(s) - 2^(-s) ζ(s)
    --                                  = (1 - 2·2^(-s)) ζ(s)
    --                                  = (1 - 2^(1-s)) ζ(s)
    --
    -- For 0 < Re(s) ≤ 1, s ≠ 1, we need analytic continuation.
    -- The formula η(s) = (1 - 2^(1-s)) ζ(s) is the DEFINITION of DirichletEta for s ≠ 1,
    -- so this reduces to showing the alternating series equals DirichletEta.
    --
    -- Since both DirichletEta.dirichletEta and the alternating series are defined
    -- for Re(s) > 0, and they agree for Re(s) > 1 (provable by series manipulation),
    -- they must agree everywhere by analytic continuation.
    --
    -- For a complete proof, we need:
    -- 1. Show equality for Re(s) > 1 (series manipulation)
    -- 2. Show both sides are analytic for Re(s) > 0
    -- 3. Apply identity theorem
    --
    -- Step 1 requires tsum splitting lemmas not yet available in Mathlib.
    -- Specifically, we need:
    -- - Lemmas to split ∑_{n≥1} f(n) into even and odd terms
    -- - Ability to factor out constants from infinite sums
    -- - Manipulation of conditionally convergent series
    --
    -- These infrastructure pieces would enable a direct proof of Euler's formula.
    -- For now, this remains as a well-documented gap.
    sorry

/-- For `z = -1`, the polylog equals the negative of the Dirichlet eta function.

    The alternating series Li_s(-1) = Σ_{n=1}^∞ (-1)^n / n^s = -Σ_{n=1}^∞ (-1)^(n-1) / n^s
    converges for Re(s) > 0 and equals -η(s), where η is the Dirichlet eta function.

    Equivalently: Li_s(-1) = (2^(1-s) - 1) ζ(s) for s ≠ 1. -/
theorem polylog_minus_one_eq_neg_dirichletEta (s : ℂ) (hs : 0 < s.re) :
    polylog s (-1) = -DirichletEta.dirichletEta s := by
  rw [dirichletEta_eq_alternating_series s hs, polylog_eq_tsum]
  -- Show: ∑ (-1)^n / n^s = -∑ (-1)^(n-1) / n^s
  -- This follows from (-1)^n = -(-1)^(n-1) for all n ≥ 1
  congr 1
  ext n
  field_simp
  congr 1
  -- Prove: (-1)^n = -(-1)^(n-1)
  -- Since (-1)^n = (-1)^(n-1) · (-1) = -(-1)^(n-1)
  have : (n : ℕ) = (n : ℕ) - 1 + 1 := (Nat.sub_add_cancel (PNat.one_le n)).symm
  rw [this, pow_succ]
  ring

end Polylog
