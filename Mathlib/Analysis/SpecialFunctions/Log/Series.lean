/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Alternating Harmonic Series

This file proves that the alternating harmonic series converges to ln(2).

## Main results

* `Real.tendsto_sum_alternating_harmonic`: Partial sums converge to some limit
* `Real.tsum_alternating_harmonic_eq_log_two`: ∑_{n=1}^∞ (-1)^(n-1)/n = ln(2)

## Tags

alternating series, harmonic series, logarithm, Abel's theorem
-/

noncomputable section

namespace Real

open Filter Finset
open scoped Topology

/-- The partial sums of the alternating harmonic series converge to some limit. -/
theorem tendsto_sum_alternating_harmonic :
    ∃ l, Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (i + 1)) atTop (𝓝 l) := by
  apply Antitone.tendsto_alternating_series_of_tendsto_zero
  · -- The terms 1/(i+1) are decreasing
    intro i j hij
    gcongr
    exact Nat.add_le_add_right hij 1
  · -- The terms tend to zero
    apply Tendsto.inv_tendsto_atTop
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop

/-- **Alternating Harmonic Series equals ln(2)**.
The alternating sum ∑_{n=1}^∞ (-1)^(n-1)/n equals ln(2),
proved by using Abel's limit theorem to extend the Taylor series of log(1+x) to x=1. -/
theorem tsum_alternating_harmonic_eq_log_two :
    ∑' n : ℕ, (-1 : ℝ) ^ n / (n + 1) = log 2 := by
  -- The series is alternating with terms of decreasing magnitude, so it converges to some limit
  obtain ⟨l, h⟩ := tendsto_sum_alternating_harmonic
  -- Abel's limit theorem states that the corresponding power series has the same limit as x → 1⁻
  have abel := tendsto_tsum_powerSeries_nhdsWithin_lt h
  -- For |x| < 1, this series equals log(1+x)
  have m : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := tendsto_nhdsWithin_of_tendsto_nhds fun _ a => a
  replace abel : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] 1) (𝓝 l) := by
    apply abel.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 1, zero_lt_one
    intro y hy1 hy2
    rw [dist_eq, abs_sub_lt_iff] at hy1
    rw [Set.mem_Iio] at hy2
    have ny : |y| < 1 := by rw [abs_lt]; constructor <;> linarith
    -- Convert to complex version for hasSum_taylorSeries_log
    rw [← ofReal_inj, ← Complex.log_ofReal_re (by linarith : 0 < 1 + y)]
    rw [ofReal_add, ofReal_one]
    have : ‖(y : ℂ)‖ < 1 := by simp [Complex.norm_eq_abs, Complex.abs_ofReal, ny]
    rw [← (Complex.hasSum_taylorSeries_log this).tsum_eq]
    simp only [div_eq_iff, ne_eq, ofReal_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel₀]
    rw [← tsum_mul_right]
    congr 1
    ext n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · simp only [pow_succ, ← mul_assoc]
      rw [ofReal_mul, ofReal_pow]
      congr 1
      · norm_cast
      · have : (-1 : ℂ) ^ n = ↑((-1 : ℝ) ^ n) := by
          rw [← ofReal_pow, ← ofReal_neg, ← ofReal_one]
        rw [this]
        congr 1
        ring_nf
  -- But log is continuous at 2, so the limit is log(2)
  have : log 2 = log (1 + 1) := by norm_num
  rw [this] at abel ⊢
  rwa [tendsto_nhds_unique abel ((continuous_log.tendsto 2).mono_left m)] at h

end Real
