/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Alternating Harmonic Series

This file proves that the alternating harmonic series converges to ln(2).

## Main results

* `Real.tendsto_sum_alternating_harmonic`: The alternating harmonic series converges to ln(2):
  `Tendsto (fun k => ∑ i ∈ range k, (-1)^i / (i+1)) atTop (𝓝 (log 2))`

## Tags

alternating series, harmonic series, logarithm, Abel's theorem
-/

noncomputable section

namespace Real

open Filter Finset
open scoped Topology

/-- **Alternating Harmonic Series equals ln(2)**.
The partial sums ∑_{i<k} (-1)^i/(i+1) converge to ln(2),
proved by using Abel's limit theorem to extend the Taylor series of log(1+x) to x=1. -/
theorem tendsto_sum_alternating_harmonic :
    Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (i + 1)) atTop (𝓝 (log 2)) := by
  -- The series is alternating with terms of decreasing magnitude, so it converges to some limit
  obtain ⟨l, h⟩ : ∃ l, Tendsto (fun k => ∑ i ∈ range k,
      (-1 : ℝ) ^ i / (i + 1)) atTop (𝓝 l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun i j hij => by
        apply inv_anti₀ (by positivity : (0 : ℝ) < ↑i + 1)
        exact_mod_cast Nat.add_le_add_right hij.le 1
    · apply Tendsto.inv_tendsto_atTop
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
  -- Abel's limit theorem: the power series has the same limit as x → 1⁻
  have abel := tendsto_tsum_powerSeries_nhdsWithin_lt h
  -- m : nhdsWithin filter is finer than nhds; used to transport the limit
  -- (𝓝[<] 1 ≤ 𝓝 1 means every nhds-neighborhood is also a nhdsWithin-neighborhood)
  have m : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := tendsto_nhdsWithin_of_tendsto_nhds fun _ a => a
  -- Multiply by x (like Leibniz proof): x * ∑ a_n x^n → l * 1 = l
  have mul_abel := abel.mul m
  rw [mul_one] at mul_abel
  -- For 0 < y < 1, y * ∑ a_n y^n = log(1+y) via hasSum_pow_div_log_of_abs_lt_one
  replace mul_abel : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] 1) (𝓝 l) := by
    apply mul_abel.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 1, zero_lt_one
    intro y hy1 hy2
    rw [dist_eq, abs_sub_lt_iff] at hy1
    rw [Set.mem_Iio] at hy2
    have ny : |y| < 1 := by rw [abs_lt]; constructor <;> linarith
    have hy_pos : 0 < y := by linarith
    -- hasSum_pow_div_log with -y: ∑ (-y)^(n+1)/(n+1) = -log(1+y)
    -- Negate: ∑ (-1)^n y^(n+1)/(n+1) = log(1+y)
    have hlog : HasSum (fun n : ℕ => ((-1 : ℝ) ^ n / (↑n + 1) * y ^ n) * y)
        (log (1 + y)) := by
      have h1 := (hasSum_pow_div_log_of_abs_lt_one (show |-y| < 1 by rwa [abs_neg])).neg
      simp only [neg_neg] at h1
      rw [show (1 : ℝ) - -y = 1 + y from by ring] at h1
      exact h1.congr fun n => by ring_nf
    -- HasSum gives tsum equality; factor y out using summable_mul_right_iff
    have hsumm : Summable (fun n : ℕ => (-1 : ℝ) ^ n / (↑n + 1) * y ^ n) :=
      ((summable_mul_right_iff (ne_of_gt hy_pos)).mp hlog.summable)
    rw [← hlog.tsum_eq, ← hsumm.tsum_mul_right]
  -- log is continuous at 2, so the limit as x → 1⁻ of log(1+x) is log(2)
  have h21 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [← h21]
  rwa [tendsto_nhds_unique mul_abel
    ((tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds |>.log
      (by rw [h21]; norm_num))] at h

end Real
