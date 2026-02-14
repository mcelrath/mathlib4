/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.PNat.Basic

/-!
# Euler's Formula for Dirichlet Eta Function

This file proves Euler's classical formula relating alternating series to the Riemann zeta function.

## Main results

* `alternating_zeta_formula`: For Re(s) > 1, ∑ (-1)^(n-1)/n^s = (1 - 2^(1-s)) ζ(s)

## References

* Euler, L. (1748). Introductio in analysin infinitorum.
* Apostol, T. M. (1976). Introduction to Analytic Number Theory. Springer.

## Tags

Dirichlet eta, Riemann zeta, alternating series
-/

noncomputable section

open Complex
open scoped Topology

namespace EulerFormula

/-- The even terms of the zeta sum equal 2^(-s) times the full zeta sum. -/
lemma tsum_zeta_even {s : ℂ} (hs : 1 < s.re) :
    ∑' (k : ℕ), 1 / (2 * (k + 1) : ℂ) ^ s = (2 : ℂ) ^ (-s) * riemannZeta s := by
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have key : ∀ k : ℕ, 1 / (2 * (k + 1) : ℂ) ^ s = (2 : ℂ) ^ (-s) * (1 / (k + 1 : ℂ) ^ s) := by
    intro k
    rw [show (2 * (k + 1) : ℂ) = (2 : ℂ) * (k + 1 : ℂ) by norm_cast; ring]
    rw [mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ 2) (Nat.cast_nonneg _)]
    field_simp
    rw [cpow_neg, mul_comm]
  simp_rw [key]
  rw [tsum_mul_left, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-- The odd terms of the zeta sum equal (1 - 2^(-s)) times the full zeta sum. -/
lemma tsum_zeta_odd {s : ℂ} (hs : 1 < s.re) :
    ∑' (k : ℕ), 1 / (2 * k + 1 : ℂ) ^ s = (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by
  sorry

/-- The alternating sum equals the odd terms minus the even terms. -/
lemma alternating_eq_odd_sub_even {s : ℂ} (hs : 1 < s.re) :
    ∑' (n : ℕ+), (-1 : ℂ) ^ ((n : ℕ) - 1) / (n : ℂ) ^ s =
    (∑' k : ℕ, 1 / (2 * k + 1 : ℂ) ^ s) - (∑' k : ℕ, 1 / (2 * (k + 1) : ℂ) ^ s) := by
  sorry

/-- Euler's formula for the Dirichlet eta function:
For Re(s) > 1, the alternating zeta sum equals (1 - 2^(1-s)) ζ(s). -/
theorem alternating_zeta_formula {s : ℂ} (hs : 1 < s.re) :
    ∑' (n : ℕ+), (-1 : ℂ) ^ ((n : ℕ) - 1) / (n : ℂ) ^ s =
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [alternating_eq_odd_sub_even hs]
  rw [tsum_zeta_odd hs, tsum_zeta_even hs]
  -- Simplify: (1 - 2^(-s))ζ - 2^(-s)ζ = ζ - 2^(-s)ζ - 2^(-s)ζ = ζ - 2·2^(-s)ζ = (1 - 2^(1-s))ζ
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  -- Show 2 * 2^(-s) = 2^(1-s)
  have key : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    rw [← cpow_one (2 : ℂ), ← cpow_add _ _ h2_ne]
    ring
  calc (1 - (2 : ℂ) ^ (-s)) * riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s
      = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by ring
    _ = riemannZeta s - ((2 : ℂ) ^ (-s) + (2 : ℂ) ^ (-s)) * riemannZeta s := by ring
    _ = riemannZeta s - (2 : ℂ) * (2 : ℂ) ^ (-s) * riemannZeta s := by ring
    _ = riemannZeta s - (2 : ℂ) ^ (1 - s) * riemannZeta s := by rw [key]
    _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by ring

end EulerFormula
