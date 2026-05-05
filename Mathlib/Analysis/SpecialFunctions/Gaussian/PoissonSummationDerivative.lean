/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivative of the Gaussian Poisson summation formula (DRAFT — work in progress)

`Real.tsum_exp_neg_mul_int_sq` provides the bosonic Jacobi inversion

`∑' (n : ℤ), exp (-π * a * n ^ 2) = a ^ (-1/2) * ∑' (n : ℤ), exp (-π / a * n ^ 2)`

for real `a > 0`. Differentiating both sides with respect to `a` produces a closed
form for the `n²`-weighted sum

`∑' (n : ℤ), n ^ 2 * exp (-π * a * n ^ 2)`

in terms of the dual sum. This file is intended to package that derivative
identity, which is needed for heat-kernel and spectral-zeta applications
(e.g. derivatives of the Jacobi theta function in the modular parameter).

## Status

DRAFT. The statements below are the intended API. Proofs of
`hasDerivAt_tsum_exp_neg_pi_mul_int_sq` and the closed-form identity require:

1. A clean ℤ-indexed dominator for `n² · exp(-π a n²)` (proof is the
   symmetrization of the standard `summable_pow_mul_geometric_of_norm_lt_one`
   ℕ-result; bookkeeping of `Int.natAbs` is fiddly).
2. Application of `hasDerivAt_tsum_of_isPreconnected` on `Set.Ioi (a/2)`
   with the geometric majorant from (1) — at the order of `n² · π · n² ·
   exp(-π · (a/2) · n²)` for the derivative bound.
3. Differentiation of the RHS via product / chain rule on
   `a ↦ a^(-1/2) · F(1/a)` where `F(b) := ∑' n, exp(-π b n²)`.
4. Algebraic rearrangement to obtain the closed form.

The statements compile (modulo `sorry`); the proofs are the substantive content.

## Main results (intended)

* `Real.summable_n_sq_exp_neg_pi_mul_int_sq` — summability of `n² · exp(-π a n²)`
  over `ℤ` for `a > 0`.
* `Real.hasDerivAt_tsum_exp_neg_pi_mul_int_sq` — term-by-term differentiation
  of `a ↦ ∑' n, exp(-π a n²)`, giving derivative `-π ∑' n, n² exp(-π a n²)`.
* `Real.tsum_n_sq_exp_neg_pi_mul_int_sq_eq` — closed-form expression obtained
  by differentiating the bosonic Poisson inversion formula.
-/

open scoped Real Topology
open Real Filter Set

namespace Real

/-! ### Summability of `n² · exp(-π a n²)` -/

/-- For `a > 0`, the `n²`-weighted Gaussian series is summable over `ℤ`. -/
theorem summable_n_sq_exp_neg_pi_mul_int_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2)) := by
  have h_c_pos : 0 < π * a := mul_pos pi_pos ha
  -- ℕ-side: dominate n² · exp(-c·n²) by n² · r^n with r = exp(-c) < 1.
  have hℕ : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2)) := by
    have hr : Real.exp (-(π * a)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hr_nn : 0 ≤ Real.exp (-(π * a)) := (Real.exp_pos _).le
    have hgeom : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-(π * a)) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 2
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hr_nn] using hr)
    refine hgeom.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.zero_le
      have hn_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (n : ℝ) * 1 ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 hn_nn
        simpa [pow_two] using this
      have hexp : Real.exp (-π * a * (n : ℝ) ^ 2) ≤ Real.exp (-(π * a) * (n : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hid : Real.exp (-(π * a)) ^ n = Real.exp (-(π * a) * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [hid]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
  -- ℤ-side: split via even symmetry f(-n) = f(n).
  refine Summable.of_nat_of_neg hℕ ?_
  refine hℕ.congr (fun n => ?_)
  simp [Int.cast_neg]

/-! ### Term-by-term derivative of the bosonic Gaussian sum -/

/-- Term-by-term differentiation: for `a > 0`,
`d/da [∑' n, exp(-π a n²)] = -π · ∑' n, n² · exp(-π a n²)`. -/
theorem hasDerivAt_tsum_exp_neg_pi_mul_int_sq {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b : ℝ => ∑' n : ℤ, Real.exp (-π * b * (n : ℝ) ^ 2))
      (-π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2)) a := by
  have ha2 : 0 < a / 2 := by linarith
  have ha_mem : a ∈ Set.Ioi (a / 2) := by simp; linarith
  -- Dominator for derivative terms on Ioi(a/2).
  have hdom : Summable (fun n : ℤ => π * ((n : ℝ) ^ 2 * Real.exp (-π * (a / 2) * (n : ℝ) ^ 2))) :=
    (summable_n_sq_exp_neg_pi_mul_int_sq ha2).const_smul π
  -- Convergence at a: the base series ∑ exp(-π·a·n²), proved exactly as summable_theta_Z_term.
  have hconv : Summable (fun n : ℤ => Real.exp (-π * a * (n : ℝ) ^ 2)) := by
    have h_c_pos : 0 < π * a := mul_pos pi_pos ha
    have hℕ : Summable (fun n : ℕ => Real.exp (-π * a * (n : ℝ) ^ 2)) := by
      have hr : Real.exp (-(π * a)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hr_nn : 0 ≤ Real.exp (-(π * a)) := (Real.exp_pos _).le
      refine (summable_geometric_of_lt_one hr_nn hr).of_nonneg_of_le
        (fun n => (Real.exp_pos _).le) (fun n => ?_)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.zero_le
        have hn_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have hid : Real.exp (-(π * a)) ^ n = Real.exp (-(π * a) * (n : ℝ)) := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [hid]
        exact Real.exp_le_exp.mpr (by nlinarith)
    refine Summable.of_nat_of_neg hℕ ?_
    refine hℕ.congr (fun n => ?_)
    push_cast; ring_nf
  -- Apply hasDerivAt_tsum_of_isPreconnected on Ioi(a/2).
  -- g n b = exp(-π·b·n²), g' n b = exp(-π·b·n²) · (-π·n²)
  have h_key : HasDerivAt (fun b : ℝ => ∑' n : ℤ, Real.exp (-π * b * (n : ℝ) ^ 2))
      (∑' n : ℤ, Real.exp (-π * a * (n : ℝ) ^ 2) * (-π * (n : ℝ) ^ 2)) a :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℤ => π * ((n : ℝ) ^ 2 * Real.exp (-π * (a / 2) * (n : ℝ) ^ 2)))
      (t := Set.Ioi (a / 2))
      (g := fun n b => Real.exp (-π * b * (n : ℝ) ^ 2))
      (g' := fun n b => Real.exp (-π * b * (n : ℝ) ^ 2) * (-π * (n : ℝ) ^ 2))
      hdom isOpen_Ioi isPreconnected_Ioi
      (fun n b _ => by
        have h := ((hasDerivAt_id b).const_mul (-π * (n : ℝ) ^ 2)).exp
        simp only [id] at h
        change HasDerivAt (fun b : ℝ => Real.exp (-π * b * (n : ℝ) ^ 2))
          (Real.exp (-π * b * (n : ℝ) ^ 2) * (-π * (n : ℝ) ^ 2)) b
        have heq : (fun b : ℝ => Real.exp (-π * b * (n : ℝ) ^ 2)) =
            (fun b : ℝ => Real.exp (-π * (n : ℝ) ^ 2 * b)) := by funext b; ring_nf
        rw [heq]
        convert h using 1; ring)
      (fun n b hb => by
        simp only [Set.mem_Ioi] at hb
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have h_exp_mono : Real.exp (-π * b * (n : ℝ) ^ 2) ≤ Real.exp (-π * (a / 2) * (n : ℝ) ^ 2) :=
          Real.exp_le_exp.mpr (by
            have hpi := pi_pos.le
            have hn2 := sq_nonneg (n : ℝ)
            nlinarith [mul_nonneg (mul_nonneg hpi (by linarith : (0 : ℝ) ≤ b - a / 2)) hn2])
        have h_abs_pi : |(-π * (n : ℝ) ^ 2)| = π * (n : ℝ) ^ 2 := by
          rw [abs_mul, abs_neg, abs_of_pos pi_pos, abs_of_nonneg (sq_nonneg _)]
        rw [h_abs_pi]
        -- goal: exp(-π*b*n²) * (π*n²) ≤ π*(n²*exp(-π*(a/2)*n²))
        have h1 : Real.exp (-π * b * (n : ℝ) ^ 2) * (π * (n : ℝ) ^ 2)
            ≤ Real.exp (-π * (a / 2) * (n : ℝ) ^ 2) * (π * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h_exp_mono (by positivity)
        linarith [h1])
      ha_mem hconv ha_mem
  convert h_key using 1
  rw [← tsum_mul_left]
  congr 1; ext n; ring

/-! ### Closed-form derivative of the bosonic Poisson inversion -/

/-- Differentiated Poisson summation formula: closed form for the `n²`-weighted
Gaussian sum, obtained by differentiating both sides of
`Real.tsum_exp_neg_mul_int_sq` and rearranging.

For `a > 0`,
$$
\pi \sum_{n \in \mathbb{Z}} n^2 \, e^{-\pi a n^2}
\;=\; \tfrac{1}{2}\, a^{-3/2}\, \sum_{n \in \mathbb{Z}} e^{-\pi n^2 / a}
\;-\; \pi\, a^{-5/2} \sum_{n \in \mathbb{Z}} n^2 \, e^{-\pi n^2 / a}.
$$
-/
theorem tsum_n_sq_exp_neg_pi_mul_int_sq_eq {a : ℝ} (ha : 0 < a) :
    π * (∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2))
      = (1 / 2) * a ^ (-(3 / 2 : ℝ)) *
          (∑' n : ℤ, Real.exp (-π / a * (n : ℝ) ^ 2))
        - π * a ^ (-(5 / 2 : ℝ)) *
          (∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π / a * (n : ℝ) ^ 2)) := by
  -- Let L(b) = ∑' n : ℤ, exp(-π*b*n²). Poisson: L(a) = a^(-1/2) * L(1/a).
  -- Differentiate both sides at a using HasDerivAt.unique.
  have ha_ne : a ≠ 0 := ha.ne'
  have ha_inv_pos : 0 < a⁻¹ := inv_pos.mpr ha
  -- LHS derivative of L at a:
  have hL : HasDerivAt (fun b : ℝ => ∑' n : ℤ, Real.exp (-π * b * (n : ℝ) ^ 2))
      (-π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2)) a :=
    hasDerivAt_tsum_exp_neg_pi_mul_int_sq ha
  -- Rewrite L as the RHS using Real.tsum_exp_neg_mul_int_sq; get same HasDerivAt.
  -- Intermediate: 1/a^(1/2) = a^(-1/2) in rpow notation.
  have hrpow_eq : (1 : ℝ) / a ^ ((1 : ℝ) / 2) = a ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, Real.rpow_neg ha.le]
  -- The Poisson identity with our exponent notation.
  have hpoisson : ∀ b : ℝ, 0 < b →
      ∑' n : ℤ, Real.exp (-π * b * (n : ℝ) ^ 2) =
      b ^ (-(1/2 : ℝ)) * ∑' n : ℤ, Real.exp (-π / b * (n : ℝ) ^ 2) := fun b hb => by
    have h0 := Real.tsum_exp_neg_mul_int_sq hb
    rw [show (1 : ℝ) / b ^ ((1:ℝ)/2) = b ^ (-(1/2:ℝ)) from by
      rw [one_div, Real.rpow_neg hb.le]] at h0
    exact h0
  -- RHS function: g(b) = b^(-1/2) * L(1/b). Same as L by Poisson.
  -- Derivative of b^(-1/2):
  have hd_rpow : HasDerivAt (fun b : ℝ => b ^ (-(1/2 : ℝ)))
      (-(1/2 : ℝ) * a ^ (-(1/2 : ℝ) - 1)) a :=
    hasDerivAt_rpow_const (Or.inl ha_ne)
  -- Derivative of 1/b = b^(-1):
  have hd_inv : HasDerivAt (fun b : ℝ => b⁻¹) (-a⁻¹ ^ 2) a := by
    simpa [sq] using hasDerivAt_inv ha_ne
  -- L'(1/a) via chain rule with 1/a derivative:
  have hd_L_inv : HasDerivAt (fun b : ℝ => ∑' n : ℤ, Real.exp (-π * b⁻¹ * (n : ℝ) ^ 2))
      ((-π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2)) * (-a⁻¹ ^ 2)) a :=
    (hasDerivAt_tsum_exp_neg_pi_mul_int_sq ha_inv_pos).comp a hd_inv
  -- Product rule for g(b) = b^(-1/2) * L(1/b):
  have hg : HasDerivAt (fun b : ℝ => b ^ (-(1/2 : ℝ)) *
      ∑' n : ℤ, Real.exp (-π * b⁻¹ * (n : ℝ) ^ 2))
      (-(1/2 : ℝ) * a ^ (-(1/2 : ℝ) - 1) *
          ∑' n : ℤ, Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2) +
       a ^ (-(1/2 : ℝ)) *
          ((-π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2)) * (-a⁻¹ ^ 2))) a :=
    hd_rpow.mul hd_L_inv
  -- Since L(b) = g(b) for all b > 0, the HasDerivAt for L at a can be recast as g's deriv.
  -- Use HasDerivAt.congr_deriv: hL.deriv = hg.deriv (same function, so derivatives equal).
  have hfun_eq : (fun b : ℝ => ∑' n : ℤ, Real.exp (-π * b * (n : ℝ) ^ 2)) =ᶠ[nhds a]
      (fun b : ℝ => b ^ (-(1/2 : ℝ)) * ∑' n : ℤ, Real.exp (-π * b⁻¹ * (n : ℝ) ^ 2)) := by
    apply Filter.eventually_of_mem (Ioi_mem_nhds ha)
    intro b hb
    simp only [Set.mem_Ioi] at hb
    exact hpoisson b hb
  have hd_lhs_eq_rhs : -π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a * (n : ℝ) ^ 2) =
      -(1/2 : ℝ) * a ^ (-(1/2 : ℝ) - 1) *
          ∑' n : ℤ, Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2) +
       a ^ (-(1/2 : ℝ)) *
          ((-π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2)) * (-a⁻¹ ^ 2)) :=
    hL.unique (hg.congr_of_eventuallyEq hfun_eq)
  -- Simplify rpow exponents and a⁻¹ = 1/a.
  have h_exp1 : -(1/2 : ℝ) - 1 = -(3/2 : ℝ) := by norm_num
  have h_inv_sq : a⁻¹ ^ 2 = a ^ (-(2 : ℝ)) := by
    simp [inv_pow, Real.rpow_neg ha.le]
  have h_prod_exp : a ^ (-(1/2 : ℝ)) * a ^ (-(2 : ℝ)) = a ^ (-(5/2 : ℝ)) := by
    rw [← Real.rpow_add ha]; norm_num
  have h_inv_pi : ∀ n : ℤ, Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2) = Real.exp (-π / a * (n : ℝ) ^ 2) := by
    intro n; congr 1
  -- Replace a⁻¹ with a^(-2) and simplify exponents.
  rw [h_exp1, h_inv_sq] at hd_lhs_eq_rhs
  -- Change a⁻¹ inside exp to a^(-1) = 1/a.
  have h_tsum_rw1 : ∑' n : ℤ, Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2) =
      ∑' n : ℤ, Real.exp (-π / a * (n : ℝ) ^ 2) := tsum_congr (fun n => h_inv_pi n)
  have h_tsum_rw2 : ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π * a⁻¹ * (n : ℝ) ^ 2) =
      ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π / a * (n : ℝ) ^ 2) :=
    tsum_congr (fun n => by rw [h_inv_pi])
  rw [h_tsum_rw1, h_tsum_rw2] at hd_lhs_eq_rhs
  -- Now hd_lhs_eq_rhs gives the equation; algebraically rearrange to goal.
  -- Goal: π * S = (1/2) * a^(-3/2) * T₁ - π * a^(-5/2) * T₂
  -- where S = ∑ n² exp(-π*a*n²), T₁ = ∑ exp(-π/a*n²), T₂ = ∑ n² exp(-π/a*n²)
  -- From hd_lhs_eq_rhs:
  --   -π * S = -(1/2) * a^(-3/2) * T₁ + a^(-1/2) * (-π * T₂) * (-a^(-2))
  --          = -(1/2) * a^(-3/2) * T₁ + π * a^(-5/2) * T₂
  -- So π * S = (1/2) * a^(-3/2) * T₁ - π * a^(-5/2) * T₂.
  have h_mul : a ^ (-(1/2 : ℝ)) * ((-π * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π / a * (n : ℝ) ^ 2)) *
      (-a ^ (-(2 : ℝ)))) =
      π * a ^ (-(5/2 : ℝ)) * ∑' n : ℤ, (n : ℝ) ^ 2 * Real.exp (-π / a * (n : ℝ) ^ 2) := by
    rw [← h_prod_exp]; ring
  linarith [hd_lhs_eq_rhs, h_mul]

end Real
