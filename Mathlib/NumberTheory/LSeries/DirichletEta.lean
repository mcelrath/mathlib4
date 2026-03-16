/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Data.PNat.Basic

@[expose] public section

/-!
# Dirichlet Eta Function

## Main definitions:

* `dirichletEta`: the Dirichlet eta function `η(s) = ∑_{n=1}^∞ (-1)^(n-1) / n^s`.

## Main results:

* `dirichletEta_one`: `η(1) = ln(2)` (the alternating harmonic series).
* `alternating_zeta_formula`: For Re(s) > 1, the series `∑ (-1)^(n-1)/n^s = (1 - 2^(1-s)) ζ(s)`.

## References

* Apostol, T. M. (1976). Introduction to Analytic Number Theory. Springer.
* NIST Digital Library of Mathematical Functions, §25.11 "Hurwitz and Lerch Zeta Functions"

## Implementation notes

The Dirichlet eta function is defined as an alternating series that converges for `Re(s) > 0`,
providing analytic continuation of the Riemann zeta function to the critical strip.

The definition uses a piecewise form to handle the removable singularity at s = 1, where
the indeterminate form `(1 - 2^(1-1)) · ζ(1) = 0 · ∞` would otherwise be problematic.

For `s ≠ 1`, the series equals `(1 - 2^(1-s)) ζ(s)`, which follows from:
```
ζ(s) = ∑ 1/n^s = (∑ 1/n^s over n odd) + (∑ 1/n^s over n even)
     = (∑ 1/n^s over n odd) + 2^(-s) · (∑ 1/m^s)
     = (∑ 1/n^s over n odd) + 2^(-s) · ζ(s)

So: (1 - 2^(-s)) ζ(s) = ∑ 1/n^s over n odd
                       = ∑ (-1)^(n-1) / n^s   (alternating series)
                       = η(s)
```

Multiplying by 2^s gives: (2^s - 1) ζ(s) = 2^s η(s), or η(s) = (1 - 2^(1-s)) ζ(s).

The value `η(1) = log 2` is the alternating harmonic series 1 - 1/2 + 1/3 - 1/4 + ... = log 2,
which is justified by continuity: `lim_{s→1} (1 - 2^{1-s}) ζ(s) = log 2` because
`(1 - 2^{1-s}) / (s - 1) → log 2` and `(s - 1) ζ(s) → 1` as `s → 1`.

-/

noncomputable section

open Complex

namespace DirichletEta

/-! ## Definition -/

/-- The Dirichlet eta function `η(s) = ∑_{n=1}^∞ (-1)^(n-1) / n^s`.

This is defined piecewise to handle the removable singularity at s = 1:
- At s = 1: η(1) = ln(2) (the alternating harmonic series)
- For s ≠ 1: η(s) = (1 - 2^(1-s)) ζ(s)

The piecewise definition avoids the indeterminate form `0 · ∞` that would arise
from evaluating `(1 - 2^(1-1)) · ζ(1)` directly. -/
def dirichletEta (s : ℂ) : ℂ :=
  if s = 1 then log 2
  else (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-! ## Basic properties -/

/-- At s = 1, the Dirichlet eta function equals ln(2).

This is the alternating harmonic series: η(1) = 1 - 1/2 + 1/3 - 1/4 + ... = ln(2). -/
@[simp] theorem dirichletEta_one : dirichletEta 1 = log 2 := by
  simp [dirichletEta]

/-- For s ≠ 1, the eta function satisfies η(s) = (1 - 2^(1-s)) ζ(s). -/
theorem dirichletEta_ne_one (s : ℂ) (hs : s ≠ 1) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  simp [dirichletEta, hs]


end DirichletEta

/-! ## Euler's alternating zeta formula

The following results prove that for Re(s) > 1, the alternating series
`∑ (-1)^(n-1)/n^s` equals `(1 - 2^(1-s)) ζ(s)`.

These were previously in `EulerFormula.lean` and are merged here because
the result belongs with the eta function definition.
-/

namespace DirichletEta

open scoped Topology

/-- The even terms of the zeta sum equal 2^(-s) times the full zeta sum. -/
lemma tsum_zeta_even {s : ℂ} (hs : 1 < s.re) :
    ∑' (k : ℕ), 1 / (2 * (k + 1) : ℂ) ^ s = (2 : ℂ) ^ (-s) * riemannZeta s := by
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have key : ∀ k : ℕ, 1 / (2 * (k + 1) : ℂ) ^ s = (2 : ℂ) ^ (-s) * (1 / (k + 1 : ℂ) ^ s) := by
    intro k
    have hsplit : (2 * (k + 1) : ℂ) ^ s = (2 : ℂ) ^ s * (k + 1 : ℂ) ^ s := by
      have h := natCast_mul_natCast_cpow 2 (k + 1) s
      simp only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
      convert h using 2
    rw [hsplit]; simp [cpow_neg, one_div, mul_comm]
  simp_rw [key]
  rw [tsum_mul_left, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-- The odd terms of the zeta sum equal (1 - 2^(-s)) times the full zeta sum. -/
lemma tsum_zeta_odd {s : ℂ} (hs : 1 < s.re) :
    ∑' (k : ℕ), 1 / (2 * k + 1 : ℂ) ^ s = (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s
  have hf : Summable f := by
    refine ((Complex.summable_one_div_nat_cpow.mpr hs).comp_injective
      (add_left_injective 1)).congr fun n => ?_
    simp only [Function.comp]; congr 1; push_cast; ring
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective (fun a b h => by omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective (fun a b h => by omega)
  have hsplit := tsum_even_add_odd he ho
  have hfk_eq_zeta : ∑' k, f k = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have heven_zeta : ∑' k, f (2 * k + 1) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    refine (tsum_zeta_even hs).symm ▸ tsum_congr fun k => ?_
    simp only [f]; congr 1; push_cast; ring_nf
  have hodd_match : ∀ k : ℕ, f (2 * k) = 1 / (2 * ↑k + 1 : ℂ) ^ s := by
    intro k; simp only [f]; congr 1; push_cast; ring
  rw [hfk_eq_zeta, heven_zeta] at hsplit
  simp_rw [hodd_match] at hsplit
  linear_combination hsplit

/-- The alternating sum equals the odd terms minus the even terms. -/
lemma alternating_eq_odd_sub_even {s : ℂ} (hs : 1 < s.re) :
    ∑' (n : ℕ+), (-1 : ℂ) ^ ((n : ℕ) - 1) / (n : ℂ) ^ s =
    (∑' k : ℕ, 1 / (2 * k + 1 : ℂ) ^ s) - (∑' k : ℕ, 1 / (2 * (k + 1) : ℂ) ^ s) := by
  -- Step 1: Reindex ℕ+ → ℕ
  rw [tsum_pnat_eq_tsum_succ (f := fun m => (-1 : ℂ) ^ (m - 1) / (m : ℂ) ^ s)]
  -- Step 2: Simplify the shifted terms
  have step1 : (fun n : ℕ => (-1 : ℂ) ^ ((n + 1) - 1) / ((n + 1 : ℕ) : ℂ) ^ s) =
      fun (n : ℕ) => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s := by
    ext n; simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [step1]
  -- Step 3: Split by parity using tsum_even_add_odd
  set h : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s
  -- Summability
  have hf : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    refine ((Complex.summable_one_div_nat_cpow.mpr hs).comp_injective
      (add_left_injective 1)).congr fun n => ?_
    simp only [Function.comp]; congr 1; push_cast; ring
  have hh : Summable h := by
    refine hf.alternating.congr fun n => ?_
    simp only [h, mul_one_div]
  have hhe : Summable fun k => h (2 * k) := hh.comp_injective (fun a b hab => by omega)
  have hho : Summable fun k => h (2 * k + 1) := hh.comp_injective (fun a b hab => by omega)
  have hsplit := tsum_even_add_odd hhe hho
  -- h(2k) = 1/(2k+1)^s since (-1)^(2k) = 1
  have h_even : ∀ k, h (2 * k) = 1 / (2 * ↑k + 1 : ℂ) ^ s := by
    intro k; simp only [h, pow_mul, neg_one_sq, one_pow, one_div]; push_cast; ring
  -- h(2k+1) = -1/(2(k+1))^s since (-1)^(2k+1) = -1
  have h_odd : ∀ k, h (2 * k + 1) = -(1 / (2 * (↑k + 1) : ℂ) ^ s) := by
    intro k; simp only [h, pow_succ, pow_mul]; push_cast; ring_nf
  simp_rw [h_even, h_odd] at hsplit
  rw [tsum_neg] at hsplit
  -- hsplit : ∑ 1/(2k+1)^s + (- ∑ 1/(2(k+1))^s) = ∑ h(n)
  -- Goal: ∑ h(n) = ∑ 1/(2k+1)^s - ∑ 1/(2(k+1))^s
  linear_combination hsplit.symm

/-- **Euler's alternating zeta formula**: For Re(s) > 1, the alternating zeta sum equals
`(1 - 2^(1-s)) ζ(s)`.

This establishes that the series definition of the Dirichlet eta function agrees with
the functional equation `η(s) = (1 - 2^(1-s)) ζ(s)` for Re(s) > 1. -/
theorem alternating_zeta_formula {s : ℂ} (hs : 1 < s.re) :
    ∑' (n : ℕ+), (-1 : ℂ) ^ ((n : ℕ) - 1) / (n : ℂ) ^ s =
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [alternating_eq_odd_sub_even hs]
  rw [tsum_zeta_odd hs, tsum_zeta_even hs]
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have key : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    rw [show (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) from by
      rw [cpow_one]]
    rw [← cpow_add _ _ h2_ne]; ring_nf
  calc (1 - (2 : ℂ) ^ (-s)) * riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s
      = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by ring
    _ = riemannZeta s - ((2 : ℂ) ^ (-s) + (2 : ℂ) ^ (-s)) * riemannZeta s := by ring
    _ = riemannZeta s - (2 : ℂ) * (2 : ℂ) ^ (-s) * riemannZeta s := by ring
    _ = riemannZeta s - (2 : ℂ) ^ (1 - s) * riemannZeta s := by rw [key]
    _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by ring

/-- For Re(s) > 1, the alternating series equals `dirichletEta s`. -/
theorem alternating_series_eq_dirichletEta {s : ℂ} (hs : 1 < s.re) :
    ∑' (n : ℕ+), (-1 : ℂ) ^ ((n : ℕ) - 1) / (n : ℂ) ^ s = dirichletEta s := by
  have hs1 : s ≠ 1 := by
    intro h; simp [h] at hs
  rw [alternating_zeta_formula hs, dirichletEta_ne_one s hs1]

/-!
## Extension to Re(s) > 0

We extend the theory of the Dirichlet eta function to the half-plane `{s | 0 < s.re}`.
-/

/-- The Dirichlet eta function is differentiable at `s ≠ 1`. -/
theorem differentiableAt_dirichletEta_ne_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ dirichletEta s := by
  have : DifferentiableAt ℂ (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) s := by
    apply DifferentiableAt.mul
    · exact (differentiableAt_const _).sub
        (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero))
    · exact differentiableAt_riemannZeta hs
  exact this.congr_of_eventuallyEq <| (isOpen_ne.eventually_mem hs).mono
    fun t (ht : t ≠ 1) => by simp [dirichletEta_ne_one t ht]

/-- The function `s ↦ 1 - 2 ^ (1 - s)` has derivative `log 2` at `s = 1`. -/
private lemma hasDerivAt_one_sub_two_cpow :
    HasDerivAt (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) (Complex.log 2) 1 := by
  have hd : HasDerivAt (fun s : ℂ => (1 : ℂ) - s) (-1) 1 := by
    have := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (1 : ℂ))
    simpa using this
  have h1 : HasDerivAt (fun s : ℂ => (2 : ℂ) ^ ((1 : ℂ) - s)) (-Complex.log 2) 1 := by
    have := HasDerivAt.const_cpow hd (Or.inl (two_ne_zero' ℂ))
    simp only [sub_self, cpow_zero] at this
    convert this using 1; ring
  have := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub h1
  simpa using this

/-- The Dirichlet eta function is differentiable at every `s` with `0 < s.re`. -/
theorem differentiableAt_dirichletEta {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ dirichletEta s := by
  rcases ne_or_eq s 1 with hs1 | rfl
  · exact differentiableAt_dirichletEta_ne_one hs1
  -- At s = 1, use the removable singularity theorem
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact differentiableAt_dirichletEta_ne_one ht
  -- Continuity at s = 1: decompose dirichletEta near 1 as G * H where
  -- G(s) = (s - 1) * ζ(s) → 1 (residue of ζ at s = 1)
  -- H(s) = (1 - 2^(1-s)) / (s - 1) → log 2 (derivative of 1 - 2^(1-s))
  let G := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  let H := Function.update (fun s => (1 - (2 : ℂ) ^ (1 - s)) / (s - 1)) 1 (Complex.log 2)
  suffices hc : ContinuousAt (G * H) 1 by
    apply ContinuousAt.congr hc
    filter_upwards with t
    rcases eq_or_ne t 1 with rfl | ht'
    · simp [G, H, dirichletEta_one]
    · simp only [G, H, Pi.mul_apply, Function.update_of_ne ht']
      rw [dirichletEta_ne_one t ht']
      have : (t - 1) ≠ 0 := sub_ne_zero.mpr ht'
      field_simp
  refine ContinuousAt.mul ?_ ?_
  · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
  · have := hasDerivAt_one_sub_two_cpow.continuousAt_div
    simp only [sub_self, cpow_zero, sub_zero] at this
    simpa only [H, continuousAt_update_same] using this

/-- The Dirichlet eta function is differentiable on `{s | 0 < s.re}`. -/
theorem differentiableOn_dirichletEta :
    DifferentiableOn ℂ dirichletEta {s | 0 < s.re} :=
  fun _ hs => (differentiableAt_dirichletEta hs).differentiableWithinAt

/-- The Dirichlet eta function is analytic on `{s | 0 < s.re}`. -/
theorem analyticOnNhd_dirichletEta :
    AnalyticOnNhd ℂ dirichletEta {s | 0 < s.re} :=
  differentiableOn_dirichletEta.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end DirichletEta
