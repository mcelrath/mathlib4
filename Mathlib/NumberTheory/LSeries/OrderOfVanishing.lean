/-
Copyright (c) 2025 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Norm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Orders of vanishing and the functional equation

We show that the functional equation for completed Dirichlet L-functions preserves
meromorphic orders of vanishing.

## Main results

* `IsPrimitive.meromorphicOrderAt_completedLFunction_one_sub`: the meromorphic order of
  `completedLFunction χ` at `1 - s₀` equals that of `completedLFunction χ⁻¹` at `s₀`.
-/

open DirichletCharacter Complex Filter Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private lemma natCast_mem_slitPlane : (N : ℂ) ∈ slitPlane :=
  ofReal_mem_slitPlane.2 (Nat.cast_pos.2 (NeZero.pos N))

private lemma analyticAt_natCast_cpow_sub (s₀ : ℂ) :
    AnalyticAt ℂ (fun s ↦ (N : ℂ) ^ (s - 1 / 2)) s₀ :=
  analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) natCast_mem_slitPlane

private lemma natCast_cpow_sub_ne_zero (s : ℂ) : (N : ℂ) ^ (s - 1 / 2) ≠ 0 :=
  cpow_ne_zero_iff.2 (.inl (Nat.cast_ne_zero.2 (NeZero.ne N)))

private lemma rootNumber_ne_zero (hχ : IsPrimitive χ) : rootNumber χ ≠ 0 := by
  intro h
  have := IsPrimitive.norm_rootNumber hχ
  rw [h, norm_zero] at this
  exact zero_ne_one this

namespace IsPrimitive

/-- The functional equation for completed Dirichlet L-functions preserves meromorphic orders:
`ord_{1-s₀}(Λ(χ, ·)) = ord_{s₀}(Λ(χ⁻¹, ·))`. -/
theorem meromorphicOrderAt_completedLFunction_one_sub (hχ : IsPrimitive χ) (s₀ : ℂ) :
    meromorphicOrderAt (completedLFunction χ) (1 - s₀) =
    meromorphicOrderAt (completedLFunction χ⁻¹) s₀ := by
  -- Step 1: Pull back through (1 - ·)
  have h_comp : meromorphicOrderAt (completedLFunction χ ∘ (1 - ·)) s₀ =
      meromorphicOrderAt (completedLFunction χ) (1 - s₀) := by
    apply meromorphicOrderAt_comp_of_deriv_ne_zero (f := completedLFunction χ)
    · fun_prop
    · rw [deriv_const_sub]; simp
  rw [← h_comp]
  -- Step 2: Use the functional equation to rewrite the composition
  have h_eq : (completedLFunction χ ∘ (1 - ·)) =ᶠ[𝓝[≠] s₀]
      fun s ↦ (N : ℂ) ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
    apply Eventually.filter_mono nhdsWithin_le_nhds
    exact Eventually.of_forall fun s ↦ IsPrimitive.completedLFunction_one_sub hχ s
  rw [meromorphicOrderAt_congr h_eq]
  -- Step 3: Strip the nonvanishing analytic prefix
  have h_ana : AnalyticAt ℂ (fun s ↦ (N : ℂ) ^ (s - 1 / 2) * rootNumber χ) s₀ :=
    (analyticAt_natCast_cpow_sub s₀).mul analyticAt_const
  have h_nz : (N : ℂ) ^ (s₀ - 1 / 2) * rootNumber χ ≠ 0 :=
    mul_ne_zero (natCast_cpow_sub_ne_zero s₀) (rootNumber_ne_zero hχ)
  exact meromorphicOrderAt_mul_of_ne_zero h_ana h_nz

end IsPrimitive

end DirichletCharacter
