/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.DirichletEta
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Analysis.Complex.Basic

/-!
# Borromean-twisted Dirichlet L-functions
-/

@[expose] public section

noncomputable section

open Complex

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The Borromean twist factor at the prime `2`. -/
noncomputable def borromeanTwist (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
   1 - χ 2 * (2 : ℂ) ^ (1 - s)

/-- The Borromean-twisted Dirichlet `L`-function. -/
noncomputable def LFunction_twisted (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
   borromeanTwist χ s * DirichletCharacter.LFunction χ s

omit [NeZero N] in
theorem borromeanTwist_trivial (χ : DirichletCharacter ℂ N) (s : ℂ) (hχ : χ 2 = 0) :
    borromeanTwist χ s = 1 := by
  simp [borromeanTwist, hχ]

theorem LFunction_twisted_eq_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hχ : χ 2 = 0) :
     LFunction_twisted χ s = LFunction χ s := by
   simp [LFunction_twisted, borromeanTwist_trivial, hχ]

theorem LFunction_twisted_one_eq_dirichletEta {s : ℂ} (hs : s ≠ 1) :
    LFunction_twisted (1 : DirichletCharacter ℂ 1) s = DirichletEta.dirichletEta s := by
  have h2 : (1 : DirichletCharacter ℂ 1) 2 = 1 := by
    change (1 : DirichletCharacter ℂ 1) (1 : ZMod 1) = 1
    simp
  rw [LFunction_twisted, DirichletEta.dirichletEta_ne_one s hs, LFunction_modOne_eq]
  rw [borromeanTwist, h2]
  ring

omit [NeZero N] in
theorem norm_char_two_le_one (χ : DirichletCharacter ℂ N) :
    ‖χ 2‖ ≤ 1 := by
  simpa using χ.norm_le_one (2 : ZMod N)

theorem borromeanTwist_ne_zero_of_re_eq_half
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s.re = 1 / 2) :
    borromeanTwist χ s ≠ 0 := by
  by_cases hχ : χ 2 = 0
  · rw [borromeanTwist_trivial χ s hχ]
    exact one_ne_zero
  · intro htw
    have hu : IsUnit (2 : ZMod N) := by
      by_contra hu
      exact hχ (χ.map_nonunit hu)
    have hpow : ‖(2 : ℂ) ^ (1 - s)‖ = Real.sqrt 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      have hre : (1 - s).re = (1 : ℝ) / 2 := by
        rw [sub_re, hs]
        norm_num
      rw [hre, Real.sqrt_eq_rpow]
    have hone : ‖χ 2 * (2 : ℂ) ^ (1 - s)‖ = 1 := by
      have hEq : χ 2 * (2 : ℂ) ^ (1 - s) = 1 := by
        exact sub_eq_zero.mp htw |>.symm
      rw [hEq, norm_one]
    have hunitnorm : ‖χ 2‖ = 1 := by
      simpa [hu.unit_spec] using χ.unit_norm_eq_one hu.unit
    rw [norm_mul, hunitnorm, hpow] at hone
    nlinarith [Real.one_lt_sqrt_two, hone]

theorem LFunction_twisted_zero_imp_LFunction_zero_of_re_eq_half
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s.re = 1 / 2)
    (h : LFunction_twisted χ s = 0) :
    LFunction χ s = 0 := by
  have htw : borromeanTwist χ s ≠ 0 := borromeanTwist_ne_zero_of_re_eq_half χ s hs
  rw [LFunction_twisted] at h
  exact (mul_eq_zero.mp h).resolve_left htw

end DirichletCharacter
