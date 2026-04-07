/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Quadratic Dirichlet characters for `ℚ(ζ₁₂)`

This file defines the quadratic Dirichlet characters `χ_{-3}`, `χ_{-4}`, and `χ₁₂`.

The characters `χ_{-3}` and `χ_{-4}` are defined at their primitive levels `3` and `4`;
`χ₁₂` is their product after changing levels to `12`.
-/

@[expose] public section

noncomputable section

namespace DirichletCharacter

def chi_neg3_int : DirichletCharacter ℤ 3 where
  toFun a :=
    match a with
    | 0 => 0
    | 1 => 1
    | 2 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- The primitive quadratic character of conductor `3`. -/
noncomputable def chi_neg3 : DirichletCharacter ℂ 3 :=
  MulChar.ringHomComp chi_neg3_int (Int.castRingHom ℂ)

/-- The primitive quadratic character of conductor `4`. -/
noncomputable def chi_neg4 : DirichletCharacter ℂ 4 :=
  MulChar.ringHomComp ZMod.χ₄ (Int.castRingHom ℂ)

/-- The quadratic character of conductor `12`. -/
noncomputable def chi_12 : DirichletCharacter ℂ 12 :=
  DirichletCharacter.mul chi_neg3 chi_neg4

@[simp] theorem chi_neg3_at_1 : chi_neg3 1 = (1 : ℂ) := by
  simp [chi_neg3, chi_neg3_int, MulChar.ringHomComp]

@[simp] theorem chi_neg3_at_2 : chi_neg3 2 = (-1 : ℂ) := by
  norm_num [chi_neg3, chi_neg3_int, MulChar.ringHomComp]

@[simp] theorem chi_neg4_at_1 : chi_neg4 1 = (1 : ℂ) := by
  simp [chi_neg4, MulChar.ringHomComp]

@[simp] theorem chi_neg4_at_2 : chi_neg4 2 = 0 := by
  norm_num [chi_neg4, ZMod.χ₄, MulChar.ringHomComp]

theorem chi_12_eq_mul :
    chi_12 =
      DirichletCharacter.changeLevel (show 3 ∣ 12 by decide) chi_neg3 *
        DirichletCharacter.changeLevel (show 4 ∣ 12 by decide) chi_neg4 :=
  rfl

@[simp] theorem chi_12_at_2 : chi_12 2 = 0 := by
  have hcop : ¬ Nat.Coprime 2 12 := by decide
  have hunit : ¬ IsUnit (2 : ZMod 12) := by
    intro hu
    exact hcop ((ZMod.isUnit_iff_coprime _ _).mp hu)
  rw [chi_12_eq_mul, MulChar.mul_apply, MulChar.map_nonunit _ hunit, zero_mul]

-- Value lemmas for nontriviality proofs

@[simp] theorem chi_neg4_at_3 : chi_neg4 3 = (-1 : ℂ) := by
  norm_num [chi_neg4, ZMod.χ₄, MulChar.ringHomComp]

@[simp] theorem chi_12_at_5 : chi_12 5 = (-1 : ℂ) := by
  rw [chi_12_eq_mul, MulChar.mul_apply]
  set u : (ZMod 12)ˣ := Units.mkOfMulEqOne 5 5 (by decide) with hu_def
  have hu5 : (u : ZMod 12) = 5 := rfl
  have h3 : (changeLevel (show 3 ∣ 12 by decide) chi_neg3) 5 = (-1 : ℂ) := by
    rw [show (5 : ZMod 12) = ↑u from hu5.symm,
        changeLevel_eq_cast_of_dvd chi_neg3 (show 3 ∣ 12 by decide) u]
    have hcast3 : (u : ZMod 12).cast = (2 : ZMod 3) := by decide
    rw [hcast3]; norm_num [chi_neg3, chi_neg3_int, MulChar.ringHomComp]
  have h4 : (changeLevel (show 4 ∣ 12 by decide) chi_neg4) 5 = (1 : ℂ) := by
    rw [show (5 : ZMod 12) = ↑u from hu5.symm,
        changeLevel_eq_cast_of_dvd chi_neg4 (show 4 ∣ 12 by decide) u]
    have hcast4 : (u : ZMod 12).cast = (1 : ZMod 4) := by decide
    rw [hcast4]; norm_num [chi_neg4, ZMod.χ₄, MulChar.ringHomComp]
  rw [h3, h4]; ring

@[simp] theorem chi_12_at_1 : chi_12 1 = (1 : ℂ) := by
  simp [chi_12, mul, changeLevel, MulChar.ringHomComp, chi_neg3, chi_neg3_int, chi_neg4, ZMod.χ₄]

@[simp] theorem chi_12_at_7 : chi_12 7 = (-1 : ℂ) := by
  rw [chi_12_eq_mul, MulChar.mul_apply]
  set u : (ZMod 12)ˣ := Units.mkOfMulEqOne 7 7 (by decide) with hu_def
  have hu7 : (u : ZMod 12) = 7 := rfl
  have h3 : (changeLevel (show 3 ∣ 12 by decide) chi_neg3) 7 = (1 : ℂ) := by
    rw [show (7 : ZMod 12) = ↑u from hu7.symm,
        changeLevel_eq_cast_of_dvd chi_neg3 (show 3 ∣ 12 by decide) u]
    have hcast3 : (u : ZMod 12).cast = (1 : ZMod 3) := by decide
    rw [hcast3]; norm_num [chi_neg3, chi_neg3_int, MulChar.ringHomComp]
  have h4 : (changeLevel (show 4 ∣ 12 by decide) chi_neg4) 7 = (-1 : ℂ) := by
    rw [show (7 : ZMod 12) = ↑u from hu7.symm,
        changeLevel_eq_cast_of_dvd chi_neg4 (show 4 ∣ 12 by decide) u]
    have hcast4 : (u : ZMod 12).cast = (3 : ZMod 4) := by decide
    rw [hcast4]; norm_num [chi_neg4, ZMod.χ₄, MulChar.ringHomComp]
  rw [h3, h4]; ring

@[simp] theorem chi_12_at_11 : chi_12 11 = (1 : ℂ) := by
  rw [chi_12_eq_mul, MulChar.mul_apply]
  set u : (ZMod 12)ˣ := Units.mkOfMulEqOne 11 11 (by decide) with hu_def
  have hu11 : (u : ZMod 12) = 11 := rfl
  have h3 : (changeLevel (show 3 ∣ 12 by decide) chi_neg3) 11 = (-1 : ℂ) := by
    rw [show (11 : ZMod 12) = ↑u from hu11.symm,
        changeLevel_eq_cast_of_dvd chi_neg3 (show 3 ∣ 12 by decide) u]
    have hcast3 : (u : ZMod 12).cast = (2 : ZMod 3) := by decide
    rw [hcast3]; norm_num [chi_neg3, chi_neg3_int, MulChar.ringHomComp]
  have h4 : (changeLevel (show 4 ∣ 12 by decide) chi_neg4) 11 = (-1 : ℂ) := by
    rw [show (11 : ZMod 12) = ↑u from hu11.symm,
        changeLevel_eq_cast_of_dvd chi_neg4 (show 4 ∣ 12 by decide) u]
    have hcast4 : (u : ZMod 12).cast = (3 : ZMod 4) := by decide
    rw [hcast4]; norm_num [chi_neg4, ZMod.χ₄, MulChar.ringHomComp]
  rw [h3, h4]; ring

-- Nontriviality theorems

theorem chi_neg3_ne_one : chi_neg3 ≠ 1 := by
  intro h
  have h1 : chi_neg3 2 = (1 : DirichletCharacter ℂ 3) 2 := by rw [h]
  rw [chi_neg3_at_2, MulChar.one_apply (by decide : IsUnit (2 : ZMod 3))] at h1
  norm_num at h1

theorem chi_neg4_ne_one : chi_neg4 ≠ 1 := by
  intro h
  have h1 : chi_neg4 3 = (1 : DirichletCharacter ℂ 4) 3 := by rw [h]
  rw [chi_neg4_at_3, MulChar.one_apply (by decide : IsUnit (3 : ZMod 4))] at h1
  norm_num at h1

theorem chi_12_ne_one : chi_12 ≠ 1 := by
  intro h
  have h1 : chi_12 5 = (1 : DirichletCharacter ℂ 12) 5 := by rw [h]
  rw [chi_12_at_5, MulChar.one_apply (by decide : IsUnit (5 : ZMod 12))] at h1
  norm_num at h1

end DirichletCharacter
