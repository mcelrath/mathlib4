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

@[simp] theorem chi_neg3_at_2 : chi_neg3 2 = (-1 : ℂ) := by
  norm_num [chi_neg3, chi_neg3_int, MulChar.ringHomComp]

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

end DirichletCharacter
