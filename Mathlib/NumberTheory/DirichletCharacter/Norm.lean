/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Norm of the root number of a Dirichlet character

We prove that the root number `ε(χ)` of a primitive Dirichlet character `χ` has absolute value 1.

## Strategy

We use two key ingredients:
1. The functional equation applied twice to show `rootNumber χ * rootNumber χ⁻¹ = 1`.
2. The identity `‖rootNumber χ‖ = ‖rootNumber χ⁻¹‖` from conjugation of the Gauss sum.
Together these give `‖rootNumber χ‖² = 1`.

## Main results

* `DirichletCharacter.conductor_inv` : `conductor χ⁻¹ = conductor χ`
* `DirichletCharacter.IsPrimitive.inv` : primitivity of the inverse character
* `DirichletCharacter.IsPrimitive.rootNumber_mul_rootNumber_inv` : `ε(χ) · ε(χ⁻¹) = 1`
* `DirichletCharacter.IsPrimitive.norm_rootNumber` : `‖rootNumber χ‖ = 1`
-/

@[expose] public section

open DirichletCharacter Complex Finset MulChar

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ### Conductor and primitivity of the inverse character -/

section Conductor

variable {R : Type*} [CommMonoidWithZero R]

omit [NeZero N] in
/-- `χ⁻¹` factors through `d` if and only if `χ` does. -/
lemma factorsThrough_inv_iff {χ : DirichletCharacter R N} {d : ℕ} :
    FactorsThrough χ⁻¹ d ↔ FactorsThrough χ d := by
  constructor
  · rintro ⟨hd, χ₀, hχ₀⟩
    exact ⟨hd, χ₀⁻¹, by rw [map_inv, ← hχ₀, inv_inv]⟩
  · rintro ⟨hd, χ₀, hχ₀⟩
    refine ⟨hd, χ₀⁻¹, ?_⟩
    rw [hχ₀, ← map_inv (changeLevel hd)]

omit [NeZero N] in
/-- The conductor of a Dirichlet character is invariant under inversion. -/
@[simp]
lemma conductor_inv (χ : DirichletCharacter R N) :
    conductor χ⁻¹ = conductor χ := by
  simp only [conductor, conductorSet]
  congr 1; ext d; exact factorsThrough_inv_iff

omit [NeZero N] in
/-- The inverse of a primitive Dirichlet character is primitive. -/
lemma IsPrimitive.inv {χ : DirichletCharacter R N} (hχ : IsPrimitive χ) :
    IsPrimitive χ⁻¹ := by
  rwa [IsPrimitive, conductor_inv]

end Conductor

/-! ### Gauss sum norm identity -/

/-- Complex conjugation of a Gauss sum: `conj(g(χ,ψ)) = g(χ⁻¹, ψ⁻¹)`. -/
lemma starRingEnd_gaussSum {χ : DirichletCharacter ℂ N} (ψ : AddChar (ZMod N) ℂ) :
    starRingEnd ℂ (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
  simp only [gaussSum, map_sum, map_mul]
  congr 1; ext a; congr 1
  · exact MulChar.star_apply' χ a
  · exact AddChar.starComp_apply
      (by rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne N)) a

/-- `‖gaussSum χ ψ‖ = ‖gaussSum χ⁻¹ ψ‖` for Dirichlet characters valued in `ℂ`. -/
lemma norm_gaussSum_eq_norm_gaussSum_inv {χ : DirichletCharacter ℂ N}
    (ψ : AddChar (ZMod N) ℂ) :
    ‖gaussSum χ ψ‖ = ‖gaussSum χ⁻¹ ψ‖ := by
  -- conj(g(χ,ψ)) = g(χ⁻¹,ψ⁻¹), so ‖g(χ,ψ)‖ = ‖g(χ⁻¹,ψ⁻¹)‖
  have h1 : ‖gaussSum χ ψ‖ = ‖gaussSum χ⁻¹ ψ⁻¹‖ := by
    rw [← starRingEnd_gaussSum, norm_conj]
  -- ψ⁻¹ = mulShift ψ (-1), so g(χ⁻¹,ψ⁻¹) = χ⁻¹(-1)⁻¹ * g(χ⁻¹,ψ)
  -- via gaussSum_mulShift: χ(a) * g(χ, mulShift ψ a) = g(χ, ψ)
  have h2 : ‖gaussSum χ⁻¹ ψ⁻¹‖ = ‖gaussSum χ⁻¹ ψ‖ := by
    rw [ψ.inv_mulShift]
    have key := gaussSum_mulShift χ⁻¹ ψ (-1 : (ZMod N)ˣ)
    simp only [Units.val_neg, Units.val_one] at key
    rw [← key, norm_mul]
    have : ‖χ⁻¹ (-1 : ZMod N)‖ = 1 := by
      rw [show (-1 : ZMod N) = ↑(-1 : (ZMod N)ˣ) from rfl]
      exact unit_norm_eq_one χ⁻¹ (-1)
    rw [this, one_mul]
  rw [h1, h2]

/-! ### Root number product formula and norm -/

namespace IsPrimitive

variable {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ)
include hχ

/-- `rootNumber χ * rootNumber χ⁻¹ = 1` for primitive `χ`. -/
theorem rootNumber_mul_rootNumber_inv :
    rootNumber χ * rootNumber χ⁻¹ = 1 := by
  classical
  -- Handle N = 1
  rcases eq_or_ne N 1 with rfl | hN
  · have h1 := level_one χ; subst h1; simp [rootNumber_modOne]
  -- χ ≠ 1 since primitive with N > 1
  have hχ_ne : χ ≠ 1 := by
    intro h; rw [h, IsPrimitive, conductor_one (NeZero.ne N)] at hχ; exact hN hχ.symm
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Λ(χ, 2) ≠ 0
  have hΛ : completedLFunction χ 2 ≠ 0 := by
    have hL : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inl hχ_ne) (by norm_num)
    rw [LFunction_eq_completed_div_gammaFactor χ 2 (.inl (by norm_num))] at hL
    exact (div_ne_zero_iff.mp hL).1
  -- FE for χ at s = -1: Λ(χ, 2) = N^(-3/2) · ε(χ) · Λ(χ⁻¹, -1)
  have fe := completedLFunction_one_sub hχ (-1 : ℂ)
  rw [show (1 : ℂ) - -1 = 2 from by ring] at fe
  -- FE for χ⁻¹ at s = 2: Λ(χ⁻¹, -1) = N^(3/2) · ε(χ⁻¹) · Λ(χ, 2)
  have fe_inv := completedLFunction_one_sub (hχ.inv) (1 - (-1 : ℂ))
  rw [show (1 : ℂ) - (1 - -1) = -1 from by ring, inv_inv,
    show (1 - (-1 : ℂ)) - 1 / 2 = 3 / 2 from by ring,
    show (1 : ℂ) - -1 = 2 from by ring] at fe_inv
  -- Substitute
  rw [fe_inv] at fe
  -- Simplify N^(-3/2) · N^(3/2) = 1
  have hpow : (N : ℂ) ^ ((-1 : ℂ) - 1 / 2) * ((N : ℂ) ^ ((3 : ℂ) / 2)) = 1 := by
    rw [← cpow_add _ _ hN_ne, show (-1 : ℂ) - 1 / 2 + 3 / 2 = 0 from by ring, cpow_zero]
  rw [show (N : ℂ) ^ ((-1 : ℂ) - 1 / 2) * rootNumber χ *
    ((N : ℂ) ^ ((3 : ℂ) / 2) * rootNumber χ⁻¹ * completedLFunction χ 2) =
    ((N : ℂ) ^ ((-1 : ℂ) - 1 / 2) * (N : ℂ) ^ ((3 : ℂ) / 2)) *
    (rootNumber χ * rootNumber χ⁻¹) * completedLFunction χ 2 from by ring,
    hpow, one_mul] at fe
  rw [show rootNumber χ * rootNumber χ⁻¹ * completedLFunction χ 2 =
    completedLFunction χ 2 * (rootNumber χ * rootNumber χ⁻¹) from by ring] at fe
  exact (mul_right_eq_self₀.mp fe.symm).resolve_right hΛ

omit hχ in
/-- `‖rootNumber χ‖ = ‖rootNumber χ⁻¹‖` for primitive `χ`. -/
lemma norm_rootNumber_eq :
    ‖rootNumber χ‖ = ‖rootNumber χ⁻¹‖ := by
  classical
  simp only [rootNumber, norm_div]
  congr 1; congr 1
  · exact norm_gaussSum_eq_norm_gaussSum_inv _
  · -- Same parity: χ.Even ↔ χ⁻¹.Even
    have h_parity : χ.Even ↔ χ⁻¹.Even := by
      simp only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_eq_one]
    simp only [h_parity]

/-- The norm of the root number equals 1 for primitive Dirichlet characters. -/
theorem norm_rootNumber :
    ‖rootNumber χ‖ = 1 := by
  have h_prod := rootNumber_mul_rootNumber_inv hχ
  have h_norm_eq := @norm_rootNumber_eq N _ χ
  have h1 : ‖rootNumber χ‖ * ‖rootNumber χ⁻¹‖ = 1 := by
    rw [← norm_mul, h_prod, norm_one]
  rw [h_norm_eq] at h1
  have hnn : 0 ≤ ‖rootNumber χ⁻¹‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖rootNumber χ⁻¹‖ - 1)]

end IsPrimitive

end DirichletCharacter
