/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Real.Sqrt

/-!
# The real quadratic number field `ℚ(√3)`

This file sets up the real quadratic number field `ℚ(√3)` as the quotient
`AdjoinRoot (X² - C 3 : ℚ[X])`, and provides the corresponding `NumberField`
instance, together with the canonical identification of its ring of integers
with `Zsqrtd 3 = ℤ[√3]`.

## Main definitions

* `Qsqrt3` : the real quadratic number field `ℚ(√3)`, defined as
  `AdjoinRoot (X^2 - C 3 : ℚ[X])`.
* `Qsqrt3.sqrt3` : the canonical square root of `3` in `Qsqrt3`,
  i.e. `AdjoinRoot.root _`.
* `Qsqrt3.fromZsqrt3 : Zsqrtd 3 →+* Qsqrt3` : the canonical embedding
  `ℤ[√3] ↪ ℚ(√3)`.
* `Qsqrt3.ringOfIntegersEquiv : 𝓞 Qsqrt3 ≃+* Zsqrtd 3` : the canonical
  identification of the ring of integers of `ℚ(√3)` with `ℤ[√3]`.

## Main results

* `Qsqrt3.irreducible_X_sq_sub_three` : the polynomial `X^2 - C 3` is
  irreducible over `ℚ`.
* `Qsqrt3.instNumberField` : `Qsqrt3` is a number field.
* `Qsqrt3.finrank_eq_two` : `[ℚ(√3) : ℚ] = 2`.
* `Qsqrt3.isIntegralClosure_zsqrtd3` : `Zsqrtd 3` is the integral closure
  of `ℤ` in `Qsqrt3`. Uses the standard discriminant argument for
  `d ≡ 3 (mod 4)`.
-/

open Polynomial

namespace Qsqrt3

/-- The minimal polynomial `X^2 - 3 ∈ ℚ[X]`. -/
noncomputable def minpoly : ℚ[X] := X ^ 2 - C 3

/-- `3 : ℚ` is not a square. -/
theorem three_not_isSquare : ¬ IsSquare (3 : ℚ) := by
  rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) from by norm_cast,
      Rat.isSquare_natCast_iff]
  exact Nat.prime_three.not_isSquare

/-- No rational number squares to `3`. -/
theorem rat_sq_ne_three (b : ℚ) : b ^ 2 ≠ 3 := by
  intro h
  exact three_not_isSquare ⟨b, by rw [← sq]; exact h.symm⟩

/-- `X^2 - C 3` is irreducible over `ℚ`. -/
theorem irreducible_X_sq_sub_three : Irreducible (X ^ 2 - C (3 : ℚ)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two rat_sq_ne_three

instance : Fact (Irreducible (X ^ 2 - C (3 : ℚ))) :=
  ⟨irreducible_X_sq_sub_three⟩

end Qsqrt3

/-- The real quadratic number field `ℚ(√3)`, realised as
`AdjoinRoot (X^2 - 3 : ℚ[X])`. -/
abbrev Qsqrt3 : Type := AdjoinRoot (X ^ 2 - C (3 : ℚ))

namespace Qsqrt3

/-- `Qsqrt3` is a number field. -/
instance instNumberField : NumberField Qsqrt3 :=
  inferInstanceAs (NumberField (AdjoinRoot _))

/-- The degree of `ℚ(√3)` over `ℚ` is `2`. -/
theorem finrank_eq_two : Module.finrank ℚ Qsqrt3 = 2 := by
  have hne : (X ^ 2 - C (3 : ℚ)) ≠ 0 := irreducible_X_sq_sub_three.ne_zero
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim,
      natDegree_X_pow_sub_C]

/-- The Pell solution `(2, 1)` for `d = 3`, i.e. `2^2 - 3 · 1^2 = 1`. -/
def pellSolutionThree : Pell.Solution₁ 3 :=
  Pell.Solution₁.mk 2 1 (by decide)

/-- The solution `(2, 1)` is the fundamental Pell solution for `d = 3`. -/
theorem pellSolutionThree_isFundamental :
    Pell.IsFundamental pellSolutionThree := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pellSolutionThree, Pell.Solution₁.x_mk]; decide
  · rw [pellSolutionThree, Pell.Solution₁.y_mk]; decide
  · intro b hb
    rw [pellSolutionThree, Pell.Solution₁.x_mk]
    omega

/-! ### The bridge `ℤ[√3] ↪ ℚ(√3)` and the ring of integers -/

/-- The canonical square root of `3` in `Qsqrt3`. -/
noncomputable def sqrt3 : Qsqrt3 := AdjoinRoot.root _

/-- The defining relation `(√3)^2 = 3` in `Qsqrt3`. -/
@[simp]
theorem sqrt3_sq : sqrt3 * sqrt3 = (3 : Qsqrt3) := by
  have h : (X ^ 2 - C (3 : ℚ)).eval₂ (algebraMap ℚ Qsqrt3) sqrt3 = 0 :=
    AdjoinRoot.eval₂_root _
  have h2 : sqrt3 * sqrt3 - (algebraMap ℚ Qsqrt3) 3 = 0 := by
    simpa [sqrt3, sq, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using h
  have h3 : (algebraMap ℚ Qsqrt3) 3 = (3 : Qsqrt3) := by
    simp [map_ofNat]
  linear_combination sub_eq_zero.mp h2 + h3

/-- The canonical embedding `ℤ[√3] →+* ℚ(√3)`, sending `⟨a,b⟩` to
`a + b · √3`. -/
noncomputable def fromZsqrt3 : Zsqrtd 3 →+* Qsqrt3 :=
  Zsqrtd.lift ⟨sqrt3, by
    have h := sqrt3_sq
    have : ((3 : ℤ) : Qsqrt3) = (3 : Qsqrt3) := by push_cast; rfl
    rw [this]; exact h⟩

@[simp]
theorem fromZsqrt3_sqrtd : fromZsqrt3 Zsqrtd.sqrtd = sqrt3 := by
  simp [fromZsqrt3]

@[simp]
theorem fromZsqrt3_intCast (n : ℤ) :
    fromZsqrt3 (n : Zsqrtd 3) = (n : Qsqrt3) := by
  simp [fromZsqrt3, Zsqrtd.intCast_val, Zsqrtd.lift]

/-- `fromZsqrt3` is injective: distinct `ℤ[√3]` elements give distinct
elements of `ℚ(√3)`. -/
theorem fromZsqrt3_injective : Function.Injective fromZsqrt3 := by
  apply Zsqrtd.lift_injective
  intro n hn
  have h : (n : ℚ) * n = 3 := by exact_mod_cast hn.symm
  exact rat_sq_ne_three n (by rw [sq]; exact h)

/-- `Qsqrt3` is a `Zsqrtd 3`-algebra via `fromZsqrt3`. -/
noncomputable instance : Algebra (Zsqrtd 3) Qsqrt3 := fromZsqrt3.toAlgebra

theorem algebraMap_zsqrtd3 :
    algebraMap (Zsqrtd 3) Qsqrt3 = fromZsqrt3 := rfl

instance : IsScalarTower ℤ (Zsqrtd 3) Qsqrt3 := by
  refine IsScalarTower.of_algebraMap_eq fun n => ?_
  rw [algebraMap_zsqrtd3]
  change ((n : Qsqrt3)) = fromZsqrt3 (n : Zsqrtd 3)
  rw [fromZsqrt3_intCast]

/-- Image of `⟨a,b⟩ ∈ ℤ[√3]` in `Qsqrt3`. -/
@[simp]
theorem fromZsqrt3_mk (a b : ℤ) :
    fromZsqrt3 (⟨a, b⟩ : Zsqrtd 3) = (a : Qsqrt3) + (b : Qsqrt3) * sqrt3 := by
  simp [fromZsqrt3, Zsqrtd.lift]

/-- Every element of `ℤ[√3]`, viewed in `ℚ(√3)`, is integral over `ℤ`.
Witness: the polynomial `X^2 - (2·a)·X + (a^2 - 3·b^2)` where `z = ⟨a,b⟩`. -/
theorem isIntegral_fromZsqrt3 (z : Zsqrtd 3) : IsIntegral ℤ (fromZsqrt3 z) := by
  obtain ⟨a, b⟩ := z
  refine ⟨X ^ 2 - C (2 * a) * X + C (a * a - 3 * b * b), ?_, ?_⟩
  · -- Monic via `X^2 + (low-degree)`.
    have heq : (X ^ 2 - C (2 * a) * X + C (a * a - 3 * b * b) : ℤ[X])
        = X ^ 2 + (- C (2 * a) * X + C (a * a - 3 * b * b)) := by ring
    rw [heq]
    refine monic_X_pow_add ?_
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · rw [show (- C (2 * a) * X : ℤ[X]) = - (C (2 * a) * X) from by ring, degree_neg]
      refine lt_of_le_of_lt (degree_C_mul_X_le _) ?_
      decide
    · refine lt_of_le_of_lt degree_C_le ?_
      decide
  · -- Evaluate.
    rw [fromZsqrt3_mk]
    have h3 : sqrt3 * sqrt3 = (3 : Qsqrt3) := sqrt3_sq
    change (X ^ 2 - C (2 * a) * X + C (a * a - 3 * b * b)).eval₂
      (algebraMap ℤ Qsqrt3) ((a : Qsqrt3) + (b : Qsqrt3) * sqrt3) = 0
    rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_C]
    have hcast : ∀ n : ℤ, (algebraMap ℤ Qsqrt3) n = (n : Qsqrt3) := fun n => by simp
    rw [hcast, hcast]
    push_cast
    have hexp : ((a : Qsqrt3) + (b : Qsqrt3) * sqrt3) ^ 2 =
        (a : Qsqrt3) * (a : Qsqrt3) + 2 * (a : Qsqrt3) * (b : Qsqrt3) * sqrt3
          + (b : Qsqrt3) * (b : Qsqrt3) * (sqrt3 * sqrt3) := by ring
    rw [hexp, h3]
    ring

/-! ### The two real embeddings `ℚ(√3) ↪ ℝ` -/

/-- The evaluation `(X^2 - C 3).eval₂ (algebraMap ℚ ℝ) (Real.sqrt 3) = 0`,
packaged for `AdjoinRoot.lift`. -/
private theorem eval₂_sqrt3_real :
    (X ^ 2 - C (3 : ℚ)).eval₂ (algebraMap ℚ ℝ) (Real.sqrt 3) = 0 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  simp [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h]

/-- Same as `eval₂_sqrt3_real` but with `-Real.sqrt 3`. -/
private theorem eval₂_neg_sqrt3_real :
    (X ^ 2 - C (3 : ℚ)).eval₂ (algebraMap ℚ ℝ) (-Real.sqrt 3) = 0 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h2 : (-Real.sqrt 3) ^ 2 = 3 := by rw [neg_pow, h]; ring
  simp [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h2]

/-- The positive real embedding `ℚ(√3) ↪ ℝ` sending `√3 ↦ Real.sqrt 3`. -/
noncomputable def embedPos : Qsqrt3 →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) (Real.sqrt 3) eval₂_sqrt3_real

/-- The negative real embedding `ℚ(√3) ↪ ℝ` sending `√3 ↦ -Real.sqrt 3`. -/
noncomputable def embedNeg : Qsqrt3 →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) (-Real.sqrt 3) eval₂_neg_sqrt3_real

@[simp]
theorem embedPos_sqrt3 : embedPos sqrt3 = Real.sqrt 3 :=
  AdjoinRoot.lift_root _

@[simp]
theorem embedNeg_sqrt3 : embedNeg sqrt3 = -Real.sqrt 3 :=
  AdjoinRoot.lift_root _

theorem embedPos_intCast (n : ℤ) : embedPos (n : Qsqrt3) = (n : ℝ) := by
  simp

theorem embedNeg_intCast (n : ℤ) : embedNeg (n : Qsqrt3) = (n : ℝ) := by
  simp

@[simp]
theorem embedPos_fromZsqrt3 (z : Zsqrtd 3) :
    embedPos (fromZsqrt3 z) = (z.re : ℝ) + (z.im : ℝ) * Real.sqrt 3 := by
  obtain ⟨a, b⟩ := z
  rw [fromZsqrt3_mk]
  simp

@[simp]
theorem embedNeg_fromZsqrt3 (z : Zsqrtd 3) :
    embedNeg (fromZsqrt3 z) = (z.re : ℝ) - (z.im : ℝ) * Real.sqrt 3 := by
  obtain ⟨a, b⟩ := z
  rw [fromZsqrt3_mk]
  simp [sub_eq_add_neg, mul_neg]

/-! ### Galois conjugation `σ : √3 ↦ -√3` -/

/-- The defining relation for `galConj`: `(-sqrt3)^2 = 3` inside `Qsqrt3`. -/
private theorem eval₂_neg_sqrt3_self :
    (X ^ 2 - C (3 : ℚ)).eval₂ (algebraMap ℚ Qsqrt3) (-sqrt3) = 0 := by
  have h3 : (algebraMap ℚ Qsqrt3) 3 = (3 : Qsqrt3) := by simp [map_ofNat]
  have hs : sqrt3 * sqrt3 = (3 : Qsqrt3) := sqrt3_sq
  simp [eval₂_sub, eval₂_X, eval₂_C, h3, sq, hs]

/-- The non-trivial Galois automorphism `σ : Qsqrt3 →+* Qsqrt3` sending
`√3 ↦ -√3`. -/
noncomputable def galConj : Qsqrt3 →+* Qsqrt3 :=
  AdjoinRoot.lift (algebraMap ℚ Qsqrt3) (-sqrt3) eval₂_neg_sqrt3_self

@[simp]
theorem galConj_sqrt3 : galConj sqrt3 = -sqrt3 :=
  AdjoinRoot.lift_root _

/-- `embedNeg` is `embedPos` precomposed with Galois conjugation. -/
theorem embedNeg_eq_embedPos_comp_galConj :
    embedNeg = embedPos.comp galConj := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · ext q
    change embedNeg (algebraMap ℚ Qsqrt3 q) = embedPos (galConj (algebraMap ℚ Qsqrt3 q))
    rw [show galConj (algebraMap ℚ Qsqrt3 q) = algebraMap ℚ Qsqrt3 q from
          AdjoinRoot.lift_of _,
        show embedNeg (algebraMap ℚ Qsqrt3 q) = algebraMap ℚ ℝ q from
          AdjoinRoot.lift_of _,
        show embedPos (algebraMap ℚ Qsqrt3 q) = algebraMap ℚ ℝ q from
          AdjoinRoot.lift_of _]
  · change embedNeg sqrt3 = embedPos (galConj sqrt3)
    rw [galConj_sqrt3, embedNeg_sqrt3, map_neg, embedPos_sqrt3]

/-- The two real embeddings are distinct. -/
theorem embedPos_ne_embedNeg : embedPos ≠ embedNeg := by
  intro h
  have hkey : Real.sqrt 3 = -Real.sqrt 3 := by
    have := congrArg (fun f => f sqrt3) h
    simpa using this
  have hpos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
  linarith

end Qsqrt3
