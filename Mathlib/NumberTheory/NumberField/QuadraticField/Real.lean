/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

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

open Polynomial NumberField

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

/-! ### Ring of integers `𝓞 ℚ(√3) ≃+* ℤ[√3]` -/

@[simp] theorem galConj_algebraMap (q : ℚ) :
    galConj ((algebraMap ℚ Qsqrt3) q) = (algebraMap ℚ Qsqrt3) q := by
  unfold galConj
  exact AdjoinRoot.lift_of _

/-- Decomposition of an arbitrary `x : Qsqrt3` along the basis `{1, √3}`. -/
theorem exists_rat_decomp (x : Qsqrt3) :
    ∃ p q : ℚ, x = (algebraMap ℚ Qsqrt3) p + (algebraMap ℚ Qsqrt3) q * sqrt3 := by
  obtain ⟨f⟩ := x
  refine ⟨(f %ₘ (X ^ 2 - C (3 : ℚ))).coeff 0, (f %ₘ (X ^ 2 - C (3 : ℚ))).coeff 1, ?_⟩
  have hmonic : Monic (X ^ 2 - C (3 : ℚ)) := by
    refine monic_X_pow_sub_C 3 (by decide)
  have hmod : AdjoinRoot.mk (X ^ 2 - C (3 : ℚ)) f
              = AdjoinRoot.mk _ (f %ₘ (X ^ 2 - C (3 : ℚ))) := by
    have hd := modByMonic_add_div f (X ^ 2 - C (3 : ℚ))
    conv_lhs => rw [← hd]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  set r := f %ₘ (X ^ 2 - C (3 : ℚ))
  have hdeg : r.degree < 2 := by
    have hlt := degree_modByMonic_lt f hmonic
    rw [degree_X_pow_sub_C (by decide : (0 : ℕ) < 2) (3 : ℚ)] at hlt
    exact_mod_cast hlt
  have hreq : r = C (r.coeff 0) + C (r.coeff 1) * X := by
    have hndeg : r.natDegree ≤ 1 := by
      by_cases h0 : r = 0
      · rw [h0]; simp
      · have := (natDegree_lt_iff_degree_lt h0 (n := 2)).mpr (by exact_mod_cast hdeg)
        omega
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · simp only [coeff_add, coeff_C, coeff_C_mul_X]
      rw [if_neg (by omega : ¬ (n + 1 + 1 = 0)), if_neg (by omega : ¬ (n + 1 + 1 = 1))]
      have : r.coeff (n + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  change AdjoinRoot.mk _ f = _
  rw [hmod, hreq, map_add, map_mul]
  have hC0 : AdjoinRoot.mk (X ^ 2 - C (3 : ℚ)) (C (r.coeff 0))
      = (algebraMap ℚ Qsqrt3) (r.coeff 0) := rfl
  have hC1 : AdjoinRoot.mk (X ^ 2 - C (3 : ℚ)) (C (r.coeff 1))
      = (algebraMap ℚ Qsqrt3) (r.coeff 1) := rfl
  have hX : AdjoinRoot.mk (X ^ 2 - C (3 : ℚ)) X = sqrt3 := rfl
  rw [hC0, hC1, hX]
  simp

theorem galConj_decomp (p q : ℚ) :
    galConj ((algebraMap ℚ Qsqrt3) p + (algebraMap ℚ Qsqrt3) q * sqrt3)
      = (algebraMap ℚ Qsqrt3) p - (algebraMap ℚ Qsqrt3) q * sqrt3 := by
  simp [galConj_sqrt3, sub_eq_add_neg, mul_neg]

theorem add_galConj (p q : ℚ) :
    ((algebraMap ℚ Qsqrt3) p + (algebraMap ℚ Qsqrt3) q * sqrt3)
      + galConj ((algebraMap ℚ Qsqrt3) p + (algebraMap ℚ Qsqrt3) q * sqrt3)
      = (algebraMap ℚ Qsqrt3) (2 * p) := by
  rw [galConj_decomp, map_mul]
  have h2 : (algebraMap ℚ Qsqrt3) 2 = (2 : Qsqrt3) := by simp [map_ofNat]
  rw [h2]; ring

theorem mul_galConj (p q : ℚ) :
    ((algebraMap ℚ Qsqrt3) p + (algebraMap ℚ Qsqrt3) q * sqrt3)
      * galConj ((algebraMap ℚ Qsqrt3) p + (algebraMap ℚ Qsqrt3) q * sqrt3)
      = (algebraMap ℚ Qsqrt3) (p ^ 2 - 3 * q ^ 2) := by
  rw [galConj_decomp]
  have h3 : sqrt3 * sqrt3 = (3 : Qsqrt3) := sqrt3_sq
  have hexp : ((algebraMap ℚ Qsqrt3) p + (algebraMap ℚ Qsqrt3) q * sqrt3) *
      ((algebraMap ℚ Qsqrt3) p - (algebraMap ℚ Qsqrt3) q * sqrt3)
      = (algebraMap ℚ Qsqrt3) p * (algebraMap ℚ Qsqrt3) p
        - (algebraMap ℚ Qsqrt3) q * (algebraMap ℚ Qsqrt3) q * (sqrt3 * sqrt3) := by ring
  rw [hexp, h3]
  have hmap3 : (algebraMap ℚ Qsqrt3) 3 = (3 : Qsqrt3) := by simp [map_ofNat]
  rw [map_sub, map_mul, map_pow, map_pow, hmap3]
  ring

theorem rat_isIntegral_of_isIntegral_in_Qsqrt3 {q : ℚ}
    (hq : IsIntegral ℤ ((algebraMap ℚ Qsqrt3) q)) : ∃ n : ℤ, (n : ℚ) = q := by
  have hinj : Function.Injective (algebraMap ℚ Qsqrt3) :=
    FaithfulSMul.algebraMap_injective ℚ Qsqrt3
  have hQ : IsIntegral ℤ q := (isIntegral_algebraMap_iff hinj).mp hq
  letI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨n, hn⟩ := (isIntegrallyClosed_iff (R := ℤ) (K := ℚ)).mp ‹_› hQ
  exact ⟨n, by simpa using hn⟩

private lemma sq_mod_four (a : ℤ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have hsq : a ^ 2 = a * a := sq a
  have ekey : a * a % 4 = (a % 4) * (a % 4) % 4 := by
    conv_lhs => rw [Int.mul_emod]
  have h4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rw [hsq, ekey]
  rcases h4 with h | h | h | h <;> rw [h] <;> decide

theorem rat_pq_integral {p q : ℚ} (htr : ∃ a : ℤ, (a : ℚ) = 2 * p)
    (hnm : ∃ d : ℤ, (d : ℚ) = p ^ 2 - 3 * q ^ 2) :
    (∃ a : ℤ, (a : ℚ) = p) ∧ (∃ b : ℤ, (b : ℚ) = q) := by
  obtain ⟨a, ha⟩ := htr
  obtain ⟨D, hD⟩ := hnm
  have hp : (a : ℚ) = 2 * p := ha
  have h12q2 : (12 : ℚ) * q ^ 2 = (a : ℚ) ^ 2 - 4 * D := by
    have hp2 : (a : ℚ) ^ 2 = 4 * p ^ 2 := by rw [hp]; ring
    nlinarith [hD, hp2]
  have hqden_eq : (q : ℚ) = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hqden_ne : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hMint : (12 : ℤ) * q.num ^ 2 = (a ^ 2 - 4 * D) * (q.den : ℤ) ^ 2 := by
    have hq2 : (q : ℚ) ^ 2 * (q.den : ℚ) ^ 2 = (q.num : ℚ) ^ 2 := by
      have hnd : (q.num : ℚ) = q * (q.den : ℚ) := by
        have h := Rat.num_div_den q
        field_simp at h
        linarith
      have h2 : (q.num : ℚ) ^ 2 = (q * (q.den : ℚ)) ^ 2 := by rw [hnd]
      rw [h2]; ring
    have hQ : (12 : ℚ) * (q.num : ℚ) ^ 2 = ((a : ℚ) ^ 2 - 4 * D) * (q.den : ℚ) ^ 2 := by
      have hmul : ((12 : ℚ) * q ^ 2) * (q.den : ℚ) ^ 2
          = ((a : ℚ) ^ 2 - 4 * D) * (q.den : ℚ) ^ 2 := by
        rw [h12q2]
      have : (12 : ℚ) * ((q : ℚ) ^ 2 * (q.den : ℚ) ^ 2)
          = ((a : ℚ) ^ 2 - 4 * D) * (q.den : ℚ) ^ 2 := by linarith [hmul]
      rw [hq2] at this
      linarith
    exact_mod_cast hQ
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    have h0 : IsCoprime ((q.den : ℤ)) q.num := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      have hred := q.reduced
      simpa [Int.gcd] using hred
    exact h0.pow
  have hq_den : (q.den : ℤ) ^ 2 ∣ 12 := by
    have hdvd : ((q.den : ℤ) ^ 2) ∣ (12 * q.num ^ 2) := ⟨a ^ 2 - 4 * D, by linarith [hMint]⟩
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hden_pos : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hsq_pos : 0 < (q.den : ℤ) ^ 2 := by positivity
  have hsq_le : (q.den : ℤ) ^ 2 ≤ 12 := Int.le_of_dvd (by decide) hq_den
  have hden_le : (q.den : ℤ) ≤ 12 := by nlinarith
  have hv12 : (q.den : ℤ) = 1 ∨ (q.den : ℤ) = 2 := by
    interval_cases ((q.den : ℤ))
    all_goals first
      | (left; rfl)
      | (right; rfl)
      | (exfalso; revert hq_den; decide)
  rcases hv12 with hv | hv
  · have hqden_eq1 : (q.den : ℚ) = 1 := by exact_mod_cast hv
    have hqZ_eq : (q.num : ℚ) = q := by
      conv_rhs => rw [hqden_eq]
      rw [hqden_eq1, div_one]
    have hp2eq : (a : ℚ) ^ 2 = 4 * D + 12 * q.num ^ 2 := by
      have h4p2 : (4 : ℚ) * p ^ 2 = (a : ℚ) ^ 2 := by rw [hp]; ring
      have : (4 : ℚ) * (D + 3 * q ^ 2) = 4 * D + 12 * q ^ 2 := by ring
      have h4D : (4 : ℚ) * p ^ 2 = 4 * D + 12 * q ^ 2 := by linarith [hD]
      have hq2num : (q : ℚ) ^ 2 = (q.num : ℚ) ^ 2 := by rw [hqZ_eq]
      rw [hq2num] at h4D
      linarith
    have hZ : a ^ 2 = 4 * D + 12 * q.num ^ 2 := by exact_mod_cast hp2eq
    have h4 : (4 : ℤ) ∣ a ^ 2 := ⟨D + 3 * q.num ^ 2, by linarith⟩
    have ha_even : (2 : ℤ) ∣ a := by
      have h2 : (2 : ℤ) ∣ a ^ 2 := dvd_trans (by decide : (2 : ℤ) ∣ 4) h4
      exact Int.prime_two.dvd_of_dvd_pow h2
    obtain ⟨k, hk⟩ := ha_even
    refine ⟨⟨k, ?_⟩, ⟨q.num, hqZ_eq⟩⟩
    have hk' : (a : ℚ) = 2 * (k : ℚ) := by exact_mod_cast hk
    have : (k : ℚ) * 2 = 2 * p := by linarith [hp]
    linarith
  · exfalso
    have hv2 : (q.den : ℤ) = 2 := hv
    have hu_coprime : Nat.Coprime q.num.natAbs q.den := q.reduced
    have hu_odd : ¬ (2 ∣ q.num) := by
      intro h2
      have h2nat : 2 ∣ q.num.natAbs := by
        rcases h2 with ⟨k, hk⟩
        refine ⟨k.natAbs, ?_⟩
        rw [hk]; exact (Int.natAbs_mul 2 k).trans rfl
      have h2den : 2 ∣ q.den := by
        have : (2 : ℕ) = (2 : ℤ).natAbs := rfl
        have h := Int.natAbs_dvd_natAbs.mpr (show (2 : ℤ) ∣ (q.den : ℤ) from ⟨1, by linarith [hv2]⟩)
        simpa using h
      have hgcd : Nat.gcd q.num.natAbs q.den ≥ 2 :=
        Nat.le_of_dvd (by omega) (Nat.dvd_gcd h2nat h2den)
      omega
    have hMint' : (12 : ℤ) * q.num ^ 2 = (a ^ 2 - 4 * D) * 4 := by
      have : ((q.den : ℤ)) ^ 2 = 4 := by rw [hv2]; ring
      rw [this] at hMint; exact hMint
    have hZ : 3 * q.num ^ 2 = a ^ 2 - 4 * D := by linarith
    have hmod : a ^ 2 % 4 = (3 * q.num ^ 2) % 4 := by omega
    have hnum_sq : q.num ^ 2 % 4 = 1 := by
      rcases sq_mod_four q.num with h | h
      · exfalso
        have h2 : (2 : ℤ) ∣ q.num := by
          have h4 : (4 : ℤ) ∣ q.num ^ 2 := Int.dvd_of_emod_eq_zero h
          have : (2 : ℤ) ∣ q.num ^ 2 := dvd_trans (by decide) h4
          exact Int.prime_two.dvd_of_dvd_pow this
        exact hu_odd h2
      · exact h
    have h3rhs : (3 * q.num ^ 2) % 4 = 3 := by
      have e : (3 * q.num ^ 2) % 4 = (3 * (q.num ^ 2 % 4)) % 4 := by
        rw [Int.mul_emod]; rfl
      rw [e, hnum_sq]; decide
    rcases sq_mod_four a with h | h <;> omega

theorem isIntegral_iff_mem_range (x : Qsqrt3) :
    IsIntegral ℤ x ↔ x ∈ Set.range fromZsqrt3 := by
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨p, q, hx_eq⟩ := exists_rat_decomp x
    have hsigma : IsIntegral ℤ (galConj x) := by
      obtain ⟨p, hpm, hpe⟩ := hx
      refine ⟨p, hpm, ?_⟩
      have h1 := congrArg galConj hpe
      rw [map_zero, Polynomial.hom_eval₂] at h1
      have hcomp : galConj.comp (algebraMap ℤ Qsqrt3) = algebraMap ℤ Qsqrt3 := by
        ext n
        change galConj ((n : ℤ) : Qsqrt3) = ((n : ℤ) : Qsqrt3)
        rw [show ((n : ℤ) : Qsqrt3) = (algebraMap ℚ Qsqrt3) ((n : ℤ) : ℚ) from by
              simp]
        exact galConj_algebraMap _
      rw [hcomp] at h1
      exact h1
    have hsum : IsIntegral ℤ (x + galConj x) := hx.add hsigma
    have hprod : IsIntegral ℤ (x * galConj x) := hx.mul hsigma
    rw [hx_eq, add_galConj] at hsum
    rw [hx_eq, mul_galConj] at hprod
    obtain ⟨a, ha⟩ := rat_isIntegral_of_isIntegral_in_Qsqrt3 hsum
    obtain ⟨D, hD⟩ := rat_isIntegral_of_isIntegral_in_Qsqrt3 hprod
    obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ :=
      rat_pq_integral (p := p) (q := q) ⟨a, ha⟩ ⟨D, hD⟩
    refine ⟨⟨m, n⟩, ?_⟩
    rw [fromZsqrt3_mk, hx_eq]
    have c1 : ((m : ℤ) : Qsqrt3) = (algebraMap ℚ Qsqrt3) p := by
      have e : ((m : ℤ) : Qsqrt3) = (algebraMap ℚ Qsqrt3) ((m : ℚ)) := by simp
      rw [e, hm]
    have c2 : ((n : ℤ) : Qsqrt3) = (algebraMap ℚ Qsqrt3) q := by
      have e : ((n : ℤ) : Qsqrt3) = (algebraMap ℚ Qsqrt3) ((n : ℚ)) := by simp
      rw [e, hn]
    rw [c1, c2]
  · rintro ⟨z, rfl⟩; exact isIntegral_fromZsqrt3 z

/-- `Zsqrtd 3` is the integral closure of `ℤ` in `Qsqrt3`. -/
instance isIntegralClosure_zsqrtd3 : IsIntegralClosure (Zsqrtd 3) ℤ Qsqrt3 where
  algebraMap_injective := fromZsqrt3_injective
  isIntegral_iff := by
    intro x
    rw [isIntegral_iff_mem_range, algebraMap_zsqrtd3]
    exact Iff.rfl

/-- The canonical identification of the ring of integers of `ℚ(√3)` with `ℤ[√3]`. -/
noncomputable def ringOfIntegersEquiv : 𝓞 Qsqrt3 ≃+* Zsqrtd 3 :=
  @RingOfIntegers.equiv Qsqrt3 _ (Zsqrtd 3) _ _ isIntegralClosure_zsqrtd3

/-! ### Bridge `(ℤ[√3])ˣ ≃* Pell.Solution₁ 3`

The Pell equation `x^2 - 3 y^2 = -1` has no integer solutions (mod-3 argument),
so every unit of `ℤ[√3]` has norm `+1`, identifying `(ℤ[√3])ˣ` with the set of
Pell-1 solutions, which Mathlib defines as `Pell.Solution₁ 3 = unitary (ℤ√3)`. -/

/-- The negative Pell equation `x^2 - 3 y^2 = -1` has no integer solutions.
Mod-3 argument: `x^2 mod 3 ∈ {0, 1}`, so `x^2 - 3 y^2 ≡ x^2 mod 3 ∈ {0, 1}`,
which never equals `-1 mod 3 = 2`. -/
theorem no_neg_pell_three : ¬ ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = -1 := by
  rintro ⟨x, y, hxy⟩
  have hmod : (x ^ 2 - 3 * y ^ 2) % 3 = (-1 : ℤ) % 3 := by rw [hxy]
  have hx2 : x ^ 2 % 3 = (x % 3) * (x % 3) % 3 := by
    rw [sq, Int.mul_emod]
  have hcase : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  have hx2_red : x ^ 2 % 3 = 0 ∨ x ^ 2 % 3 = 1 := by
    rcases hcase with h | h | h <;> rw [hx2, h] <;> decide
  omega

/-- For `d = 3`, every unit of `ℤ[√3]` has norm exactly `+1` (not `-1`). -/
theorem Zsqrt3.units_norm_eq_one (u : (Zsqrtd 3)ˣ) :
    (u : Zsqrtd 3).norm = 1 := by
  set z : Zsqrtd 3 := (u : Zsqrtd 3) with hz_def
  have hUnit : IsUnit z := u.isUnit
  have habs : z.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hUnit
  -- `z.norm = 1 ∨ z.norm = -1`; rule out `-1` via `no_neg_pell_three`.
  have hcases : z.norm = 1 ∨ z.norm = -1 := by
    rcases Int.natAbs_eq z.norm with h | h
    · left; omega
    · right; omega
  rcases hcases with h | h
  · exact h
  · exfalso
    apply no_neg_pell_three
    refine ⟨z.re, z.im, ?_⟩
    have := Zsqrtd.norm_def z
    -- `z.norm = z.re*z.re - 3*z.im*z.im` and `z.norm = -1` ⇒ `re^2 - 3 im^2 = -1`.
    have h2 : z.re * z.re - 3 * z.im * z.im = -1 := by rw [← this]; exact h
    nlinarith [h2]

/-- The bridge isomorphism: units of `ℤ[√3]` ≃* Pell solutions to `x² - 3 y² = 1`.
The forward map takes a unit to its underlying element viewed as a Pell solution
(possible because units have norm `+1` for `d = 3`); the inverse is
`Unitary.toUnits`. -/
noncomputable def Zsqrt3.unitsEquivSolution₁ :
    (Zsqrtd 3)ˣ ≃* Pell.Solution₁ 3 where
  toFun u :=
    ⟨(u : Zsqrtd 3),
      (Zsqrtd.norm_eq_one_iff_mem_unitary).mp (Zsqrt3.units_norm_eq_one u)⟩
  invFun s := Unitary.toUnits s
  left_inv u := by
    apply Units.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl
  map_mul' u v := by
    apply Subtype.ext
    rfl

@[simp]
theorem Zsqrt3.unitsEquivSolution₁_coe (u : (Zsqrtd 3)ˣ) :
    ((Zsqrt3.unitsEquivSolution₁ u : Pell.Solution₁ 3) : Zsqrtd 3) = (u : Zsqrtd 3) :=
  rfl

@[simp]
theorem Zsqrt3.unitsEquivSolution₁_symm_coe (s : Pell.Solution₁ 3) :
    ((Zsqrt3.unitsEquivSolution₁.symm s : (Zsqrtd 3)ˣ) : Zsqrtd 3) = (s : Zsqrtd 3) :=
  rfl

/-! ### The fundamental unit `2 + √3` of `𝓞 ℚ(√3)`

The fundamental Pell solution `(2, 1)` for `d = 3` transports through the chain

  `Pell.Solution₁ 3 ≃* (Zsqrtd 3)ˣ ≃* (𝓞 Qsqrt3)ˣ`

to give the fundamental unit `2 + √3 ∈ (𝓞 Qsqrt3)ˣ`. The unit-group bridge
`Units.mapEquiv (ringOfIntegersEquiv.toMulEquiv)` lifts the ring isomorphism
`𝓞 Qsqrt3 ≃+* Zsqrtd 3` to a multiplicative equivalence of unit groups. -/

/-- The unit-group isomorphism `(𝓞 Qsqrt3)ˣ ≃* (Zsqrtd 3)ˣ` induced by
`ringOfIntegersEquiv`. -/
noncomputable def unitsRingOfIntegersEquiv :
    (𝓞 Qsqrt3)ˣ ≃* (Zsqrtd 3)ˣ :=
  Units.mapEquiv ringOfIntegersEquiv.toMulEquiv

/-- The fundamental unit of `𝓞 Qsqrt3`: the image of the Pell solution `(2, 1)`
under the chain `Pell.Solution₁ 3 ≃* (Zsqrtd 3)ˣ ≃* (𝓞 Qsqrt3)ˣ`. As an element
of `Qsqrt3`, it equals `2 + √3`. -/
noncomputable def fundamentalUnit : (𝓞 Qsqrt3)ˣ :=
  unitsRingOfIntegersEquiv.symm (Zsqrt3.unitsEquivSolution₁.symm pellSolutionThree)

/-- The image of `fundamentalUnit` in `Zsqrtd 3` is the Pell solution `(2, 1)`. -/
theorem ringOfIntegersEquiv_fundamentalUnit :
    ringOfIntegersEquiv (fundamentalUnit : 𝓞 Qsqrt3) = (⟨2, 1⟩ : Zsqrtd 3) := by
  show ringOfIntegersEquiv
      ((unitsRingOfIntegersEquiv.symm
          (Zsqrt3.unitsEquivSolution₁.symm pellSolutionThree) : (𝓞 Qsqrt3)ˣ) :
            𝓞 Qsqrt3) = _
  have h1 : (unitsRingOfIntegersEquiv.symm
      (Zsqrt3.unitsEquivSolution₁.symm pellSolutionThree) : (𝓞 Qsqrt3)ˣ).val
        = ringOfIntegersEquiv.symm
            ((Zsqrt3.unitsEquivSolution₁.symm pellSolutionThree : (Zsqrtd 3)ˣ) :
              Zsqrtd 3) := by
    rfl
  rw [h1]
  rw [show ((Zsqrt3.unitsEquivSolution₁.symm pellSolutionThree : (Zsqrtd 3)ˣ) :
        Zsqrtd 3) = (pellSolutionThree : Zsqrtd 3) from
        Zsqrt3.unitsEquivSolution₁_symm_coe _]
  rw [RingEquiv.apply_symm_apply]
  rfl

/-! The round-trip identity `fromZsqrt3 (ringOfIntegersEquiv u) = (u : Qsqrt3)` follows
from `IsIntegralClosure.algebraMap_equiv`, which requires both
`IsScalarTower ℤ (𝓞 Qsqrt3) Qsqrt3` and `IsScalarTower ℤ (Zsqrtd 3) Qsqrt3`. Both
are now available globally; the former is the upstream-Mathlib instance added in
`Mathlib/NumberTheory/NumberField/Basic.lean`. -/

/-- The image in `Qsqrt3` of the `ringOfIntegersEquiv`-preimage of a `Zsqrtd 3` element
agrees with `fromZsqrt3`. This is the bridge identity unlocking the regulator computation.
The proof applies `Zsqrtd.hom_ext` after reducing to agreement on `Zsqrtd.sqrtd`, then uses
the universal property of integral closure. -/
theorem algebraMap_ringOfIntegersEquiv_symm (z : Zsqrtd 3) :
    algebraMap (𝓞 Qsqrt3) Qsqrt3 (ringOfIntegersEquiv.symm z) = fromZsqrt3 z := by
  -- Strategy: define a ring hom `g : Zsqrtd 3 →+* Qsqrt3` as the LHS-as-a-function-of-z and
  -- show `g = fromZsqrt3` via `Zsqrtd.hom_ext`, checking agreement on `Zsqrtd.sqrtd`.
  let g : Zsqrtd 3 →+* Qsqrt3 :=
    (algebraMap (𝓞 Qsqrt3) Qsqrt3).comp
      (ringOfIntegersEquiv.symm : Zsqrtd 3 →+* 𝓞 Qsqrt3)
  suffices hg : g = fromZsqrt3 by
    exact congrArg (fun f : Zsqrtd 3 →+* Qsqrt3 => f z) hg
  refine Zsqrtd.hom_ext _ _ ?_
  -- RHS at `sqrtd`: `fromZsqrt3 sqrtd = sqrt3`.
  rw [fromZsqrt3_sqrtd]
  -- LHS at `sqrtd`: take `u = ⟨sqrt3, hint⟩ : 𝓞 Qsqrt3`. Then `ringOfIntegersEquiv u = sqrtd`,
  -- so `ringOfIntegersEquiv.symm sqrtd = u`, and `algebraMap _ _ u = sqrt3`.
  have hint : IsIntegral ℤ (sqrt3 : Qsqrt3) := by
    have := isIntegral_fromZsqrt3 (Zsqrtd.sqrtd : Zsqrtd 3)
    rwa [fromZsqrt3_sqrtd] at this
  let u : 𝓞 Qsqrt3 := ⟨sqrt3, hint⟩
  have hu_val : algebraMap (𝓞 Qsqrt3) Qsqrt3 u = sqrt3 := rfl
  -- Show `ringOfIntegersEquiv u = Zsqrtd.sqrtd`.
  have hequiv : ringOfIntegersEquiv u = Zsqrtd.sqrtd := by
    -- Use injectivity of `fromZsqrt3` after applying to both sides.
    apply fromZsqrt3_injective
    rw [fromZsqrt3_sqrtd]
    rw [← algebraMap_zsqrtd3]
    -- Goal: `algebraMap (Zsqrtd 3) Qsqrt3 (ringOfIntegersEquiv u) = sqrt3`.
    -- Make instances available locally so synth in `algebraMap_equiv` succeeds.
    have hkey : ∀ v : 𝓞 Qsqrt3,
        algebraMap (Zsqrtd 3) Qsqrt3 (ringOfIntegersEquiv v) =
          algebraMap (𝓞 Qsqrt3) Qsqrt3 v := fun v => by
      letI iIC1 : IsIntegralClosure (𝓞 Qsqrt3) ℤ Qsqrt3 :=
        NumberField.RingOfIntegers.instIsIntegralClosureInt
      letI iST1 : IsScalarTower ℤ (𝓞 Qsqrt3) Qsqrt3 :=
        NumberField.RingOfIntegers.instIsScalarTowerInt Qsqrt3
      letI iST2 : IsScalarTower ℤ (Zsqrtd 3) Qsqrt3 := by infer_instance
      exact @IsIntegralClosure.algebraMap_equiv ℤ (𝓞 Qsqrt3) Qsqrt3
        _ _ _ _ _ iIC1 (Zsqrtd 3) _ _ isIntegralClosure_zsqrtd3 _ _ iST1 iST2 v
    rw [hkey]
    exact hu_val
  -- Now use `hequiv` to compute the LHS.
  show algebraMap (𝓞 Qsqrt3) Qsqrt3 (ringOfIntegersEquiv.symm Zsqrtd.sqrtd) = sqrt3
  rw [← hequiv, ringOfIntegersEquiv.symm_apply_apply]
  exact hu_val

/-- `Zsqrt3.unitsEquivSolution₁.symm` sends `-s` to `-(image of s)`, since both
sides agree on the underlying `Zsqrtd 3` element. -/
theorem Zsqrt3.unitsEquivSolution₁_symm_neg (s : Pell.Solution₁ 3) :
    Zsqrt3.unitsEquivSolution₁.symm (-s) = - Zsqrt3.unitsEquivSolution₁.symm s := by
  apply Units.ext
  show ((-s : Pell.Solution₁ 3) : Zsqrtd 3) = ((- Zsqrt3.unitsEquivSolution₁.symm s :
    (Zsqrtd 3)ˣ) : Zsqrtd 3)
  show (- (s : Zsqrtd 3) : Zsqrtd 3) = _
  rfl

/-- `unitsRingOfIntegersEquiv.symm` sends `-v` to `-(image of v)`, since
`ringOfIntegersEquiv.symm` is a `RingEquiv` and hence preserves negation, and
the underlying values of `-v` and `-(image of v)` are then equal. -/
theorem unitsRingOfIntegersEquiv_symm_neg (v : (Zsqrtd 3)ˣ) :
    unitsRingOfIntegersEquiv.symm (-v) = - unitsRingOfIntegersEquiv.symm v := by
  apply Units.ext
  show ringOfIntegersEquiv.symm ((-v : (Zsqrtd 3)ˣ) : Zsqrtd 3)
      = - ringOfIntegersEquiv.symm ((v : (Zsqrtd 3)ˣ) : Zsqrtd 3)
  rw [Units.val_neg]
  exact map_neg _ _

/-- Every unit of `𝓞 Qsqrt3` is, up to sign, a power of `fundamentalUnit`. This
is the unit-group analogue of `Pell.IsFundamental.eq_zpow_or_neg_zpow`, and
is equivalent to the statement that `fundamentalUnit` generates the free part
of `(𝓞 Qsqrt3)ˣ` modulo torsion. -/
theorem fundamentalUnit_eq_zpow_or_neg_zpow (u : (𝓞 Qsqrt3)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = - fundamentalUnit ^ n := by
  set s : Pell.Solution₁ 3 :=
    Zsqrt3.unitsEquivSolution₁ (unitsRingOfIntegersEquiv u) with hs_def
  obtain ⟨n, hn⟩ := pellSolutionThree_isFundamental.eq_zpow_or_neg_zpow s
  refine ⟨n, ?_⟩
  have hu : u = unitsRingOfIntegersEquiv.symm
      (Zsqrt3.unitsEquivSolution₁.symm s) := by
    rw [hs_def, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  rw [hu]
  rcases hn with hn | hn
  · left
    rw [hn, map_zpow, map_zpow]
    rfl
  · right
    rw [hn, Zsqrt3.unitsEquivSolution₁_symm_neg, map_zpow,
        unitsRingOfIntegersEquiv_symm_neg, map_zpow]
    rfl

/-! ### Phase C T7: regulator of `ℚ(√3)` — algebraic prerequisites

The headline target

```
regulator_eq_log_two_add_sqrt_three :
    NumberField.Units.regulator Qsqrt3 = Real.log (2 + Real.sqrt 3)
```

reduces, in the rank-1 totally-real case, to the standard `regOfFamily_eq_det` identity
on the 1×1 matrix `(log |embedPos fundamentalUnit|)`. The algebraic bridge identity
`algebraMap_fundamentalUnit` below converts the abstract Pell-derived
`fundamentalUnit : (𝓞 Qsqrt3)ˣ` into the concrete element `2 + √3 ∈ Qsqrt3`. The remaining
infrastructure (`IsTotallyReal Qsqrt3`, infinite-place enumeration, max-rank `funSystem`,
and the determinant reduction) is left as a follow-up; this commit lands the structural
prerequisite. -/

/-- `algebraMap (𝓞 Qsqrt3) Qsqrt3` applied to `fundamentalUnit` gives `2 + √3`. -/
theorem algebraMap_fundamentalUnit :
    algebraMap (𝓞 Qsqrt3) Qsqrt3 (fundamentalUnit : 𝓞 Qsqrt3) = 2 + sqrt3 := by
  have h1 : (fundamentalUnit : 𝓞 Qsqrt3) =
      ringOfIntegersEquiv.symm (⟨2, 1⟩ : Zsqrtd 3) := by
    rw [← ringOfIntegersEquiv_fundamentalUnit, RingEquiv.symm_apply_apply]
  rw [h1, algebraMap_ringOfIntegersEquiv_symm, fromZsqrt3_mk]
  push_cast
  ring

/-- The positive real embedding sends `fundamentalUnit` to `2 + √3 > 1`. -/
theorem embedPos_fundamentalUnit :
    embedPos (algebraMap (𝓞 Qsqrt3) Qsqrt3 (fundamentalUnit : 𝓞 Qsqrt3)) =
      2 + Real.sqrt 3 := by
  rw [algebraMap_fundamentalUnit]
  simp [embedPos_sqrt3, map_add, map_ofNat]

/-! ### Phase C T7 (v4): IsTotallyReal, infinite-place enumeration, regulator closed form -/

open NumberField NumberField.InfinitePlace NumberField.Units

/-- Every ring homomorphism `Qsqrt3 →+* ℂ` factors through `ℝ`: its image lies in `ℝ ⊆ ℂ`.

Strategy: `Qsqrt3 = AdjoinRoot (X² - 3)`, so any `φ : Qsqrt3 →+* ℂ` is determined by
its values on `algebraMap ℚ Qsqrt3` and on `sqrt3`. The relation `(φ sqrt3)² = 3 : ℂ`
forces `φ sqrt3 ∈ {↑(Real.sqrt 3), -↑(Real.sqrt 3)}`, both real. Therefore `conj ∘ φ`
and `φ` agree on the generators and hence everywhere. -/
instance instIsTotallyReal : NumberField.IsTotallyReal Qsqrt3 := by
  refine (NumberField.isTotallyReal_iff Qsqrt3).mpr ?_
  intro w
  obtain ⟨φ, rfl⟩ : ∃ φ : Qsqrt3 →+* ℂ, InfinitePlace.mk φ = w :=
    ⟨w.embedding, InfinitePlace.mk_embedding w⟩
  apply InfinitePlace.isReal_mk_iff.mpr
  rw [ComplexEmbedding.isReal_iff]
  have hsq : (φ sqrt3) ^ 2 = 3 := by
    have h := congrArg φ sqrt3_sq
    rw [map_mul] at h
    have h3 : φ (3 : Qsqrt3) = 3 := by
      show φ (3 : Qsqrt3) = (3 : ℂ)
      rw [show ((3 : Qsqrt3)) = ((3 : ℕ) : Qsqrt3) from by push_cast; ring]
      rw [map_natCast]
      norm_num
    rw [h3] at h
    rw [sq]; exact h
  have hReal_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    exact_mod_cast h
  have hroots : φ sqrt3 = (Real.sqrt 3 : ℂ) ∨ φ sqrt3 = -(Real.sqrt 3 : ℂ) := by
    have hdiff : (φ sqrt3 - (Real.sqrt 3 : ℂ)) * (φ sqrt3 + (Real.sqrt 3 : ℂ)) = 0 := by
      have : (φ sqrt3) ^ 2 - (Real.sqrt 3 : ℂ) ^ 2 = 0 := by rw [hsq, hReal_sq]; ring
      linear_combination this
    rcases mul_eq_zero.mp hdiff with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hconj_sqrt3 : (starRingEnd ℂ) (φ sqrt3) = φ sqrt3 := by
    rcases hroots with h | h
    · rw [h]; simp
    · rw [h]; simp
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine RingHom.ext fun q => ?_
    -- Both sides equal `((q : ℝ) : ℂ)` since any `RingHom Qsqrt3 →+* ℂ` is determined
    -- on the image of ℚ by the rationals' universal property.
    have hreal : φ ((AdjoinRoot.of (X ^ 2 - C (3:ℚ))) q) = ((q : ℚ) : ℂ) := by
      have h1 : (AdjoinRoot.of (X ^ 2 - C (3:ℚ))) q = ((q : ℚ) : Qsqrt3) := by
        change (algebraMap ℚ Qsqrt3) q = _
        simp
      rw [h1, map_ratCast]
    change (starRingEnd ℂ) (φ ((AdjoinRoot.of (X ^ 2 - C (3:ℚ))) q)) =
            φ ((AdjoinRoot.of (X ^ 2 - C (3:ℚ))) q)
    rw [hreal]; simp
  · exact hconj_sqrt3

/-- The number of real places of `ℚ(√3)` is `2`. -/
theorem nrRealPlaces_eq_two : nrRealPlaces Qsqrt3 = 2 := by
  rw [← NumberField.IsTotallyReal.finrank Qsqrt3, finrank_eq_two]

/-- The total number of infinite places of `ℚ(√3)` is `2`. -/
theorem card_infinitePlace_eq_two :
    Fintype.card (InfinitePlace Qsqrt3) = 2 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      nrRealPlaces_eq_two, NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]

/-- The unit rank of `ℚ(√3)` is `1`. -/
theorem units_rank_eq_one : rank Qsqrt3 = 1 := by
  rw [NumberField.Units.rank, card_infinitePlace_eq_two]

/-! ### The single-unit family and its regulator -/

/-- The single-element family of units sending `0 ↦ fundamentalUnit`, viewed as
a function on `Fin (rank Qsqrt3) = Fin 1`. -/
noncomputable def funSystem3 : Fin (rank Qsqrt3) → (𝓞 Qsqrt3)ˣ :=
  fun _ => fundamentalUnit

/-- The closure of `range funSystem3` together with `torsion Qsqrt3` is the full unit
group. -/
theorem closure_funSystem3_sup_torsion_eq_top :
    Subgroup.closure (Set.range funSystem3) ⊔ torsion Qsqrt3 = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro u
  obtain ⟨n, hn⟩ := fundamentalUnit_eq_zpow_or_neg_zpow u
  have hfu_mem :
      fundamentalUnit ∈ Subgroup.closure (Set.range funSystem3) := by
    -- We must provide a member of `Fin (rank Qsqrt3)`; supply one via `units_rank_eq_one`.
    refine Subgroup.subset_closure ?_
    refine ⟨(Fin.cast units_rank_eq_one.symm) ⟨0, by decide⟩, rfl⟩
  rcases hn with hn | hn
  · exact Subgroup.mem_sup_left (by rw [hn]; exact Subgroup.zpow_mem _ hfu_mem _)
  · have : u = ((-1 : (𝓞 Qsqrt3)ˣ)) * (fundamentalUnit ^ n) := by rw [hn]; simp
    rw [this, sup_comm]
    exact Subgroup.mul_mem_sup neg_one_mem_torsion
      (Subgroup.zpow_mem _ hfu_mem _)

/-- `regOfFamily funSystem3` equals the regulator. -/
theorem regOfFamily_funSystem3_eq_regulator :
    regOfFamily funSystem3 = regulator Qsqrt3 := by
  have h := regOfFamily_div_regulator funSystem3
  rw [closure_funSystem3_sup_torsion_eq_top, Subgroup.index_top, Nat.cast_one] at h
  exact (div_eq_one_iff_eq (regulator_ne_zero Qsqrt3)).mp h

/-! ### 1×1 determinant: the regulator equals `log (2 + √3)` -/

/-- The infinite place of `Qsqrt3` defined by `embedPos`. -/
noncomputable def wPos : InfinitePlace Qsqrt3 :=
  InfinitePlace.mk (Complex.ofRealHom.comp embedPos)

/-- The infinite place of `Qsqrt3` defined by `embedNeg`. -/
noncomputable def wNeg : InfinitePlace Qsqrt3 :=
  InfinitePlace.mk (Complex.ofRealHom.comp embedNeg)

/-- `(Complex.ofRealHom.comp f)` is a real complex embedding for any `f : K →+* ℝ`. -/
private theorem isReal_ofRealHom_comp (f : Qsqrt3 →+* ℝ) :
    ComplexEmbedding.IsReal (Complex.ofRealHom.comp f) := by
  rw [ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun x => ?_
  change (starRingEnd ℂ) (((f x : ℝ) : ℂ)) = ((f x : ℝ) : ℂ)
  simp

/-- `wPos ≠ wNeg`. -/
theorem wPos_ne_wNeg : wPos ≠ wNeg := by
  intro habs
  have hreal_pos : ComplexEmbedding.IsReal (Complex.ofRealHom.comp embedPos) :=
    isReal_ofRealHom_comp embedPos
  have hdisj := InfinitePlace.mk_eq_iff.mp habs
  have hpos_eq : Complex.ofRealHom.comp embedPos = Complex.ofRealHom.comp embedNeg := by
    rcases hdisj with h | h
    · exact h
    · rw [ComplexEmbedding.isReal_iff.mp hreal_pos] at h
      exact h
  -- Evaluate at `sqrt3` to get a numerical contradiction.
  have hsqrt3 : (embedPos sqrt3 : ℂ) = (embedNeg sqrt3 : ℂ) := by
    have := RingHom.ext_iff.mp hpos_eq sqrt3
    change ((embedPos sqrt3 : ℝ) : ℂ) = ((embedNeg sqrt3 : ℝ) : ℂ) at this
    exact_mod_cast this
  rw [embedPos_sqrt3, embedNeg_sqrt3] at hsqrt3
  have h2 : (Real.sqrt 3 : ℝ) = -Real.sqrt 3 := by exact_mod_cast hsqrt3
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- `wPos` is the unique infinite place ≠ `wNeg`. -/
theorem unique_ne_wNeg :
    ∀ w : {w : InfinitePlace Qsqrt3 // w ≠ wNeg}, w = ⟨wPos, wPos_ne_wNeg⟩ := by
  rintro ⟨w, hw⟩
  refine Subtype.ext ?_
  classical
  have hcard2 : (Finset.univ : Finset (InfinitePlace Qsqrt3)).card = 2 := by
    rw [Finset.card_univ]; exact card_infinitePlace_eq_two
  have hpair_card : ({wNeg, wPos} : Finset (InfinitePlace Qsqrt3)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using wPos_ne_wNeg.symm),
        Finset.card_singleton]
  have hsub : ({wNeg, wPos} : Finset _) ⊆ Finset.univ := Finset.subset_univ _
  have hmem : (Finset.univ : Finset (InfinitePlace Qsqrt3)) = {wNeg, wPos} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hpair_card, hcard2])).symm
  have hwmem : w ∈ ({wNeg, wPos} : Finset _) := by rw [← hmem]; exact Finset.mem_univ _
  rcases Finset.mem_insert.mp hwmem with h | h
  · exact absurd h hw
  · exact Finset.mem_singleton.mp h

/-- The equivalence `{w // w ≠ wNeg} ≃ Fin 1`. -/
noncomputable def equivSurvivingPlace : {w : InfinitePlace Qsqrt3 // w ≠ wNeg} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨wPos, wPos_ne_wNeg⟩
  left_inv x := (unique_ne_wNeg x).symm
  right_inv := by decide

/-- `wPos` applied to `fundamentalUnit` equals `2 + √3`. -/
theorem wPos_fundamentalUnit :
    wPos (fundamentalUnit : Qsqrt3) = 2 + Real.sqrt 3 := by
  change ‖(Complex.ofRealHom.comp embedPos) ((fundamentalUnit : 𝓞 Qsqrt3) : Qsqrt3)‖ =
    2 + Real.sqrt 3
  have hval : (Complex.ofRealHom.comp embedPos) ((fundamentalUnit : 𝓞 Qsqrt3) : Qsqrt3) =
      ((2 + Real.sqrt 3 : ℝ) : ℂ) := by
    change ((embedPos ((fundamentalUnit : 𝓞 Qsqrt3) : Qsqrt3) : ℝ) : ℂ) = _
    rw [embedPos_fundamentalUnit]
  rw [hval, Complex.norm_real]
  have hpos : (0 : ℝ) ≤ 2 + Real.sqrt 3 := by positivity
  exact abs_of_nonneg hpos

/-- The headline theorem for Phase C item (a): the regulator of `ℚ(√3)` is `log (2 + √3)`. -/
theorem regulator_eq_log_two_add_sqrt_three :
    regulator Qsqrt3 = Real.log (2 + Real.sqrt 3) := by
  classical
  -- Translate `Fin (rank Qsqrt3)` to `Fin 1` via `units_rank_eq_one`.
  have eFin : Fin 1 ≃ Fin (rank Qsqrt3) :=
    Equiv.cast (by rw [units_rank_eq_one])
  have e : {w : InfinitePlace Qsqrt3 // w ≠ wNeg} ≃ Fin (rank Qsqrt3) :=
    equivSurvivingPlace.trans eFin
  rw [← regOfFamily_funSystem3_eq_regulator, regOfFamily_eq_det funSystem3 wNeg e]
  letI hUnique : Unique {w : InfinitePlace Qsqrt3 // w ≠ wNeg} :=
    ⟨⟨⟨wPos, wPos_ne_wNeg⟩⟩, unique_ne_wNeg⟩
  rw [Matrix.det_unique]
  -- The single entry of the matrix; `default = ⟨wPos, _⟩` for our Unique instance.
  change |(mult ((default : {w : InfinitePlace Qsqrt3 // w ≠ wNeg}).val) : ℝ) *
      Real.log ((default : {w : InfinitePlace Qsqrt3 // w ≠ wNeg}).val
        ((funSystem3 (e default) : 𝓞 Qsqrt3) : Qsqrt3))| = Real.log (2 + Real.sqrt 3)
  have hmult : (mult wPos : ℝ) = 1 := by
    have := NumberField.IsTotallyReal.mult_eq (K := Qsqrt3) wPos
    exact_mod_cast this
  -- `default = ⟨wPos, wPos_ne_wNeg⟩` for hUnique.
  rw [show (default : {w : InfinitePlace Qsqrt3 // w ≠ wNeg}) = ⟨wPos, wPos_ne_wNeg⟩ from rfl]
  simp only [funSystem3]
  rw [hmult, one_mul, wPos_fundamentalUnit]
  have hpos1 : (1 : ℝ) < 2 + Real.sqrt 3 := by
    have h0 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    linarith
  exact abs_of_pos (Real.log_pos hpos1)

end Qsqrt3
