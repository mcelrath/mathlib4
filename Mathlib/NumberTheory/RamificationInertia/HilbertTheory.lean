/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!

# Decomposition and Inertia fields

In this file, we develop Hilbert Theory on the splitting of prime ideals in a Galois extension.

Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`K` fraction field of `A`, `L` fraction field of `B` and `B` the integral closure of `A` in `L`.

For `P` a prime ideal of `B`, the decomposition field `D` of `P` in `L/K` is the subfield of
elements of `L` fixed by the stabilizer of `P` in `Gal(L/K)`, and the inertia field `E` of `P`
in `L/K` is the subfield of elements of `L` fixed by the inertia group of `P` in `Gal(L/K)`.

-/

@[expose] public section

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]

open MulAction Pointwise Ideal

section basic

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield fixed by the
decomposition subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (stabilizer Gal(L/K) P) D L] :
    IsDecompositionField K L P D := { toIsGaloisGroup := h }

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed by the inertia
subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (inertia Gal(L/K) P) E L] :
    IsInertiaField K L P E := { toIsGaloisGroup := h }

variable [MulSemiringAction Gal(L/K) B]

instance [IsGalois K L] : IsDecompositionField K L P
    (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

instance [IsGalois K L] : IsInertiaField K L P
    (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [MulSemiringAction G B]

section of_isGaloisGroup

variable [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L] [SMulDistribClass G B L]

/--
If `G` is a Galois group for `L/K` and the stabilizer of `P` in `G` is a Galois group for
`L/D`, then `D` is a decomposition field for `P`.
-/
theorem IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D := by
  refine (isDecompositionField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      stabilizerEquiv_symm_apply_smul]

/--
If `G` is a Galois group for `L/K` and the inertia group of `P` in `G` is a Galois group for
`L/E`, then `E` is an inertia field for `P`.
-/
theorem IsInertiaField.of_isGaloisGroup [h : IsGaloisGroup (inertia G P) E L] :
    IsInertiaField K L P E := by
  refine (isInertiaField_iff K L P E).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      inertiaEquiv_symm_apply_smul]

end of_isGaloisGroup

variable (D' : Type*) [Field D'] [Algebra D' L] (E' : Type*) [Field E'] [Algebra E' L]

/-- Two decomposition fields are isomorphic. -/
noncomputable def IsDecompositionField.ringEquiv [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] :
    D ≃+* D' :=
  IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[simp]
theorem IsDecompositionField.algebraMap_ringEquiv_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D) :
    algebraMap D' L (IsDecompositionField.ringEquiv K L P D D' x) = algebraMap D L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
theorem IsDecompositionField.algebraMap_ringEquiv_symm_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D') :
    algebraMap D L ((IsDecompositionField.ringEquiv K L P D D').symm x) = algebraMap D' L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

/-- Two inertia fields are isomorphic. -/
noncomputable def IsInertiaField.ringEquiv [IsInertiaField K L P E] [IsInertiaField K L P E'] :
    E ≃+* E' :=
  IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[simp]
theorem IsInertiaField.algebraMap_ringEquiv_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E) :
    algebraMap E' L (IsInertiaField.ringEquiv K L P E E' x) = algebraMap E L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
theorem IsInertiaField.algebraMap_ringEquiv_symm_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E') :
    algebraMap E L ((IsInertiaField.ringEquiv K L P E E').symm x) = algebraMap E' L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

end basic

section rank

attribute [local instance] Ideal.Quotient.field

variable [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P

/--
The degree `[L : D]` of `L` over the decomposition field `D` equals the product of the
ramification index and the inertia degree of `p` in `B`.
-/
theorem IsDecompositionField.rank_left (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p hp]

/--
The degree `[D : K]` of the decomposition field `D` over `K` equals the number of prime ideals
of `B` lying over `p`.
-/
theorem IsDecompositionField.rank_right [IsGalois K L] [Algebra K D] [IsScalarTower K D L]
    (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P D hp,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

/--
The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p` in `B`.
-/
theorem IsInertiaField.rank_left (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L,
    card_inertia_eq_ramificationIdxIn p hp]

/--
The degree `[E : K]` of the inertia field `E` over `K` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`.
-/
theorem IsInertiaField.rank_right [IsGalois K L] [Algebra K E] [IsScalarTower K E L] (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P E hp, mul_assoc, mul_comm (p.inertiaDegIn B),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

/--
The degree `[E : D]` of the inertia field `E` over the decomposition field `D` equals the
inertia degree of `p` in `B`.
-/
theorem IsInertiaField.rank_decompositionField [IsGalois K L] [Algebra K D] [Algebra K E]
    [Algebra D E] [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] (hp : p ≠ ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact IsDedekindDomain.primesOver_ncard_ne_zero p B

end rank

section integralClosure_inertia

/-!
### Instances for `integralClosure A E` when `E` is an inertia (or decomposition) subfield

For an inertia or decomposition subfield `E` of `L/K` sitting between `K` and `L`, the integral
closure `B_E := integralClosure A E` of `A` in `E` is a Dedekind domain with fraction field `E`,
and the scalar towers `A → B_E → E` and `K → B_E ↪ L` are well-behaved. We register the
instances here under the per-theorem hypotheses `[Algebra K E] [IsScalarTower K E L]` shared by
`IsInertiaField.rank_right`, `IsDecompositionField.rank_right`, and downstream consumers.

These instances are stated at the level of `integralClosure A E`, not specifically for inertia
or decomposition fields, so they apply equally to any subfield `E ⊆ L` over `K`.
-/

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [Algebra A E] [IsScalarTower A K E] [IsScalarTower A E L]

omit [Algebra A L] [IsScalarTower A K L] [IsScalarTower A E L] in
include K L in
/-- The integral closure of `A` in an intermediate field `E` is a Dedekind domain.

Stated as a `theorem` (not an `instance`) because `K` cannot be inferred from the conclusion;
downstream consumers should pull it in with
`haveI := integralClosure.isDedekindDomain_intermediateField A K L E`. -/
theorem integralClosure.isDedekindDomain_intermediateField [IsDedekindDomain A]
    [Algebra.IsSeparable K E] :
    IsDedekindDomain (integralClosure A E) :=
  have _ : FiniteDimensional K E := FiniteDimensional.left K E L
  _root_.integralClosure.isDedekindDomain A K E

omit [Algebra A L] [IsScalarTower A K L] [IsScalarTower A E L] in
include K L in
/-- The integral closure of `A` in an intermediate field `E` has fraction field `E`. -/
theorem integralClosure.isFractionRing_intermediateField [IsDomain A] :
    IsFractionRing (integralClosure A E) E :=
  have _ : FiniteDimensional K E := FiniteDimensional.left K E L
  isFractionRing_of_finite_extension K E

/-- The scalar tower `A → integralClosure A E → E`. (Already an instance via
`IsScalarTower.subalgebra'` applied to the subalgebra `integralClosure A E ⊆ E`,
recorded here for documentation.) -/
example : IsScalarTower A (integralClosure A E) E := inferInstance

end integralClosure_inertia

section inertia_action_inertia_field

/-!
### Trivial action of the inertia group on the inertia field

Let `E` be the inertia field of `P` in `L/K`. By definition, the inertia group
`I := inertia Gal(L/K) P` fixes `E` pointwise (as a subfield of `L`). On the abstract field `E`
we record the resulting trivial `MulSemiringAction (inertia Gal(L/K) P) E`, defined as the
constant identity action. This lifts to `B_E := integralClosure A E` via the generic
integral-closure instance.
-/

variable [MulSemiringAction Gal(L/K) B]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [IsInertiaField K L P E]

/-- The inertia group `inertia Gal(L/K) P` acts trivially on the inertia field `E`. -/
instance IsInertiaField.inertiaMulSemiringAction :
    MulSemiringAction (inertia Gal(L/K) P) E :=
  MulSemiringAction.compHom E (1 : inertia Gal(L/K) P →* (E ≃+* E))

omit [Algebra K E] [Algebra E L] [IsScalarTower K E L] [IsInertiaField K L P E] in
@[simp]
lemma IsInertiaField.inertia_smul_eq (g : inertia Gal(L/K) P) (x : E) : g • x = x := rfl

instance IsInertiaField.smulCommClass_inertia_K :
    SMulCommClass (inertia Gal(L/K) P) K E :=
  ⟨fun _ _ _ ↦ by simp [IsInertiaField.inertia_smul_eq]⟩

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [Algebra A E] [IsScalarTower A K E] [IsScalarTower A E L]

instance IsInertiaField.smulCommClass_inertia_A :
    SMulCommClass (inertia Gal(L/K) P) A E :=
  ⟨fun _ _ _ ↦ by simp [IsInertiaField.inertia_smul_eq]⟩

/-- The inertia group acts (trivially) on `B_E := integralClosure A E` via the action on `E`. -/
example : MulSemiringAction (inertia Gal(L/K) P) (integralClosure A E) := inferInstance

end inertia_action_inertia_field
