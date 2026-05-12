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

/-!
#### Algebra structure and scalar towers `integralClosure A E → B`

Every element of `integralClosure A E` is, by definition, integral over `A` in `E`; its image
in `L` (via `algebraMap E L`) is then integral over `A` in `L`, hence lies in any `B` with
`[IsIntegralClosure B A L]`. This induces a canonical `A`-algebra map
`integralClosure A E →ₐ[A] B`, which we turn into an `Algebra (integralClosure A E) B` instance
together with the scalar towers `A → integralClosure A E → B` and
`integralClosure A E → E → L` / `integralClosure A E → B → L`.
-/

/-- The canonical `A`-algebra map `integralClosure A E →ₐ[A] B` arising from
`integralClosure A E ↪ E → L` and the fact that `B = integralClosure A L`. -/
noncomputable def integralClosure.intermediateFieldToAlgHom
    (B' : Type*) [CommRing B'] [Algebra A B'] [Algebra B' L] [IsScalarTower A B' L]
    [IsIntegralClosure B' A L] :
    integralClosure A E →ₐ[A] B' :=
  (IsIntegralClosure.equiv A (integralClosure A L) L B').toAlgHom.comp
    ((IsScalarTower.toAlgHom A E L).mapIntegralClosure)

@[simp]
lemma integralClosure.algebraMap_intermediateFieldToAlgHom_apply
    (B' : Type*) [CommRing B'] [Algebra A B'] [Algebra B' L] [IsScalarTower A B' L]
    [IsIntegralClosure B' A L] (x : integralClosure A E) :
    algebraMap B' L (integralClosure.intermediateFieldToAlgHom A L E B' x) =
      algebraMap E L (x : E) := by
  unfold integralClosure.intermediateFieldToAlgHom
  simp [Subalgebra.algebraMap_eq, IsScalarTower.coe_toAlgHom']

/-- The canonical `Algebra (integralClosure A E) B` structure when `B` is the integral closure of
`A` in `L`.

Stated as a `def` (not an `instance`) because Lean cannot synthesize the underlying `A`-algebra
map `integralClosure A E →ₐ[A] B` automatically. Downstream consumers should pull it in with
`haveI` or `letI`. -/
@[reducible] noncomputable def integralClosure.algebra_intermediateField
    (B' : Type*) [CommRing B'] [Algebra A B'] [Algebra B' L] [IsScalarTower A B' L]
    [IsIntegralClosure B' A L] :
    Algebra (integralClosure A E) B' :=
  (integralClosure.intermediateFieldToAlgHom A L E B').toRingHom.toAlgebra

/-- With `Algebra (integralClosure A E) B` from `integralClosure.algebra_intermediateField`,
`B` is a scalar tower over `A` through `integralClosure A E`. -/
theorem integralClosure.isScalarTower_intermediateField
    (B' : Type*) [CommRing B'] [Algebra A B'] [Algebra B' L] [IsScalarTower A B' L]
    [IsIntegralClosure B' A L] :
    letI := integralClosure.algebra_intermediateField A L E B'
    IsScalarTower A (integralClosure A E) B' := by
  letI := integralClosure.algebra_intermediateField A L E B'
  refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
  apply IsIntegralClosure.algebraMap_injective B' A L
  have hcoe : ∀ y : integralClosure A E,
      (algebraMap (integralClosure A E) B') y =
        integralClosure.intermediateFieldToAlgHom A L E B' y := fun _ ↦ rfl
  rw [hcoe, integralClosure.algebraMap_intermediateFieldToAlgHom_apply]
  rw [← IsScalarTower.algebraMap_apply A B' L,
    show ((algebraMap A (integralClosure A E)) a : E) = algebraMap A E a from rfl,
    ← IsScalarTower.algebraMap_apply A E L]

/-- The scalar tower `integralClosure A E → B → L` (i.e. the embedding `B_E ↪ B` is compatible
with the embeddings into `L`). -/
theorem integralClosure.isScalarTower_intermediateField_right
    (B' : Type*) [CommRing B'] [Algebra A B'] [Algebra B' L] [IsScalarTower A B' L]
    [IsIntegralClosure B' A L] :
    letI := integralClosure.algebra_intermediateField A L E B'
    IsScalarTower (integralClosure A E) B' L := by
  letI := integralClosure.algebra_intermediateField A L E B'
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  have hcoe : (algebraMap (integralClosure A E) B') x =
      integralClosure.intermediateFieldToAlgHom A L E B' x := rfl
  rw [hcoe, integralClosure.algebraMap_intermediateFieldToAlgHom_apply]
  exact (IsScalarTower.algebraMap_apply (integralClosure A E) E L x).symm

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

section stabilizer_action_inertia_field

/-!
### Action of the decomposition group on the inertia field

Let `E` be an inertia field of `P` in `L/K`. The inertia group `I := inertia Gal(L/K) P` is the
Galois group of `L/E`, and is normal inside the decomposition group
`G₀ := stabilizer Gal(L/K) P` (`(inertia _ P).subgroupOf (stabilizer _ P)` is normal, proven
generically in `Mathlib.RingTheory.Ideal.Pointwise`). For `g : G₀` and `x : E`, the element
`(g : Gal(L/K)) • algebraMap E L x ∈ L` is fixed by `I` (by normality of `I` in `G₀`), so
descends uniquely to an element of `E` via `Algebra.IsInvariant.isInvariant`. This defines a
`MulSemiringAction (stabilizer Gal(L/K) P) E`, which lifts to `integralClosure A E` via the
generic instance on integral closures.
-/

variable [MulSemiringAction Gal(L/K) B]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [hE : IsInertiaField K L P E]

omit [Algebra K E] [IsScalarTower K E L] in
lemma IsInertiaField.stabilizer_smul_invariant
    (g : stabilizer Gal(L/K) P) (x : E) :
    ∀ n : inertia Gal(L/K) P,
      (n : Gal(L/K)) • ((g : Gal(L/K)) • algebraMap E L x) =
        (g : Gal(L/K)) • algebraMap E L x := by
  intro n
  have hI_le : inertia Gal(L/K) P ≤ stabilizer Gal(L/K) P := inertia_le_stabilizer P
  have hN : ((inertia Gal(L/K) P).subgroupOf (stabilizer Gal(L/K) P)).Normal := inferInstance
  -- The conjugate g⁻¹ n g lies in the inertia subgroup, hence fixes algebraMap E L x.
  have hconj_mem :
      (g : Gal(L/K))⁻¹ * (n : Gal(L/K)) * (g : Gal(L/K)) ∈ inertia Gal(L/K) P := by
    have hn_sub : (⟨(n : Gal(L/K)), hI_le n.2⟩ : stabilizer Gal(L/K) P) ∈
        (inertia Gal(L/K) P).subgroupOf (stabilizer Gal(L/K) P) := n.2
    have hconj := hN.conj_mem'
      ⟨(n : Gal(L/K)), hI_le n.2⟩ hn_sub ⟨(g : Gal(L/K)), g.2⟩
    simpa [Subgroup.mem_subgroupOf] using hconj
  have hfix : ((g : Gal(L/K))⁻¹ * (n : Gal(L/K)) * (g : Gal(L/K))) • algebraMap E L x =
      algebraMap E L x := by
    have hc : SMulCommClass (inertia Gal(L/K) P) E L := hE.toIsGaloisGroup.commutes
    have h1 := smul_algebraMap (R := E) (A := L) (⟨_, hconj_mem⟩ : inertia Gal(L/K) P) x
    rw [MulAction.subgroup_smul_def] at h1
    exact h1
  have hgnConj : (n : Gal(L/K)) * (g : Gal(L/K)) =
      (g : Gal(L/K)) * ((g : Gal(L/K))⁻¹ * (n : Gal(L/K)) * (g : Gal(L/K))) := by group
  calc (n : Gal(L/K)) • ((g : Gal(L/K)) • algebraMap E L x)
      = ((n : Gal(L/K)) * (g : Gal(L/K))) • algebraMap E L x := by rw [mul_smul]
    _ = ((g : Gal(L/K)) *
          ((g : Gal(L/K))⁻¹ * (n : Gal(L/K)) * (g : Gal(L/K)))) • algebraMap E L x := by
            rw [hgnConj]
    _ = (g : Gal(L/K)) •
          (((g : Gal(L/K))⁻¹ * (n : Gal(L/K)) * (g : Gal(L/K))) • algebraMap E L x) := by
            rw [mul_smul]
    _ = (g : Gal(L/K)) • algebraMap E L x := by rw [hfix]

/-- The unique element of `E` whose image in `L` is `(g : Gal(L/K)) • algebraMap E L x`. -/
noncomputable def IsInertiaField.stabilizerSmul
    (g : stabilizer Gal(L/K) P) (x : E) : E :=
  (hE.toIsGaloisGroup.isInvariant.isInvariant ((g : Gal(L/K)) • algebraMap E L x)
    (IsInertiaField.stabilizer_smul_invariant K L P E g x)).choose

omit [Algebra K E] [IsScalarTower K E L] in
lemma IsInertiaField.algebraMap_stabilizerSmul
    (g : stabilizer Gal(L/K) P) (x : E) :
    algebraMap E L (IsInertiaField.stabilizerSmul K L P E g x) =
      (g : Gal(L/K)) • algebraMap E L x :=
  (hE.toIsGaloisGroup.isInvariant.isInvariant ((g : Gal(L/K)) • algebraMap E L x)
    (IsInertiaField.stabilizer_smul_invariant K L P E g x)).choose_spec

omit [Algebra K E] [IsScalarTower K E L] in
lemma IsInertiaField.stabilizerSmul_eq_iff
    (g : stabilizer Gal(L/K) P) (x y : E) :
    IsInertiaField.stabilizerSmul K L P E g x = y ↔
      algebraMap E L y = (g : Gal(L/K)) • algebraMap E L x := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl; exact IsInertiaField.algebraMap_stabilizerSmul K L P E g x
  · apply FaithfulSMul.algebraMap_injective E L
    rw [IsInertiaField.algebraMap_stabilizerSmul, h]

noncomputable instance IsInertiaField.instSMulStabilizer :
    SMul (stabilizer Gal(L/K) P) E :=
  ⟨IsInertiaField.stabilizerSmul K L P E⟩

omit [Algebra K E] [IsScalarTower K E L] in
lemma IsInertiaField.stabilizer_smul_def
    (g : stabilizer Gal(L/K) P) (x : E) :
    g • x = IsInertiaField.stabilizerSmul K L P E g x := rfl

omit [Algebra K E] [IsScalarTower K E L] in
@[simp]
lemma IsInertiaField.algebraMap_stabilizer_smul
    (g : stabilizer Gal(L/K) P) (x : E) :
    algebraMap E L (g • x) = (g : Gal(L/K)) • algebraMap E L x := by
  rw [IsInertiaField.stabilizer_smul_def]
  exact IsInertiaField.algebraMap_stabilizerSmul K L P E g x

/-- The decomposition group `stabilizer Gal(L/K) P` acts on the inertia field `E`. The action
factors through the quotient `stabilizer Gal(L/K) P ⧸ (inertia Gal(L/K) P).subgroupOf _`,
which is the Galois group of `E/D` where `D` is the decomposition field. -/
noncomputable instance IsInertiaField.stabilizerMulSemiringAction :
    MulSemiringAction (stabilizer Gal(L/K) P) E :=
  have injE : Function.Injective (algebraMap E L) := FaithfulSMul.algebraMap_injective E L
  { one_smul := fun x ↦ injE <| by
      rw [IsInertiaField.algebraMap_stabilizer_smul]; simp
    mul_smul := fun g h x ↦ injE <| by
      rw [IsInertiaField.algebraMap_stabilizer_smul,
        IsInertiaField.algebraMap_stabilizer_smul,
        IsInertiaField.algebraMap_stabilizer_smul, Subgroup.coe_mul, mul_smul]
    smul_zero := fun g ↦ injE <| by
      rw [IsInertiaField.algebraMap_stabilizer_smul]; simp
    smul_add := fun g x y ↦ injE <| by
      rw [IsInertiaField.algebraMap_stabilizer_smul, map_add, map_add, smul_add,
        IsInertiaField.algebraMap_stabilizer_smul,
        IsInertiaField.algebraMap_stabilizer_smul]
    smul_one := fun g ↦ injE <| by
      rw [IsInertiaField.algebraMap_stabilizer_smul]; simp
    smul_mul := fun g x y ↦ injE <| by
      rw [IsInertiaField.algebraMap_stabilizer_smul, map_mul, map_mul, smul_mul',
        IsInertiaField.algebraMap_stabilizer_smul,
        IsInertiaField.algebraMap_stabilizer_smul] }

noncomputable instance IsInertiaField.smulCommClass_stabilizer_K :
    SMulCommClass (stabilizer Gal(L/K) P) K E := by
  refine ⟨fun g k x ↦ ?_⟩
  apply FaithfulSMul.algebraMap_injective E L
  rw [IsInertiaField.algebraMap_stabilizer_smul, Algebra.smul_def, Algebra.smul_def,
    map_mul, map_mul, IsInertiaField.algebraMap_stabilizer_smul, smul_mul',
    ← IsScalarTower.algebraMap_apply K E L, smul_algebraMap]

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [Algebra A E] [IsScalarTower A K E] [IsScalarTower A E L]

noncomputable instance IsInertiaField.smulCommClass_stabilizer_A :
    SMulCommClass (stabilizer Gal(L/K) P) A E := by
  refine ⟨fun g a x ↦ ?_⟩
  apply FaithfulSMul.algebraMap_injective E L
  rw [IsInertiaField.algebraMap_stabilizer_smul, Algebra.smul_def, Algebra.smul_def,
    map_mul, map_mul, IsInertiaField.algebraMap_stabilizer_smul, smul_mul',
    ← IsScalarTower.algebraMap_apply A E L,
    IsScalarTower.algebraMap_apply A K L, smul_algebraMap]

/-- The decomposition group acts on `B_E := integralClosure A E` via the action on `E`. -/
noncomputable example : MulSemiringAction (stabilizer Gal(L/K) P) (integralClosure A E) :=
  inferInstance

end stabilizer_action_inertia_field

section B_E_to_B_bridge

/-!
### Bridge instances for `B_E ↪ B`

For an inertia field `E` of `P` in `L/K` and `B_E := integralClosure A E`, we establish the
prerequisites needed by `card_inertia_eq_ramificationIdxIn` and
`IsGaloisGroup.of_isFractionRing` applied to the tower `B_E → B` (with fraction fields
`E → L`):

* `IsIntegralClosure B B_E L` (via `IsIntegralClosure.tower_top`),
* `Algebra.IsIntegral B_E B`,
* `Module.Finite B_E B`,
* `IsTorsionFree B_E B`,
* `IsGaloisGroup (inertia Gal(L/K) P) B_E B`.

These are required for `ramificationIdx_under_eq_one` (`6rod.6b`), which combines
`card_inertia_eq_ramificationIdxIn` applied to `B_E → B` with
`IsInertiaField.rank_left` to conclude that the ramification index of `P` in `B/B_E`
equals `[L : E] = e(P/p)`, so the residue extension `B/P ↪ B_E/P_E` is trivial.

Stated as `theorem`s (not `instance`s) because the `K`/`L`/`E` parameters cannot be
synthesized from the conclusion and the underlying `Algebra (integralClosure A E) B` is
itself a `def` (`integralClosure.algebra_intermediateField`) rather than an `instance`.
Downstream consumers pull these in via `haveI :=`.
-/

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsDedekindDomain A] [Algebra.IsSeparable K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [Algebra A E] [IsScalarTower A K E] [IsScalarTower A E L]

set_option linter.unusedSectionVars false in
/-- `B` is the integral closure of `B_E := integralClosure A E` in `L`.

This uses `IsIntegralClosure.tower_top` on the tower `A → B_E → L` together with the fact
that every element of `integralClosure A E` is integral over `A` (instance
`integralClosure.AlgebraIsIntegral`). -/
theorem integralClosure.isIntegralClosure_intermediateField :
    letI := integralClosure.algebra_intermediateField A L E B
    haveI := integralClosure.isScalarTower_intermediateField_right A L E B
    IsIntegralClosure B (integralClosure A E) L := by
  letI := integralClosure.algebra_intermediateField A L E B
  haveI := integralClosure.isScalarTower_intermediateField_right A L E B
  exact IsIntegralClosure.tower_top (R := A) (A := integralClosure A E) (B := L) (C := B)

set_option linter.unusedSectionVars false in
/-- `B` is integral over `B_E := integralClosure A E`. -/
theorem integralClosure.algebra_isIntegral_intermediateField :
    letI := integralClosure.algebra_intermediateField A L E B
    Algebra.IsIntegral (integralClosure A E) B := by
  letI := integralClosure.algebra_intermediateField A L E B
  haveI := integralClosure.isScalarTower_intermediateField_right A L E B
  haveI : IsIntegralClosure B (integralClosure A E) L := IsIntegralClosure.tower_top (R := A) (A := integralClosure A E) (B := L) (C := B)
  exact IsIntegralClosure.isIntegral_algebra (integralClosure A E) L

set_option linter.unusedSectionVars false in
include K in
/-- `B` is module-finite over `B_E := integralClosure A E`.

Combines `integralClosure.isDedekindDomain_intermediateField` (giving
`IsIntegrallyClosed B_E` and `IsNoetherianRing B_E`) with `IsIntegralClosure.finite` on
the tower `B_E → E → L`. The latter needs `Algebra.IsSeparable E L`, which follows from
`Algebra.IsSeparable K L` via the intermediate-field tower-top instance. -/
theorem integralClosure.module_finite_intermediateField :
    letI := integralClosure.algebra_intermediateField A L E B
    Module.Finite (integralClosure A E) B := by
  letI := integralClosure.algebra_intermediateField A L E B
  haveI := integralClosure.isScalarTower_intermediateField_right A L E B
  haveI : IsIntegralClosure B (integralClosure A E) L := IsIntegralClosure.tower_top (R := A) (A := integralClosure A E) (B := L) (C := B)
  haveI : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  haveI : IsDedekindDomain (integralClosure A E) :=
    integralClosure.isDedekindDomain_intermediateField A K L E
  haveI : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_intermediateField A K L E
  haveI : FiniteDimensional E L := FiniteDimensional.right K E L
  haveI : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable K E L
  exact IsIntegralClosure.finite (integralClosure A E) E L B

set_option linter.unusedSectionVars false in
include K in
/-- `B` is torsion-free as a `B_E`-module, where `B_E := integralClosure A E`.

`B_E → E → L` is injective and `L` is a field, so `IsTorsionFree B_E L` follows; then
`IsIntegralClosure.isTorsionFree` on `B = integralClosure B_E L` transfers torsion-freeness
back to `B`. -/
theorem integralClosure.isTorsionFree_intermediateField :
    letI := integralClosure.algebra_intermediateField A L E B
    Module.IsTorsionFree (integralClosure A E) B := by
  letI := integralClosure.algebra_intermediateField A L E B
  haveI := integralClosure.isScalarTower_intermediateField_right A L E B
  haveI : IsIntegralClosure B (integralClosure A E) L := IsIntegralClosure.tower_top (R := A) (A := integralClosure A E) (B := L) (C := B)
  haveI : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_intermediateField A K L E
  -- Torsion-freeness of `L` over `B_E`: `B_E → E → L` is injective and `L` is a field.
  haveI : Module.IsTorsionFree (integralClosure A E) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective (integralClosure A E) L)
  exact IsIntegralClosure.isTorsionFree (A := B) (integralClosure A E) L

variable [MulSemiringAction Gal(L/K) B] [SMulDistribClass Gal(L/K) B L]
  [IsInertiaField K L P E]

include K L in
/-- The inertia group `inertia Gal(L/K) P` is a Galois group for `B/B_E`, where
`B_E := integralClosure A E`.

The inertia field hypothesis gives `IsGaloisGroup (inertia Gal(L/K) P) E L` (i.e. on the
fraction-field level). Combined with `Algebra.IsIntegral B_E B` and the fact that `B_E`,
being Dedekind, is integrally closed, this lifts to `IsGaloisGroup` on the integral closures
via `IsGaloisGroup.of_isFractionRing`. -/
theorem IsInertiaField.isGaloisGroup_inertia_integralClosure :
    letI := integralClosure.algebra_intermediateField A L E B
    haveI := integralClosure.isScalarTower_intermediateField_right A L E B
    IsGaloisGroup (inertia Gal(L/K) P) (integralClosure A E) B := by
  letI := integralClosure.algebra_intermediateField A L E B
  haveI := integralClosure.isScalarTower_intermediateField_right A L E B
  haveI : IsIntegralClosure B (integralClosure A E) L := IsIntegralClosure.tower_top (R := A) (A := integralClosure A E) (B := L) (C := B)
  haveI : Algebra.IsIntegral (integralClosure A E) B :=
    IsIntegralClosure.isIntegral_algebra (integralClosure A E) L
  haveI : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  haveI : IsDedekindDomain (integralClosure A E) :=
    integralClosure.isDedekindDomain_intermediateField A K L E
  haveI : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_intermediateField A K L E
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B A L).isDomain (algebraMap B L)
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  -- Force the natural restricted action on `L` (rather than the trivial inertia-field action,
  -- which Lean would otherwise pick up from `IsInertiaField.inertiaMulSemiringAction` if it
  -- speculatively unifies `E := L`).
  letI : MulSemiringAction (inertia Gal(L/K) P) L := (inertia Gal(L/K) P).mulSemiringAction
  haveI hGEL : IsGaloisGroup (inertia Gal(L/K) P) E L := ‹IsInertiaField K L P E›.toIsGaloisGroup
  haveI : SMulDistribClass (inertia Gal(L/K) P) B L :=
    ⟨fun g b x ↦ smul_distrib_smul (g : Gal(L/K)) b x⟩
  exact IsGaloisGroup.of_isFractionRing (inertia Gal(L/K) P) (integralClosure A E) B E L

end B_E_to_B_bridge
