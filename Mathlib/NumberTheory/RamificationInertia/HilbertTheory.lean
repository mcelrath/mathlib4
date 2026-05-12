/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.TotallyRamified
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

section galois_action_intermediate_field

/-!
### Action of `Gal(L/K)` on a Galois intermediate field and its integral closure

Let `F` be a field intermediate between `K` and `L` with `[Normal K F]`. The restriction map
`AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)` together with the canonical action of
`Gal(F/K)` on `F` (`AlgEquiv.applyMulSemiringAction`) yields a `MulSemiringAction Gal(L/K) F`
via `MulSemiringAction.compHom`. This lifts to `B_F := integralClosure A F` via the generic
integral-closure instance.

These are recorded as `def`s (not `instance`s) for the same diamond-avoidance reason as
`integralClosure.algebra_intermediateField`: when `F = L`, the action coincides with the
ambient hypothesis `[MulSemiringAction Gal(L/K) L]`, and we do not want Lean's instance
synthesis to introduce a second route. Downstream consumers pull these in with `letI` /
`haveI` at the point of use, paralleling the `integralClosure.algebra_intermediateField`
pattern. -/

variable (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L] [Normal K F]

/-- The Galois group `Gal(L/K)` acts on a Galois intermediate field `F`, via the restriction
homomorphism `AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)` and the canonical action of
`Gal(F/K)` on `F`.

Stated as a `def` (not an `instance`) to avoid an instance-diamond with the ambient
hypothesis `[MulSemiringAction Gal(L/K) L]` in the boundary case `F = L`. -/
@[reducible] noncomputable def IntermediateField.galoisMulSemiringAction :
    MulSemiringAction Gal(L/K) F :=
  MulSemiringAction.compHom F (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F)

@[simp]
lemma IntermediateField.algebraMap_galois_smul
    (g : Gal(L/K)) (x : F) :
    letI := IntermediateField.galoisMulSemiringAction K L F
    algebraMap F L (g • x) = (g : Gal(L/K)) • algebraMap F L x := by
  letI := IntermediateField.galoisMulSemiringAction K L F
  show algebraMap F L (AlgEquiv.restrictNormalHom F g x) = g (algebraMap F L x)
  exact AlgEquiv.restrictNormal_commutes g F x

/-- The induced `SMulCommClass` over the base field `K`. -/
@[reducible] noncomputable def IntermediateField.galoisSmulCommClass_K :
    letI := IntermediateField.galoisMulSemiringAction K L F
    SMulCommClass Gal(L/K) K F := by
  letI := IntermediateField.galoisMulSemiringAction K L F
  refine ⟨fun g k x ↦ ?_⟩
  apply FaithfulSMul.algebraMap_injective F L
  rw [IntermediateField.algebraMap_galois_smul, Algebra.smul_def, Algebra.smul_def,
    map_mul, map_mul, IntermediateField.algebraMap_galois_smul, smul_mul',
    ← IsScalarTower.algebraMap_apply K F L, smul_algebraMap]

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [Algebra A F] [IsScalarTower A K F] [IsScalarTower A F L]

/-- The induced `SMulCommClass` over the base ring `A`. -/
@[reducible] noncomputable def IntermediateField.galoisSmulCommClass_A :
    letI := IntermediateField.galoisMulSemiringAction K L F
    SMulCommClass Gal(L/K) A F := by
  letI := IntermediateField.galoisMulSemiringAction K L F
  refine ⟨fun g a x ↦ ?_⟩
  apply FaithfulSMul.algebraMap_injective F L
  rw [IntermediateField.algebraMap_galois_smul, Algebra.smul_def, Algebra.smul_def,
    map_mul, map_mul, IntermediateField.algebraMap_galois_smul, smul_mul',
    ← IsScalarTower.algebraMap_apply A F L,
    IsScalarTower.algebraMap_apply A K L, smul_algebraMap]

/-- The Galois group `Gal(L/K)` acts on `B_F := integralClosure A F` via the action on `F`.

Stated as a `def` (not an `instance`) since the underlying action on `F`
(`IntermediateField.galoisMulSemiringAction`) is itself a `def`. Downstream consumers pull
both in with `letI` / `haveI`. -/
@[reducible] noncomputable def IntermediateField.galoisMulSemiringAction_integralClosure :
    MulSemiringAction Gal(L/K) (integralClosure A F) :=
  letI := IntermediateField.galoisMulSemiringAction K L F
  letI := IntermediateField.galoisSmulCommClass_A A K L F
  inferInstance

omit [IsFractionRing A K] [IsScalarTower A K F] in
@[simp]
lemma IntermediateField.coe_galois_smul_integralClosure
    (g : Gal(L/K)) (x : integralClosure A F) :
    letI := IntermediateField.galoisMulSemiringAction K L F
    letI := IntermediateField.galoisMulSemiringAction_integralClosure A K L F
    ((g • x : integralClosure A F) : F) = g • (x : F) := by
  letI := IntermediateField.galoisMulSemiringAction K L F
  letI := IntermediateField.galoisSmulCommClass_A A K L F
  letI := IntermediateField.galoisMulSemiringAction_integralClosure A K L F
  rfl

end galois_action_intermediate_field

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

section ramificationIdx_under

/-!
### Ramification of `P_E := P ∩ B_E` over `p` is trivial

Let `E` be an inertia field of `P` in `L/K` and let `B_E := integralClosure A E` and
`P_E := P.under B_E`. The classical Hilbert-theory statement is that the ramification of `p`
in `B_E` is trivial:

  `e(P_E / p) = 1`.

The proof is tower-arithmetic: with `R = ramificationIdxIn p B`,
`IsInertiaField.rank_left` gives `[L : E] = R`. On the upper tower, the bridge instances of
`B_E ↪ B` make `inertia Gal(L/K) P` a Galois group for `B/B_E`, and the inertia subgroup of
`P` *within* that inertia group is the whole group (a direct algebraic identity, see
`AddSubgroup.subgroupOf_inertia` and `Subgroup.subgroupOf_self`). So
`card_inertia_eq_ramificationIdxIn` applied at the upper level gives
`Nat.card (inertia Gal(L/K) P) = ramificationIdxIn P_E B`, which by the lower-level instance
of the same lemma also equals `ramificationIdxIn p B`. The tower formula
`e(P / p) = e(P_E / p) · e(P / P_E)` together with `e(P / P_E) = R = e(P / p)` (after
unfolding `ramificationIdxIn` via `ramificationIdxIn_eq_ramificationIdx`) forces
`e(P_E / p) = 1`, using that `e(P / P_E) ≠ 0` for a non-zero prime of a Dedekind domain.
-/

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsDedekindDomain A] [Algebra.IsSeparable K L]
  [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [Algebra A E] [IsScalarTower A K E] [IsScalarTower A E L]
variable [MulSemiringAction Gal(L/K) B] [SMulDistribClass Gal(L/K) B L]
  [IsGaloisGroup Gal(L/K) A B] [IsInertiaField K L P E]
  [P.IsMaximal] [Ring.HasFiniteQuotients A]

set_option linter.unusedSectionVars false in
include K L in
/-- The ramification index of `p` in `B_E := integralClosure A E` is one, when `E` is the
inertia field of `P` in `L/K` (and `p` is non-zero).

This is the classical statement that the inertia field absorbs all the ramification: in the
tower `A → B_E → B`, all the ramification of `p` in `B` comes from the upper step
`B_E → B`, and the lower step `A → B_E` is unramified at `P_E := P.under B_E`. -/
theorem IsInertiaField.ramificationIdx_under_eq_one (hp : p ≠ ⊥) :
    letI := integralClosure.algebra_intermediateField A L E B
    Ideal.ramificationIdx p
      (P.under (integralClosure A E)) = 1 := by
  classical
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (integralClosure A E) B :=
    integralClosure.algebra_intermediateField A L E B
  haveI : IsScalarTower (integralClosure A E) B L :=
    integralClosure.isScalarTower_intermediateField_right A L E B
  haveI : IsScalarTower A (integralClosure A E) B :=
    integralClosure.isScalarTower_intermediateField A L E B
  haveI : IsIntegralClosure B (integralClosure A E) L :=
    IsIntegralClosure.tower_top (R := A) (A := integralClosure A E) (B := L) (C := B)
  haveI : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  haveI : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable K E L
  haveI : IsDedekindDomain (integralClosure A E) :=
    integralClosure.isDedekindDomain_intermediateField A K L E
  haveI : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_intermediateField A K L E
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : Module.Finite A (integralClosure A E) :=
    IsIntegralClosure.finite A K E (integralClosure A E)
  haveI : Module.IsTorsionFree A (integralClosure A E) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    -- `A → K ↪ E` is injective; this factors through `integralClosure A E`.
    intro x y hxy
    have hAE : Function.Injective (algebraMap A E) := by
      intro x y hxy
      have := (FaithfulSMul.algebraMap_injective K E).comp (IsFractionRing.injective A K)
      apply this
      simp only [Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A K E, ← IsScalarTower.algebraMap_apply A K E, hxy]
    apply hAE
    rw [IsScalarTower.algebraMap_apply A (integralClosure A E) E,
        IsScalarTower.algebraMap_apply A (integralClosure A E) E, hxy]
  haveI : Module.Finite (integralClosure A E) B :=
    integralClosure.module_finite_intermediateField A K L E
  haveI : Module.IsTorsionFree (integralClosure A E) B :=
    integralClosure.isTorsionFree_intermediateField A K L E
  haveI : Algebra.IsIntegral (integralClosure A E) B := by
    haveI : IsFractionRing (integralClosure A E) E :=
      integralClosure.isFractionRing_intermediateField A K L E
    exact IsIntegralClosure.isIntegral_algebra (integralClosure A E) L
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B A L).isDomain (algebraMap B L)
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  -- Galois-group structure of the upper tower.
  letI : MulSemiringAction (inertia Gal(L/K) P) L := (inertia Gal(L/K) P).mulSemiringAction
  haveI : IsGaloisGroup (inertia Gal(L/K) P) (integralClosure A E) B :=
    IsInertiaField.isGaloisGroup_inertia_integralClosure A K L P E
  -- The lifted primes are in the right configuration.
  haveI : P.LiesOver (P.under (integralClosure A E)) :=
    Ideal.over_under (A := integralClosure A E) P
  haveI : (P.under (integralClosure A E)).LiesOver p :=
    Ideal.under_liesOver_of_liesOver (A := A) (B := integralClosure A E) (𝔓 := P) p
  have hP_ne_bot : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have hPE_ne_bot : P.under (integralClosure A E) ≠ ⊥ :=
    Ideal.under_ne_bot (A := integralClosure A E) hP_ne_bot
  haveI : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  haveI : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  haveI : PerfectField (A ⧸ p) := PerfectField.ofFinite
  haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- For the upper layer we need separability of the residue extension `BE/PE → B/P`,
  -- which follows from finiteness of `BE/PE` (a perfect field).
  haveI : Ring.HasFiniteQuotients (integralClosure A E) :=
    Ring.HasFiniteQuotients.of_module_finite (R := A) (integralClosure A E)
  haveI : (P.under (integralClosure A E)).IsMaximal :=
    over_def P (P.under (integralClosure A E)) ▸
      Ideal.IsMaximal.under (integralClosure A E) P
  letI : Field (integralClosure A E ⧸ P.under (integralClosure A E)) :=
    Ideal.Quotient.field _
  haveI : Finite (integralClosure A E ⧸ P.under (integralClosure A E)) :=
    Ring.HasFiniteQuotients.finiteQuotient hPE_ne_bot
  haveI : PerfectField (integralClosure A E ⧸ P.under (integralClosure A E)) :=
    PerfectField.ofFinite
  haveI : Algebra.IsSeparable
      (integralClosure A E ⧸ P.under (integralClosure A E)) (B ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- Inertia of `P` inside the inertia group of `P` is the whole inertia group.
  have hinertia_top : P.inertia (inertia Gal(L/K) P) = ⊤ := by
    show AddSubgroup.inertia P.toAddSubgroup (inertia Gal(L/K) P) = ⊤
    rw [← AddSubgroup.subgroupOf_inertia]
    exact Subgroup.subgroupOf_self _
  -- Card identity on the upper tower.
  have hcard_upper :
      Nat.card (P.inertia (inertia Gal(L/K) P)) =
        Ideal.ramificationIdxIn (P.under (integralClosure A E)) B :=
    card_inertia_eq_ramificationIdxIn (G := inertia Gal(L/K) P)
      (R := integralClosure A E) (S := B) (P.under (integralClosure A E)) hPE_ne_bot P
  -- Card identity on the lower tower.
  have hcard_lower :
      Nat.card (inertia Gal(L/K) P) = Ideal.ramificationIdxIn p B :=
    card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (R := A) (S := B) p hp P
  -- Combine: `ramificationIdxIn PE B = ramificationIdxIn p B`.
  have hRE_eq_R : Ideal.ramificationIdxIn (P.under (integralClosure A E)) B =
      Ideal.ramificationIdxIn p B := by
    have h1 : Nat.card (P.inertia (inertia Gal(L/K) P)) = Nat.card (inertia Gal(L/K) P) := by
      rw [hinertia_top, Nat.card_congr (Subgroup.topEquiv.toEquiv)]
    rw [← hcard_upper, h1, hcard_lower]
  -- Unfold `ramificationIdxIn` via `P` as the canonical representative.
  have hR_eq : Ideal.ramificationIdxIn p B = Ideal.ramificationIdx p P :=
    ramificationIdxIn_eq_ramificationIdx (G := Gal(L/K)) p P
  have hRE_eq : Ideal.ramificationIdxIn (P.under (integralClosure A E)) B =
      Ideal.ramificationIdx (P.under (integralClosure A E)) P :=
    ramificationIdxIn_eq_ramificationIdx (G := inertia Gal(L/K) P)
      (P.under (integralClosure A E)) P
  -- Tower formula: `e(P/p) = e(PE/p) · e(P/PE)`.
  have htower : Ideal.ramificationIdx p P =
      Ideal.ramificationIdx p (P.under (integralClosure A E)) *
        Ideal.ramificationIdx (P.under (integralClosure A E)) P :=
    Ideal.ramificationIdx_algebra_tower' (R := A) (S := integralClosure A E) (T := B)
      p (P.under (integralClosure A E)) P
  -- `e(PE/P) = e(p/P)` via `ramificationIdxIn` equality.
  have key : Ideal.ramificationIdx (P.under (integralClosure A E)) P =
      Ideal.ramificationIdx p P := by
    rw [← hRE_eq, ← hR_eq, hRE_eq_R]
  rw [key] at htower
  have hR_pos : Ideal.ramificationIdx p P ≠ 0 :=
    IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  have hcancel : Ideal.ramificationIdx p (P.under (integralClosure A E)) *
      Ideal.ramificationIdx p P = 1 * Ideal.ramificationIdx p P := by
    rw [one_mul]; exact htower.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hR_pos) hcancel

end ramificationIdx_under

section isTotallyRamifiedIn_upper

/-!
### Total ramification in the upper tower `B_E → B`

Let `E` be an inertia field of `P` in `L/K` and let `B_E := integralClosure A E` and
`P_E := P.under B_E`. The classical Hilbert-theory statement is that all the ramification of
`p` is absorbed in the upper step:

  `P_E.IsTotallyRamifiedIn B`.

The proof composes:
* `IsInertiaField.rank_left` : `[L : E] = ramificationIdxIn p B`;
* `ramificationIdxIn_eq_ramificationIdx` (applied to the lower tower with Galois group
  `Gal(L/K)`) : `ramificationIdxIn p B = ramificationIdx p P`;
* `ramificationIdx_algebra_tower'` : `ramificationIdx p P = ramificationIdx p P_E *
  ramificationIdx P_E P`;
* `IsInertiaField.ramificationIdx_under_eq_one` : `ramificationIdx p P_E = 1`;

which combine to `ramificationIdx P_E P = [L : E] = [B : B_E]` (the latter via
`Algebra.IsAlgebraic.finrank_of_isFractionRing` on `B_E → E → B → L`). The conclusion follows
from `isTotallyRamifiedIn_of_ramificationIdx_eq_finrank`.
-/

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsDedekindDomain A] [Algebra.IsSeparable K L]
  [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [Algebra A E] [IsScalarTower A K E] [IsScalarTower A E L]
variable [MulSemiringAction Gal(L/K) B] [SMulDistribClass Gal(L/K) B L]
  [IsGaloisGroup Gal(L/K) A B] [IsInertiaField K L P E]
  [P.IsMaximal] [Ring.HasFiniteQuotients A]

set_option linter.unusedSectionVars false in
include K L in
/-- **Total ramification in the upper tower.** Let `L/K` be a finite separable Galois extension
of fields with Dedekind integer rings `A ⊆ K` and `B ⊆ L` (with `B` the integral closure of `A`
in `L`), and let `E` be the inertia field of a maximal prime `P` of `B` over a non-zero prime
`p` of `A`. Then `P_E := P.under (integralClosure A E)` is totally ramified in `B`. -/
theorem IsInertiaField.isTotallyRamifiedIn_upper (hp : p ≠ ⊥) :
    letI := integralClosure.algebra_intermediateField A L E B
    Ideal.IsTotallyRamifiedIn B (P.under (integralClosure A E)) := by
  classical
  letI : Algebra (integralClosure A E) B :=
    integralClosure.algebra_intermediateField A L E B
  haveI : IsScalarTower (integralClosure A E) B L :=
    integralClosure.isScalarTower_intermediateField_right A L E B
  haveI : IsScalarTower A (integralClosure A E) B :=
    integralClosure.isScalarTower_intermediateField A L E B
  haveI : IsIntegralClosure B (integralClosure A E) L :=
    IsIntegralClosure.tower_top (R := A) (A := integralClosure A E) (B := L) (C := B)
  haveI : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  haveI : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable K E L
  haveI : IsDedekindDomain (integralClosure A E) :=
    integralClosure.isDedekindDomain_intermediateField A K L E
  haveI : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_intermediateField A K L E
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : FiniteDimensional E L := FiniteDimensional.right K E L
  haveI : Module.Finite A (integralClosure A E) :=
    IsIntegralClosure.finite A K E (integralClosure A E)
  haveI : Module.Finite (integralClosure A E) B :=
    integralClosure.module_finite_intermediateField A K L E
  haveI : Module.IsTorsionFree (integralClosure A E) B :=
    integralClosure.isTorsionFree_intermediateField A K L E
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B A L).isDomain (algebraMap B L)
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  -- The lifted primes are in the right configuration.
  haveI : P.LiesOver (P.under (integralClosure A E)) :=
    Ideal.over_under (A := integralClosure A E) P
  haveI : (P.under (integralClosure A E)).LiesOver p :=
    Ideal.under_liesOver_of_liesOver (A := A) (B := integralClosure A E) (𝔓 := P) p
  have hP_ne_bot : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have hPE_ne_bot : P.under (integralClosure A E) ≠ ⊥ :=
    Ideal.under_ne_bot (A := integralClosure A E) hP_ne_bot
  haveI : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  haveI : Ring.HasFiniteQuotients (integralClosure A E) :=
    Ring.HasFiniteQuotients.of_module_finite (R := A) (integralClosure A E)
  haveI hPE_max : (P.under (integralClosure A E)).IsMaximal :=
    over_def P (P.under (integralClosure A E)) ▸
      Ideal.IsMaximal.under (integralClosure A E) P
  -- `Module.IsTorsionFree A (integralClosure A E)` (needed for `ramificationIdx_algebra_tower'`).
  haveI : Module.IsTorsionFree A (integralClosure A E) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    intro x y hxy
    have hAE : Function.Injective (algebraMap A E) := by
      intro a b hab
      have := (FaithfulSMul.algebraMap_injective K E).comp (IsFractionRing.injective A K)
      apply this
      simp only [Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A K E, ← IsScalarTower.algebraMap_apply A K E, hab]
    apply hAE
    rw [IsScalarTower.algebraMap_apply A (integralClosure A E) E,
        IsScalarTower.algebraMap_apply A (integralClosure A E) E, hxy]
  -- `NoZeroSMulDivisors B_E B` from injectivity of `algebraMap`.
  haveI hinj_BE_B : Function.Injective (algebraMap (integralClosure A E) B) := by
    intro x y hxy
    have hL : algebraMap (integralClosure A E) L x = algebraMap (integralClosure A E) L y := by
      rw [IsScalarTower.algebraMap_apply (integralClosure A E) B L,
          IsScalarTower.algebraMap_apply (integralClosure A E) B L, hxy]
    exact FaithfulSMul.algebraMap_injective (integralClosure A E) L hL
  haveI : NoZeroSMulDivisors (integralClosure A E) B := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Or.inl (hinj_BE_B (by simpa using h1))
    · exact Or.inr h2
  -- Step 1: `IsInertiaField.rank_left` : `[L : E] = ramificationIdxIn p B`.
  have hrk : Module.finrank E L = Ideal.ramificationIdxIn p B :=
    IsInertiaField.rank_left A K L P E hp
  -- Step 2: `ramificationIdxIn p B = ramificationIdx p P`.
  have hidxIn : Ideal.ramificationIdxIn p B = Ideal.ramificationIdx p P :=
    ramificationIdxIn_eq_ramificationIdx (G := Gal(L/K)) p P
  -- Step 3: tower formula `e(P|p) = e(P_E|p) * e(P|P_E)`.
  have htower : Ideal.ramificationIdx p P =
      Ideal.ramificationIdx p (P.under (integralClosure A E)) *
        Ideal.ramificationIdx (P.under (integralClosure A E)) P :=
    Ideal.ramificationIdx_algebra_tower' (R := A) (S := integralClosure A E) (T := B)
      p (P.under (integralClosure A E)) P
  -- Step 4: `e(P_E|p) = 1` from `IsInertiaField.ramificationIdx_under_eq_one`.
  have hPE_eq_one : Ideal.ramificationIdx p (P.under (integralClosure A E)) = 1 :=
    IsInertiaField.ramificationIdx_under_eq_one A K L P E hp
  rw [hPE_eq_one, one_mul] at htower
  -- Step 5: `[L : E] = [B : B_E]` via `Algebra.IsAlgebraic.finrank_of_isFractionRing`.
  have hfr_bridge : Module.finrank E L = Module.finrank (integralClosure A E) B :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing (integralClosure A E) E B L
  -- Combine: `e(P_E, P) = [B : B_E]`.
  have hePE_P_eq : Ideal.ramificationIdx (P.under (integralClosure A E)) P =
      Module.finrank (integralClosure A E) B := by
    rw [← hfr_bridge, hrk, hidxIn, ← htower]
  exact isTotallyRamifiedIn_of_ramificationIdx_eq_finrank
    (R := integralClosure A E) (S := B) E L hPE_ne_bot P hePE_P_eq

end isTotallyRamifiedIn_upper

section inertia_map_restrictNormalHom

/-!
### Inertia under restriction to a Galois intermediate field

Let `F` be a Galois intermediate field of `L/K`. The restriction homomorphism
`q := AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)` carries `P.inertia Gal(L/K)`
into `(P.under B_F).inertia Gal(F/K)`, where `B_F := integralClosure A F`.

This is the forward inclusion in the inertia-vs-restriction match
`q (P.inertia Gal(L/K)) = (P.under B_F).inertia Gal(F/K)`; the reverse inclusion
(via cardinality matching) is proved separately. -/

variable [Algebra A K] [Algebra A L] [IsScalarTower A K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [MulSemiringAction Gal(L/K) B] [SMulDistribClass Gal(L/K) B L]
variable (F : IntermediateField K L) [Normal K F]
  [Algebra A F] [IsScalarTower A K F] [IsScalarTower A F L]

set_option linter.unusedSectionVars false in
include K L in
/-- **Forward inclusion of the inertia-vs-restriction match.** Let `F` be a Galois
intermediate field of `L/K`, let `q := AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)`
be the restriction map, and let `B_F := integralClosure A F`. Then `q` carries the inertia
group of `P` in `Gal(L/K)` into the inertia group of `P_F := P.under B_F` in `Gal(F/K)`. -/
theorem IntermediateField.inertia_map_restrictNormalHom_le :
    letI := integralClosure.algebra_intermediateField A L F B
    Subgroup.map (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K))
        (P.inertia Gal(L/K)) ≤
      (P.under (integralClosure A F)).inertia Gal(F/K) := by
  letI : Algebra (integralClosure A F) B :=
    integralClosure.algebra_intermediateField A L F B
  haveI : IsScalarTower A (integralClosure A F) B :=
    integralClosure.isScalarTower_intermediateField A L F B
  haveI : IsScalarTower (integralClosure A F) B L :=
    integralClosure.isScalarTower_intermediateField_right A L F B
  letI := IntermediateField.galoisMulSemiringAction K L F
  letI := IntermediateField.galoisMulSemiringAction_integralClosure A K L F
  rintro _ ⟨σ, hσ, rfl⟩
  rw [AddSubgroup.mem_inertia]
  intro x
  -- Need: `AlgEquiv.restrictNormalHom F σ • x - x ∈ P.under (integralClosure A F)`.
  show _ ∈ Ideal.comap (algebraMap (integralClosure A F) B) P
  rw [Ideal.mem_comap, map_sub]
  -- Reduce to membership of `σ • algebraMap _ _ x - algebraMap _ _ x` in `P`,
  -- using that `algebraMap B_F B` intertwines `AlgEquiv.restrictNormalHom F σ` with `σ`.
  have hkey : algebraMap (integralClosure A F) B
      (AlgEquiv.restrictNormalHom F σ • x) =
        σ • algebraMap (integralClosure A F) B x := by
    apply IsIntegralClosure.algebraMap_injective B A L
    -- Reduce both sides to `algebraMap (integralClosure A F) L _`.
    rw [← IsScalarTower.algebraMap_apply (integralClosure A F) B L,
        algebraMap.smul' (A := Gal(L/K)) (B := B) (C := L),
        ← IsScalarTower.algebraMap_apply (integralClosure A F) B L,
        IsScalarTower.algebraMap_apply (integralClosure A F) F L,
        IsScalarTower.algebraMap_apply (integralClosure A F) F L]
    show algebraMap F L ((AlgEquiv.restrictNormalHom F σ • x : integralClosure A F) : F) =
        σ • algebraMap F L ((x : integralClosure A F) : F)
    rw [integralClosure.coe_smul (AlgEquiv.restrictNormalHom F σ) x]
    -- Goal: algebraMap F L (q σ • (x : F)) = σ • algebraMap F L (x : F).
    -- The `q σ • _ : F` is the canonical Gal(F/K)-action on F, which by
    -- `restrictNormal_commutes` agrees with `σ` after `algebraMap F L`.
    exact AlgEquiv.restrictNormal_commutes σ F (x : F)
  rw [hkey]
  -- Now it suffices that `σ • y - y ∈ P` for `y := algebraMap _ _ x`, which is `hσ`.
  exact (AddSubgroup.mem_inertia.mp hσ) _

set_option maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
attribute [local instance] Ideal.Quotient.field in
include K L in
/-- **Cardinality matching of inertia under restriction.** Let `F` be a Galois intermediate
field of `L/K`, `q := AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)`, and
`B_F := integralClosure A F`. The cardinality of the image of `P.inertia Gal(L/K)` under `q`
equals the cardinality of the inertia group of `P_F := P.under B_F` in `Gal(F/K)`.

Combined with the forward inclusion `inertia_map_restrictNormalHom_le`, this gives the
set equality `q (P.inertia Gal(L/K)) = (P.under B_F).inertia Gal(F/K)`.

The proof is the cyclotomic precedent (`DedekindZetaCharacterProduct.lean:1598-1615`) lifted
to the abstract Hilbert-theory setting: identify the kernel of the restricted map
`q|_{P.inertia} : P.inertia Gal(L/K) → Gal(F/K)` as `F.fixingSubgroup.subgroupOf P.inertia`,
use `Subgroup.subgroupOf_map_subtype` + `AddSubgroup.inertia_map_subtype` to rewrite this
as `(P.inertia F.fixingSubgroup)`, apply `card_inertia_eq_ramificationIdxIn` for the lower
(`F.fixingSubgroup` on `B_F → B`) and full (`Gal(L/K)` on `A → B`) tower, identify the
target via `card_inertia_eq_ramificationIdxIn` for `Gal(F/K)` on `A → B_F`, and combine
using the multiplicativity of `ramificationIdxIn` over the tower
(`Ideal.ramificationIdxIn_mul_ramificationIdxIn'`). -/
theorem IntermediateField.inertia_map_restrictNormalHom_card_eq
    [IsFractionRing A K] [FiniteDimensional K L] [IsDedekindDomain A]
    [Algebra.IsSeparable K L] [IsDedekindDomain B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [IsGaloisGroup Gal(L/K) A B] [P.IsMaximal]
    [Ring.HasFiniteQuotients A] (hp : p ≠ ⊥) :
    letI := integralClosure.algebra_intermediateField A L F B
    Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K))
        (P.inertia Gal(L/K))) =
      Nat.card ((P.under (integralClosure A F)).inertia Gal(F/K)) := by
  classical
  -- B_F bridge instances (same as `isTotallyRamifiedIn_upper`).
  letI : Algebra (integralClosure A F) B :=
    integralClosure.algebra_intermediateField A L F B
  haveI : IsScalarTower A (integralClosure A F) B :=
    integralClosure.isScalarTower_intermediateField A L F B
  haveI : IsScalarTower (integralClosure A F) B L :=
    integralClosure.isScalarTower_intermediateField_right A L F B
  haveI : IsIntegralClosure B (integralClosure A F) L :=
    IsIntegralClosure.tower_top (R := A) (A := integralClosure A F) (B := L) (C := B)
  haveI : Algebra.IsSeparable K F := Algebra.isSeparable_tower_bot_of_isSeparable K F L
  haveI : Algebra.IsSeparable F L := Algebra.isSeparable_tower_top_of_isSeparable K F L
  haveI : IsDedekindDomain (integralClosure A F) :=
    integralClosure.isDedekindDomain_intermediateField A K L F
  haveI : IsFractionRing (integralClosure A F) F :=
    integralClosure.isFractionRing_intermediateField A K L F
  haveI : FiniteDimensional K F := FiniteDimensional.left K F L
  haveI : FiniteDimensional F L := FiniteDimensional.right K F L
  haveI : Module.Finite A (integralClosure A F) :=
    IsIntegralClosure.finite A K F (integralClosure A F)
  haveI : Module.Finite (integralClosure A F) B :=
    integralClosure.module_finite_intermediateField A K L F
  haveI : Module.IsTorsionFree (integralClosure A F) B :=
    integralClosure.isTorsionFree_intermediateField A K L F
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B A L).isDomain (algebraMap B L)
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  -- LiesOver chain.
  haveI : P.LiesOver (P.under (integralClosure A F)) :=
    Ideal.over_under (A := integralClosure A F) P
  haveI : (P.under (integralClosure A F)).LiesOver p :=
    Ideal.under_liesOver_of_liesOver (A := A) (B := integralClosure A F) (𝔓 := P) p
  have hP_ne_bot : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have hPF_ne_bot : P.under (integralClosure A F) ≠ ⊥ :=
    Ideal.under_ne_bot (A := integralClosure A F) hP_ne_bot
  haveI : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  haveI : Ring.HasFiniteQuotients (integralClosure A F) :=
    Ring.HasFiniteQuotients.of_module_finite (R := A) (integralClosure A F)
  haveI hPF_max : (P.under (integralClosure A F)).IsMaximal :=
    over_def P (P.under (integralClosure A F)) ▸
      Ideal.IsMaximal.under (integralClosure A F) P
  haveI : Module.IsTorsionFree A (integralClosure A F) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    intro x y hxy
    have hAF : Function.Injective (algebraMap A F) := by
      intro a b hab
      have := (FaithfulSMul.algebraMap_injective K F).comp (IsFractionRing.injective A K)
      apply this
      simp only [Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A K F, ← IsScalarTower.algebraMap_apply A K F, hab]
    apply hAF
    rw [IsScalarTower.algebraMap_apply A (integralClosure A F) F,
        IsScalarTower.algebraMap_apply A (integralClosure A F) F, hxy]
  haveI : Ring.HasFiniteQuotients B :=
    Ring.HasFiniteQuotients.of_module_finite (R := A) B
  -- Galois actions on F and B_F via the canonical/intermediate-field action.
  haveI hGalLK_KL : IsGaloisGroup Gal(L/K) K L :=
    IsGaloisGroup.to_isFractionRing Gal(L/K) A B K L
  haveI hGalKL : IsGalois K L := IsGaloisGroup.isGalois Gal(L/K) K L
  haveI hGalKF : IsGalois K F :=
    { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable K F L
      to_normal := ‹Normal K F› }
  letI : MulSemiringAction Gal(F/K) F := AlgEquiv.applyMulSemiringAction
  haveI hGalGFK_F : IsGaloisGroup Gal(F/K) K F := IsGaloisGroup.of_isGalois K F
  haveI hGalGFK_BF : IsGaloisGroup Gal(F/K) A (integralClosure A F) :=
    IsGaloisGroup.of_isFractionRing Gal(F/K) A (integralClosure A F) K F
  -- F.fixingSubgroup is a Galois group for L/F, and lifts to B_F → B.
  haveI hGalSub_FL : IsGaloisGroup F.fixingSubgroup F L := by
    apply IsGaloisGroup.subgroup_iff.mpr
    exact IsGalois.fixedField_fixingSubgroup (K := F)
  letI hmsa_L : MulSemiringAction (↥F.fixingSubgroup) L := inferInstance
  haveI hsd_BL : SMulDistribClass (↥F.fixingSubgroup) B L := ⟨fun g b x ↦
    smul_distrib_smul (g : Gal(L/K)) b x⟩
  haveI hGalSub_BFB : IsGaloisGroup F.fixingSubgroup (integralClosure A F) B :=
    IsGaloisGroup.of_isFractionRing F.fixingSubgroup (integralClosure A F) B F L
  -- Separability of residue extensions.
  haveI : Finite (B ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP_ne_bot
  haveI : Finite (integralClosure A F ⧸ P.under (integralClosure A F)) :=
    Ring.HasFiniteQuotients.finiteQuotient hPF_ne_bot
  haveI : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  haveI : PerfectField (A ⧸ p) := inferInstance
  haveI : PerfectField (integralClosure A F ⧸ P.under (integralClosure A F)) := inferInstance
  haveI h_isSep_AP : Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by
    haveI : Module.Finite (A ⧸ p) (B ⧸ P) :=
      (Module.finite_iff_finite (R := A ⧸ p)).mpr ‹_›
    haveI : Algebra.IsAlgebraic (A ⧸ p) (B ⧸ P) := Algebra.IsAlgebraic.of_finite _ _
    exact inferInstance
  haveI h_isSep_APF : Algebra.IsSeparable (A ⧸ p) (integralClosure A F ⧸ P.under (integralClosure A F)) := by
    haveI : Module.Finite (A ⧸ p) (integralClosure A F ⧸ P.under (integralClosure A F)) :=
      (Module.finite_iff_finite (R := A ⧸ p)).mpr ‹_›
    haveI : Algebra.IsAlgebraic (A ⧸ p) (integralClosure A F ⧸ P.under (integralClosure A F)) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact inferInstance
  haveI h_isSep_PFP : Algebra.IsSeparable (integralClosure A F ⧸ P.under (integralClosure A F)) (B ⧸ P) := by
    haveI : Module.Finite (integralClosure A F ⧸ P.under (integralClosure A F)) (B ⧸ P) :=
      (Module.finite_iff_finite (R := integralClosure A F ⧸ P.under (integralClosure A F))).mpr ‹_›
    haveI : Algebra.IsAlgebraic (integralClosure A F ⧸ P.under (integralClosure A F)) (B ⧸ P) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact inferInstance
  -- Now the DZCP 1598-1615 chain.
  let restrictF : Gal(L/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hker_F_eq : restrictF.ker = F.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker F
  -- First iso: |ker(q|_I)| * |image| = |P.inertia|.
  let f_r := restrictF.restrict (P.inertia Gal(L/K))
  have hrange_f_r : f_r.range = (P.inertia Gal(L/K)).map restrictF :=
    MonoidHom.restrict_range _ _
  have hfirst_iso : Nat.card f_r.ker * Nat.card f_r.range =
      Nat.card (P.inertia Gal(L/K)) := by
    have h := f_r.ker.card_mul_index
    rw [Subgroup.index_ker] at h
    exact h
  have hker_f_r : f_r.ker = F.fixingSubgroup.subgroupOf (P.inertia Gal(L/K)) := by
    rw [MonoidHom.ker_restrict, hker_F_eq]
  -- Identify |ker(q|_I)| = |P.inertia F.fixingSubgroup| via the 17-LOC chain.
  have hcard_ker_f_r :
      Nat.card f_r.ker = Nat.card (P.inertia F.fixingSubgroup) := by
    rw [hker_f_r]
    have h1 : Nat.card ↥(F.fixingSubgroup.subgroupOf (P.inertia Gal(L/K))) =
        Nat.card ↥((F.fixingSubgroup.subgroupOf (P.inertia Gal(L/K))).map
          (P.inertia Gal(L/K)).subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv
    have h2 : (F.fixingSubgroup.subgroupOf (P.inertia Gal(L/K))).map
        (P.inertia Gal(L/K)).subtype = F.fixingSubgroup ⊓ P.inertia Gal(L/K) :=
      Subgroup.subgroupOf_map_subtype _ _
    have h3 : Nat.card ↥(P.inertia F.fixingSubgroup) =
        Nat.card ↥((P.inertia F.fixingSubgroup).map F.fixingSubgroup.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv
    have h4 : (P.inertia F.fixingSubgroup).map F.fixingSubgroup.subtype =
        P.inertia Gal(L/K) ⊓ F.fixingSubgroup :=
      AddSubgroup.inertia_map_subtype P.toAddSubgroup F.fixingSubgroup
    rw [h1, h2, h3, h4, inf_comm]
  -- Cardinality identifications via card_inertia_eq_ramificationIdxIn.
  have hcard_inertia_L : Nat.card (P.inertia Gal(L/K)) =
      Ideal.ramificationIdxIn p B :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) p hp P
  have hcard_inertia_F : Nat.card ((P.under (integralClosure A F)).inertia Gal(F/K)) =
      Ideal.ramificationIdxIn p (integralClosure A F) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(F/K)) p hp (P.under (integralClosure A F))
  have hcard_inertia_FL : Nat.card (P.inertia F.fixingSubgroup) =
      Ideal.ramificationIdxIn (P.under (integralClosure A F)) B :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := F.fixingSubgroup) (P.under (integralClosure A F))
      hPF_ne_bot P
  -- Tower law.
  have htower : Ideal.ramificationIdxIn p (integralClosure A F) *
        Ideal.ramificationIdxIn (P.under (integralClosure A F)) B =
      Ideal.ramificationIdxIn p B :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn' (P.under (integralClosure A F))
      (G := Gal(F/K)) (GAC := Gal(L/K)) (GBC := F.fixingSubgroup) B
  -- Non-zero values for cancellation.
  have hram_FL_ne_zero : Ideal.ramificationIdxIn (P.under (integralClosure A F)) B ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (G := F.fixingSubgroup) hPF_ne_bot
  -- Combine: |image| = ramificationIdxIn p B_F.
  have hcard_image : Nat.card f_r.range = Ideal.ramificationIdxIn p (integralClosure A F) := by
    have hfiso2 := hfirst_iso
    rw [hcard_ker_f_r, hcard_inertia_FL, hcard_inertia_L] at hfiso2
    -- hfiso2 : ramificationIdxIn PF B * |range| = ramificationIdxIn p B
    have hkey : Ideal.ramificationIdxIn (P.under (integralClosure A F)) B *
        Nat.card f_r.range =
        Ideal.ramificationIdxIn (P.under (integralClosure A F)) B *
        Ideal.ramificationIdxIn p (integralClosure A F) := by
      rw [hfiso2, ← htower, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero hram_FL_ne_zero) hkey
  -- Final: |image| = |inertia F| = ramificationIdxIn p B_F.
  rw [← hrange_f_r, hcard_image, ← hcard_inertia_F]

set_option linter.unusedSectionVars false in
include K L in
/-- **Inertia-vs-restriction set equality.** Let `F` be a Galois intermediate field of `L/K`,
`q := AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)`, and `B_F := integralClosure A F`.
Then the image of the inertia group of `P` in `Gal(L/K)` under `q` equals the inertia group
of `P_F := P.under B_F` in `Gal(F/K)`.

This combines the forward inclusion `inertia_map_restrictNormalHom_le` with the cardinality
matching `inertia_map_restrictNormalHom_card_eq`. -/
theorem IntermediateField.inertia_map_restrictNormalHom
    [IsFractionRing A K] [FiniteDimensional K L] [IsDedekindDomain A]
    [Algebra.IsSeparable K L] [IsDedekindDomain B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [IsGaloisGroup Gal(L/K) A B] [P.IsMaximal]
    [Ring.HasFiniteQuotients A] (hp : p ≠ ⊥) :
    letI := integralClosure.algebra_intermediateField A L F B
    Subgroup.map (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K))
        (P.inertia Gal(L/K)) =
      (P.under (integralClosure A F)).inertia Gal(F/K) := by
  haveI : FiniteDimensional K F := FiniteDimensional.left K F L
  haveI : Finite Gal(F/K) := AlgEquiv.fintype K F |>.finite
  exact Subgroup.eq_of_le_of_card_ge
    (IntermediateField.inertia_map_restrictNormalHom_le (A := A) (B := B) (P := P) (F := F))
    ((IntermediateField.inertia_map_restrictNormalHom_card_eq
      (A := A) (B := B) (P := P) (F := F) (hp := hp)).ge)

end inertia_map_restrictNormalHom
