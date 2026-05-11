/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Relative cyclotomic extensions over `ℚ`

Let `Km` and `Kn` be `ℚ`-cyclotomic extensions of order `m` and `n`, respectively, with `m ∣ n`
and an algebra structure `Algebra Km Kn` (compatible with the `ℚ`-structure via the canonical
`IsScalarTower ℚ Km Kn` instance from `Mathlib.Algebra.Module.Rat`). We deduce that `Kn / Km`
is itself a cyclotomic extension of order `n`, with corresponding Galois-theoretic
consequences.

## Main results

* `IsCyclotomicExtension.Rat.relative`: `IsCyclotomicExtension {n} Km Kn`.
* `IsCyclotomicExtension.Rat.relative_finrank`:
  `Module.finrank Km Kn * Nat.totient m = Nat.totient n`.
* `IsCyclotomicExtension.Rat.relative_isGalois`: `IsGalois Km Kn`.
* `IsCyclotomicExtension.Rat.relative_isAbelianGalois`: `IsAbelianGalois Km Kn`.
* `IsCyclotomicExtension.Rat.relative_galEquivZMod_quotient`:
  `Gal(Kn/Km) ≃* (ZMod.unitsMap hmn).ker`.
-/

open Algebra

@[expose] public section

namespace IsCyclotomicExtension.Rat

open NumberField IsCyclotomicExtension

variable {m n : ℕ} [NeZero n]
variable (Km Kn : Type*) [Field Km] [NumberField Km] [Field Kn] [NumberField Kn]
variable [IsCyclotomicExtension {m} ℚ Km] [IsCyclotomicExtension {n} ℚ Kn]
variable [Algebra Km Kn]

omit [IsCyclotomicExtension {m} ℚ Km] in
/-- If `Km` and `Kn` are `ℚ`-cyclotomic extensions of order `m` and `n` with `m ∣ n` and
`Algebra Km Kn`, then `Kn / Km` is a cyclotomic extension of order `n`.

(The hypothesis `[IsCyclotomicExtension {m} ℚ Km]` is not strictly required for this theorem,
but it is included in the section variables and used by the other theorems in this file.) -/
theorem relative (hmn : m ∣ n) : IsCyclotomicExtension {n} Km Kn := by
  have hne_n : n ≠ 0 := NeZero.ne n
  have hne_m : m ≠ 0 := fun h => hne_n (eq_zero_of_zero_dvd (h ▸ hmn))
  haveI : NeZero m := ⟨hne_m⟩
  refine (IsCyclotomicExtension.iff_singleton n Km Kn).mpr ⟨?_, ?_⟩
  · obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) (A := ℚ)
      (B := Kn) (Set.mem_singleton _) hne_n
    exact ⟨ζ, hζ⟩
  · intro x
    have hQ_top : Algebra.adjoin ℚ {b : Kn | b ^ n = 1} = ⊤ := by
      have h := (IsCyclotomicExtension.iff_singleton n ℚ Kn).mp ‹_›
      rw [Algebra.eq_top_iff]
      intro y
      exact h.2 y
    have hrestrict :
        (Algebra.adjoin Km {b : Kn | b ^ n = 1}).restrictScalars ℚ
          = (IsScalarTower.toAlgHom ℚ Km Kn).range ⊔ Algebra.adjoin ℚ {b : Kn | b ^ n = 1} :=
      Subalgebra.restrictScalars_adjoin ℚ
    have htop : (Algebra.adjoin Km {b : Kn | b ^ n = 1}).restrictScalars ℚ = ⊤ := by
      rw [hrestrict, hQ_top]; exact sup_top_eq _
    have : x ∈ (Algebra.adjoin Km {b : Kn | b ^ n = 1}).restrictScalars ℚ := htop ▸ Algebra.mem_top
    exact this

theorem relative_finrank (hmn : m ∣ n) :
    Module.finrank Km Kn * Nat.totient m = Nat.totient n := by
  have hne_m : m ≠ 0 := fun h => (NeZero.ne n) (eq_zero_of_zero_dvd (h ▸ hmn))
  haveI : NeZero m := ⟨hne_m⟩
  haveI : IsCyclotomicExtension {n} Km Kn := relative Km Kn hmn
  haveI : FiniteDimensional ℚ Km :=
    IsCyclotomicExtension.finiteDimensional {m} ℚ Km
  haveI : FiniteDimensional Km Kn :=
    IsCyclotomicExtension.finiteDimensional {n} Km Kn
  have hKm : Module.finrank ℚ Km = Nat.totient m :=
    IsCyclotomicExtension.finrank Km (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  have hKn : Module.finrank ℚ Kn = Nat.totient n :=
    IsCyclotomicExtension.finrank Kn (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))
  have htower : Module.finrank ℚ Km * Module.finrank Km Kn = Module.finrank ℚ Kn :=
    Module.finrank_mul_finrank ℚ Km Kn
  rw [hKm, hKn] at htower
  linarith [htower]

omit [IsCyclotomicExtension {m} ℚ Km] in
theorem relative_isGalois (hmn : m ∣ n) : IsGalois Km Kn :=
  haveI : IsCyclotomicExtension {n} Km Kn := relative Km Kn hmn
  IsCyclotomicExtension.isGalois {n} Km Kn

omit [IsCyclotomicExtension {m} ℚ Km] in
theorem relative_isAbelianGalois (hmn : m ∣ n) : IsAbelianGalois Km Kn :=
  haveI : IsCyclotomicExtension {n} Km Kn := relative Km Kn hmn
  IsCyclotomicExtension.isAbelianGalois {n} Km Kn

/-- `Gal(Kn/Km)` is isomorphic to the kernel of the natural map `(ZMod n)ˣ →* (ZMod m)ˣ`.

The forward map sends `σ : Kn ≃ₐ[Km] Kn` to `(galEquivZMod n Kn) (σ.restrictScalars ℚ)`, which
lies in the kernel of `ZMod.unitsMap hmn` because `σ` fixes `Km` pointwise, hence
its restriction to the intermediate field `(algebraMap Km Kn).range` is the identity. -/
noncomputable def relative_galEquivZMod_quotient (hmn : m ∣ n) :
    Gal(Kn/Km) ≃* (ZMod.unitsMap hmn).ker := by
  have hne_m : m ≠ 0 := fun h => (NeZero.ne n) (eq_zero_of_zero_dvd (h ▸ hmn))
  haveI : NeZero m := ⟨hne_m⟩
  haveI : IsGalois ℚ Km := IsCyclotomicExtension.isGalois {m} ℚ Km
  haveI : IsGalois ℚ Kn := IsCyclotomicExtension.isGalois {n} ℚ Kn
  let f : Km →ₐ[ℚ] Kn := IsScalarTower.toAlgHom ℚ Km Kn
  let Km' : IntermediateField ℚ Kn := f.fieldRange
  haveI : IsCyclotomicExtension {m} ℚ Km' :=
    IsCyclotomicExtension.equiv {m} ℚ Km (AlgEquiv.ofInjectiveField f)
  haveI : NumberField Km' := IsCyclotomicExtension.numberField {m} ℚ Km'
  haveI : IsGalois ℚ Km' := IsCyclotomicExtension.isGalois {m} ℚ Km'
  haveI : Normal ℚ Km' := IsGalois.to_normal
  let φn : Gal(Kn/ℚ) ≃* (ZMod n)ˣ := galEquivZMod n Kn
  let φm : Gal(Km'/ℚ) ≃* (ZMod m)ˣ := galEquivZMod m Km'
  have hsq : ∀ σ : Gal(Kn/ℚ),
      φm (AlgEquiv.restrictNormalHom Km' σ) = ZMod.unitsMap hmn (φn σ) :=
    fun σ => galEquivZMod_restrictNormal_apply n Kn (F := Km') hmn σ
  -- key fact A: for σ : Kn ≃ₐ[Km] Kn, the restriction `σ.restrictScalars ℚ` fixes Km' pointwise.
  have hKm_fix : ∀ (σ : Gal(Kn/Km)) (y : Km'), (σ.restrictScalars ℚ) (y : Kn) = (y : Kn) := by
    rintro σ ⟨_, x, rfl⟩
    show σ (algebraMap Km Kn x) = algebraMap Km Kn x
    exact σ.commutes x
  -- key fact B: hence restrictNormalHom Km' (σ.restrictScalars ℚ) = 1.
  have hKm_fix_hom : ∀ σ : Gal(Kn/Km),
      AlgEquiv.restrictNormalHom Km' (σ.restrictScalars ℚ) = 1 := by
    intro σ
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have hfix := hKm_fix σ y
    have hcomm := AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) Km' y
    have : ((AlgEquiv.restrictNormalHom Km' (σ.restrictScalars ℚ)) y : Kn) =
        ((σ.restrictScalars ℚ) (y : Kn) : Kn) := by
      show (algebraMap Km' Kn) (((σ.restrictScalars ℚ).restrictNormal Km') y) =
          (σ.restrictScalars ℚ) (y : Kn)
      exact hcomm
    rw [this, hfix]
    rfl
  -- Forward MonoidHom Gal(Kn/Km) →* (ZMod.unitsMap hmn).ker.
  let F : Gal(Kn/Km) →* (ZMod.unitsMap hmn).ker :=
  { toFun := fun σ => ⟨φn (σ.restrictScalars ℚ), by
      rw [MonoidHom.mem_ker, ← hsq (σ.restrictScalars ℚ), hKm_fix_hom σ, map_one]⟩,
    map_one' := by
      apply Subtype.ext
      show φn ((1 : Gal(Kn/Km)).restrictScalars ℚ) = 1
      rw [show ((1 : Gal(Kn/Km)).restrictScalars ℚ : Kn ≃ₐ[ℚ] Kn) = 1 from rfl, map_one]
    map_mul' := fun σ τ => by
      apply Subtype.ext
      show φn ((σ * τ).restrictScalars ℚ)
        = (φn (σ.restrictScalars ℚ)) * (φn (τ.restrictScalars ℚ))
      rw [show ((σ * τ).restrictScalars ℚ : Kn ≃ₐ[ℚ] Kn) =
            σ.restrictScalars ℚ * τ.restrictScalars ℚ from rfl, map_mul] }
  -- Inverse map ker → Gal(Kn/Km) constructed below.
  -- Given u in the kernel, set τ := φn.symm u : Gal(Kn/ℚ). Show τ fixes Km' pointwise,
  -- which gives `τ (algebraMap Km Kn x) = algebraMap Km Kn x` for all x : Km, i.e. τ
  -- descends to a Km-algebra automorphism.
  have hInv_fix : ∀ (u : (ZMod n)ˣ) (_ : u ∈ (ZMod.unitsMap hmn).ker) (x : Km),
      (φn.symm u) (algebraMap Km Kn x) = algebraMap Km Kn x := by
    intro u hu x
    have hres : AlgEquiv.restrictNormalHom Km' (φn.symm u) = 1 := by
      apply φm.injective
      rw [map_one, hsq (φn.symm u), MulEquiv.apply_symm_apply]
      rwa [MonoidHom.mem_ker] at hu
    have hx_mem : f x ∈ Km' := ⟨x, rfl⟩
    have h := AlgEquiv.ext_iff.mp hres ⟨f x, hx_mem⟩
    simp only [AlgEquiv.one_apply] at h
    have hsub : ((AlgEquiv.restrictNormalHom Km' (φn.symm u)) ⟨f x, hx_mem⟩ : Kn) = f x :=
      congrArg Subtype.val h
    have hcomm := AlgEquiv.restrictNormal_commutes (φn.symm u) Km' ⟨f x, hx_mem⟩
    -- hcomm: algebraMap Km' Kn ((φn.symm u).restrictNormal Km' ⟨f x, _⟩)
    --        = (φn.symm u) (algebraMap Km' Kn ⟨f x, _⟩)
    have halg : (algebraMap Km' Kn) (⟨f x, hx_mem⟩ : Km') = f x := rfl
    rw [halg] at hcomm
    -- hsub gives: algebraMap Km' Kn ((φn.symm u).restrictNormal Km' ⟨f x, _⟩) = f x
    show (φn.symm u) (f x) = f x
    show (φn.symm u) (algebraMap Km Kn x) = algebraMap Km Kn x
    have : (φn.symm u) (f x) = f x := by
      rw [← hcomm]; exact hsub
    exact this
  let G : (ZMod.unitsMap hmn).ker → Gal(Kn/Km) := fun u =>
    { toRingEquiv := (φn.symm u.1).toRingEquiv,
      commutes' := hInv_fix u.1 u.2 }
  refine MonoidHom.toMulEquiv F
    { toFun := G, map_one' := ?_, map_mul' := ?_ } ?_ ?_
  · apply AlgEquiv.ext
    intro x
    show (φn.symm (1 : (ZMod.unitsMap hmn).ker).1) x = x
    rw [show ((1 : (ZMod.unitsMap hmn).ker).1 : (ZMod n)ˣ) = 1 from rfl, map_one]
    rfl
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    apply AlgEquiv.ext
    intro x
    show (φn.symm (u * v)) x = ((φn.symm u) * (φn.symm v)) x
    rw [map_mul]
  · ext σ x
    show (φn.symm (φn (σ.restrictScalars ℚ))) x = σ x
    rw [MulEquiv.symm_apply_apply]
    rfl
  · ext ⟨u, hu⟩
    have heq : (F (G ⟨u, hu⟩) : (ZMod n)ˣ) = u := by
      show φn ((G ⟨u, hu⟩).restrictScalars ℚ) = u
      show φn (φn.symm u) = u
      exact MulEquiv.apply_symm_apply _ _
    show ((F (G ⟨u, hu⟩) : (ZMod n)ˣ) : ZMod n) = ((u : (ZMod n)ˣ) : ZMod n)
    rw [heq]

end IsCyclotomicExtension.Rat
