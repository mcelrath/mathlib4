/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Cyclotomic inertia identification

Let `Kn = ℚ(ζₙ)` be a cyclotomic extension of `ℚ` of level `n`, let `p` be a prime, write
`m = Nat.divMaxPow n p` for the `p`-free part of `n`, and let `Km = ℚ(ζₘ)`. The intermediate
field `Km ⊆ Kn` is the maximal subextension unramified at primes above `p`, and
`Gal(Kn/Km)` is the inertia subgroup at any such prime.

## Main results

* `IsCyclotomicExtension.Rat.galEquivZMod_mapSubgroup_inertia`:
  the image of the inertia subgroup `P.inertia Gal(Kn/ℚ)` under `galEquivZMod n Kn`
  is the kernel of the natural map `(ZMod n)ˣ → (ZMod m)ˣ`.
-/

open NumberField

namespace Nat

/-- `Nat.divMaxPow n p` (the `p`-free part of `n`) divides `n`. -/
theorem divMaxPow_dvd (n p : ℕ) : Nat.divMaxPow n p ∣ n :=
  ⟨p ^ padicValNat p n, (Nat.divMaxPow_mul_pow_padicValNat p n).symm⟩

end Nat

namespace IsCyclotomicExtension.Rat

open IsCyclotomicExtension

variable (n : ℕ) [NeZero n] (Kn : Type*) [Field Kn] [NumberField Kn]
  [IsCyclotomicExtension {n} ℚ Kn]
variable (p : ℕ) [hp : Fact p.Prime]
variable (P : Ideal (𝓞 Kn)) [hPmax : P.IsMaximal]
  [hPlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]

/-- **Cyclotomic inertia, in terms of `(ZMod n)ˣ`.**

The image of the inertia group `P.inertia Gal(Kn/ℚ)` under the canonical isomorphism
`galEquivZMod n Kn : Gal(Kn/ℚ) ≃* (ZMod n)ˣ` equals the kernel of the projection
`ZMod.unitsMap (Nat.divMaxPow_dvd n p) : (ZMod n)ˣ → (ZMod m)ˣ`,
where `m = Nat.divMaxPow n p` is the `p`-free part of `n`.

**Proof.** `⊆` follows from the action of inertia on a primitive `m`-th root of unity
modulo `P` (via `IsPrimitiveRoot.idealQuotient_mk` and `pow_inj_mod`). The reverse
inclusion follows by cardinality:
`|ker| = φ(n)/φ(m) = φ(p^v) = ramificationIdxIn p Kn = |inertia|`. -/
theorem galEquivZMod_mapSubgroup_inertia :
    (galEquivZMod n Kn).mapSubgroup (P.inertia Gal(Kn/ℚ)) =
      (ZMod.unitsMap (Nat.divMaxPow_dvd n p)).ker := by
  classical
  haveI hGalKn : IsGalois ℚ Kn := IsCyclotomicExtension.isGalois {n} ℚ Kn
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  let m := Nat.divMaxPow n p
  let v := padicValNat p n
  have hm_dvd : m ∣ n := Nat.divMaxPow_dvd n p
  have hm_ndvd : ¬ p ∣ m := Nat.not_dvd_divMaxPow hp.out.one_lt (NeZero.ne n)
  have hn_eq : n = p ^ v * m := by
    rw [mul_comm]; exact (Nat.divMaxPow_mul_pow_padicValNat p n).symm
  haveI hm_ne : NeZero m := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) hm_dvd⟩
  -- Primitive n-th root of unity ζ in 𝓞 Kn
  let hζ := IsCyclotomicExtension.zeta_spec n ℚ Kn
  have hζn_prim : IsPrimitiveRoot hζ.toInteger n := hζ.toInteger_isPrimitiveRoot
  -- ζm = ζn^(p^v) is a primitive m-th root of unity
  let ζm := hζ.toInteger ^ (p ^ v)
  have hζm_prim : IsPrimitiveRoot ζm m := hζn_prim.pow (NeZero.pos n) hn_eq
  have hζm_pow_n : ζm ^ n = 1 := by
    have hζm_pow_m : ζm ^ m = 1 := hζm_prim.pow_eq_one
    calc ζm ^ n = ζm ^ (p ^ v * m) := by rw [← hn_eq]
      _ = (ζm ^ m) ^ (p ^ v) := by rw [mul_comm (p ^ v) m, pow_mul]
      _ = 1 ^ (p ^ v) := by rw [hζm_pow_m]
      _ = 1 := one_pow _
  -- Primitivity of ζm modulo P
  have habsNorm_ne_one : Ideal.absNorm P ≠ 1 :=
    Ideal.absNorm_eq_one_iff.not.mpr hPmax.ne_top
  have habsNorm_cop_m : (Ideal.absNorm P).Coprime m := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg' P hp.out]
    exact (hp.out.coprime_iff_not_dvd.mpr hm_ndvd).pow_left _
  have hζm_prim_mod : IsPrimitiveRoot (Ideal.Quotient.mk P ζm) m :=
    hζm_prim.idealQuotient_mk habsNorm_ne_one habsNorm_cop_m
  -- Apply Subgroup.eq_of_le_of_card_ge: need ⊆ and card inequality
  apply Subgroup.eq_of_le_of_card_ge
  · -- ⊆: image of inertia ≤ ker(unitsMap)
    intro u hu
    rw [MulEquiv.mapSubgroup_apply, Subgroup.mem_map] at hu
    obtain ⟨σ, hσ_inertia, rfl⟩ := hu
    rw [MonoidHom.mem_ker]
    -- σ acts trivially mod P on ζm (by inertia), so galEquivZMod(σ) ≡ 1 mod m
    let k := (galEquivZMod n Kn σ).val.val
    have hsmul : σ • ζm = ζm ^ k :=
      galEquivZMod_smul_of_pow_eq n Kn σ hζm_pow_n
    have hmem_P : σ • ζm - ζm ∈ P := AddSubgroup.mem_inertia.mp hσ_inertia ζm
    have hmap_eq : (Ideal.Quotient.mk P ζm) ^ k = (Ideal.Quotient.mk P ζm) ^ 1 := by
      rw [pow_one, ← map_pow, ← hsmul]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hmem_P
    -- k ≡ 1 (mod m) by primitivity
    have hk_mod : k % m = 1 % m := by
      have h := (hζm_prim_mod.isOfFinOrder (NeZero.ne m)).pow_inj_mod.mp hmap_eq
      rwa [← hζm_prim_mod.eq_orderOf] at h
    -- Conclude unitsMap = 1
    rw [Units.ext_iff, ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val]
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' k 1 m).mpr hk_mod
  · -- card inequality: |ker(unitsMap)| ≤ |image of inertia|
    -- Both equal ramificationIdxIn p Kn
    rw [Subgroup.card_mapSubgroup]
    haveI hGalKnQ : IsGaloisGroup Gal(Kn/ℚ) ℚ Kn := IsGaloisGroup.of_isGalois ℚ Kn
    haveI hGalKnZ : IsGaloisGroup Gal(Kn/ℚ) ℤ (𝓞 Kn) := inferInstance
    have hp_ideal_ne_bot : p_ideal ≠ ⊥ := by
      simp only [p_ideal, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    have hP_ne_bot : P ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField hPmax (RingOfIntegers.not_isField Kn)
    letI hFieldZ : Field (ℤ ⧸ p_ideal) := Ideal.Quotient.field _
    letI hFieldKn : Field (𝓞 Kn ⧸ P) := Ideal.Quotient.field _
    haveI h_isSep : Algebra.IsSeparable (ℤ ⧸ p_ideal) (𝓞 Kn ⧸ P) := by
      haveI : Finite (𝓞 Kn ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP_ne_bot
      haveI : Finite (ℤ ⧸ p_ideal) := inferInstance
      haveI : PerfectField (ℤ ⧸ p_ideal) := inferInstance
      haveI : Module.Finite (ℤ ⧸ p_ideal) (𝓞 Kn ⧸ P) :=
        (Module.finite_iff_finite (R := ℤ ⧸ p_ideal)).mpr ‹_›
      haveI : Algebra.IsAlgebraic (ℤ ⧸ p_ideal) (𝓞 Kn ⧸ P) :=
        Algebra.IsAlgebraic.of_finite _ _
      exact inferInstance
    have hcard_inertia : Nat.card (P.inertia Gal(Kn/ℚ)) =
        Ideal.ramificationIdxIn p_ideal (𝓞 Kn) :=
      Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(Kn/ℚ)) p_ideal hp_ideal_ne_bot P
    -- Compute cardinality of kernel
    have hcard_ker : Nat.card (ZMod.unitsMap hm_dvd).ker =
        Ideal.ramificationIdxIn p_ideal (𝓞 Kn) := by
      have hsurj : Function.Surjective (ZMod.unitsMap hm_dvd) :=
        ZMod.unitsMap_surjective hm_dvd
      have hrange : (ZMod.unitsMap hm_dvd).range = ⊤ :=
        MonoidHom.range_eq_top.mpr hsurj
      have hfirst_iso : Nat.card (ZMod.unitsMap hm_dvd).ker * Nat.totient m = Nat.totient n := by
        have h := (ZMod.unitsMap hm_dvd).ker.card_mul_index
        rw [Subgroup.index_ker, hrange, Subgroup.card_top] at h
        conv at h => rhs; rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
        conv at h => lhs; rhs; rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
        exact h
      have hram_tot : Ideal.ramificationIdxIn p_ideal (𝓞 Kn) * Nat.totient m =
          Nat.totient n := by
        rcases Nat.eq_zero_or_pos v with hv | hv
        · have hn_eq_m : n = m := by
            have : p ^ v = 1 := by rw [hv, pow_zero]
            rw [hn_eq, this, one_mul]
          rw [← hn_eq_m]
          have hram1 : Ideal.ramificationIdxIn p_ideal (𝓞 Kn) = 1 :=
            IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p Kn (hn_eq_m ▸ hm_ndvd)
          simp [hram1]
        · obtain ⟨k', hv_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hv)
          have hn_eq' : n = p ^ (k' + 1) * m := by rw [hn_eq, hv_eq]
          have hram : Ideal.ramificationIdxIn p_ideal (𝓞 Kn) = p ^ k' * (p - 1) :=
            IsCyclotomicExtension.Rat.ramificationIdxIn_eq n Kn hn_eq' hm_ndvd
          have hcop : Nat.Coprime (p ^ (k' + 1)) m :=
            Nat.Coprime.pow_left _ (hp.out.coprime_iff_not_dvd.mpr hm_ndvd)
          rw [hram, hn_eq', Nat.totient_mul hcop, Nat.totient_prime_pow_succ hp.out]
      exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr (NeZero.pos m))
        (hfirst_iso.trans hram_tot.symm)
    linarith [hcard_inertia, hcard_ker]

end IsCyclotomicExtension.Rat
