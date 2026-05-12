/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Relative
public import Mathlib.NumberTheory.RamificationInertia.TotallyRamified
public import Mathlib.Data.Nat.MaxPowDiv

/-!
# Total ramification in relative cyclotomic extensions over `ℚ`

Let `Kn = ℚ(ζ_n)` and `Km = ℚ(ζ_m)` with `m = Nat.divMaxPow n p` (the prime-to-`p` part of `n`),
so that `n = p ^ (padicValNat p n) * m` and `p ∤ m`. Then for any prime `P` of `𝓞 Km` lying over
`p`, the prime `P` is totally ramified in `𝓞 Kn` (in the sense of
`Ideal.IsTotallyRamifiedIn`).

This is the relative version of the classical absolute fact (in `Cyclotomic.Ideal`) that the
ramification index of `p` in `ℚ(ζ_n)` is `p ^ k (p - 1) = φ(p ^ (k + 1))` (where
`n = p ^ (k + 1) m`, `p ∤ m`), combined with the fact that `p` is unramified in `Km` (since
`p ∤ m`), and the multiplicativity of ramification in a tower.

## Main result

* `IsCyclotomicExtension.Rat.relative_isTotallyRamifiedIn`: for `m = Nat.divMaxPow n p` with
  `p ∣ n`, every prime of `𝓞 Km` lying over `p` is totally ramified in `𝓞 Kn`.
-/

public section

namespace IsCyclotomicExtension.Rat

open NumberField Ideal

variable {n : ℕ} (p : ℕ) [hp : Fact p.Prime] [NeZero n]
variable (Km Kn : Type*) [Field Km] [NumberField Km] [Field Kn] [NumberField Kn]
variable [IsCyclotomicExtension {Nat.divMaxPow n p} ℚ Km]
variable [IsCyclotomicExtension {n} ℚ Kn]
variable [Algebra Km Kn] [IsScalarTower ℚ Km Kn]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

omit hp in
private lemma divMaxPow_ne_zero : Nat.divMaxPow n p ≠ 0 := by
  intro h
  have hmul := Nat.divMaxPow_mul_pow_padicValNat p n
  rw [h, zero_mul] at hmul
  exact (NeZero.ne n) hmul.symm

omit [IsScalarTower ℚ Km Kn] in
/-- **Total ramification in a relative cyclotomic extension.** Let `Km = ℚ(ζ_m)` where
`m = Nat.divMaxPow n p` (the prime-to-`p` part of `n`), and `Kn = ℚ(ζ_n)`. If `p ∣ n`, then for
every prime `P` of `𝓞 Km` lying over `(p)`, `P` is totally ramified in `𝓞 Kn`. -/
theorem relative_isTotallyRamifiedIn
    (hpn : p ∣ n) (P : Ideal (𝓞 Km)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P.IsTotallyRamifiedIn (𝓞 Kn) := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hn0 : n ≠ 0 := NeZero.ne n
  have hk1_pos : 0 < padicValNat p n := one_le_padicValNat_of_dvd hn0 hpn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk1_pos.ne'
  have hm_ndvd : ¬ p ∣ Nat.divMaxPow n p := Nat.not_dvd_divMaxPow hp1 hn0
  have hm_ne : Nat.divMaxPow n p ≠ 0 := divMaxPow_ne_zero p (n := n)
  haveI : NeZero (Nat.divMaxPow n p) := ⟨hm_ne⟩
  have hmn : Nat.divMaxPow n p ∣ n :=
    ⟨p ^ padicValNat p n, (Nat.divMaxPow_mul_pow_padicValNat p n).symm⟩
  -- n = p^(k+1) * m where m = divMaxPow n p.
  have hn_eq : n = p ^ (k + 1) * Nat.divMaxPow n p := by
    conv_lhs => rw [← Nat.divMaxPow_mul_pow_padicValNat p n]
    rw [mul_comm, hk]
  -- Compute the relative finrank via Phase B's relative_finrank.
  have hpcop : Nat.Coprime (p ^ padicValNat p n) (Nat.divMaxPow n p) :=
    Nat.Coprime.pow_left _ (hp.out.coprime_iff_not_dvd.mpr hm_ndvd)
  have hfr_phi : Module.finrank Km Kn * Nat.totient (Nat.divMaxPow n p) = Nat.totient n :=
    relative_finrank Km Kn hmn
  have htot : Nat.totient n =
      p ^ k * (p - 1) * Nat.totient (Nat.divMaxPow n p) := by
    conv_lhs => rw [hn_eq]
    rw [Nat.totient_mul (by simpa [hk] using hpcop), Nat.totient_prime_pow_succ hp.out]
  have hφm_pos : 0 < Nat.totient (Nat.divMaxPow n p) :=
    Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm_ne)
  have hfr_eq : Module.finrank Km Kn = p ^ k * (p - 1) := by
    have := hfr_phi
    rw [htot] at this
    exact Nat.eq_of_mul_eq_mul_right hφm_pos this
  -- Setup non-bot ideals.
  have hp_ne : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have hPbot : P ≠ ⊥ := by
    intro hbot
    apply hp_ne
    have hover := hP₂.over
    rw [hbot] at hover
    -- hover : 𝒑 = comap _ ⊥. Composed with comap_bot_of_injective:
    rw [Ideal.under_def,
      Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 Km))] at hover
    exact hover
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPbot hP₁
  -- Pick a prime Q of 𝓞 Kn lying over P.
  obtain ⟨Q, hQ_max, hQo_P⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P (S := 𝓞 Kn)
  haveI hQp : Q.IsPrime := hQ_max.isPrime
  haveI : Q.LiesOver P := hQo_P
  haveI : Q.LiesOver 𝒑 := Ideal.LiesOver.trans Q P 𝒑
  -- Absolute ramificationIdx at Kn level: e(Q | 𝒑) = p^k (p-1).
  have hQ_eK : ramificationIdx 𝒑 Q = p ^ k * (p - 1) :=
    ramificationIdx_eq (n := n) (m := Nat.divMaxPow n p) (p := p) (k := k) Kn Q hn_eq hm_ndvd
  -- Absolute ramificationIdx at Km level: e(P|𝒑) = 1 since p ∤ m.
  have hP_eK : ramificationIdx 𝒑 P = 1 :=
    ramificationIdx_eq_of_not_dvd (p := p) (K := Km) P hm_ndvd
  -- Tower law for ramification (ℤ → 𝓞 Km → 𝓞 Kn).
  have hinjZKn : Function.Injective (algebraMap ℤ (𝓞 Kn)) :=
    FaithfulSMul.algebraMap_injective ℤ (𝓞 Kn)
  have hinjKmKn : Function.Injective (algebraMap (𝓞 Km) (𝓞 Kn)) :=
    FaithfulSMul.algebraMap_injective (𝓞 Km) (𝓞 Kn)
  have hPT_ne : Ideal.map (algebraMap (𝓞 Km) (𝓞 Kn)) P ≠ ⊥ :=
    fun h => hPbot ((Ideal.map_eq_bot_iff_of_injective hinjKmKn).mp h)
  have hpT_ne : Ideal.map (algebraMap ℤ (𝓞 Kn)) 𝒑 ≠ ⊥ :=
    fun h => hp_ne ((Ideal.map_eq_bot_iff_of_injective hinjZKn).mp h)
  have hPKn_le_Q : Ideal.map (algebraMap (𝓞 Km) (𝓞 Kn)) P ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (‹Q.LiesOver P›).over
  -- ramificationIdx_algebra_tower for the tower ℤ → 𝓞 Km → 𝓞 Kn.
  have h_e_tower : ramificationIdx 𝒑 Q =
      ramificationIdx 𝒑 P * ramificationIdx P Q :=
    ramificationIdx_algebra_tower (R := ℤ) (S := 𝓞 Km) (T := 𝓞 Kn)
      (p := 𝒑) (P := P) (Q := Q) hPT_ne hpT_ne hPKn_le_Q
  -- Combine: e(Q|P) = p^k * (p-1) = finrank Km Kn = finrank (𝓞 Km) (𝓞 Kn).
  have h_eQP : ramificationIdx P Q = p ^ k * (p - 1) := by
    have := h_e_tower
    rw [hQ_eK, hP_eK, one_mul] at this
    exact this.symm
  have h_eQP_finrank : ramificationIdx P Q = Module.finrank (𝓞 Km) (𝓞 Kn) := by
    have hbridge : Module.finrank Km Kn = Module.finrank (𝓞 Km) (𝓞 Kn) :=
      Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 Km) Km (𝓞 Kn) Kn
    rw [h_eQP, ← hfr_eq, hbridge]
  -- Provide NoZeroSMulDivisors instance (𝓞 Km acts on 𝓞 Kn via injective algebraMap, domain).
  haveI : NoZeroSMulDivisors (𝓞 Km) (𝓞 Kn) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Or.inl (hinjKmKn (by simpa using h1))
    · exact Or.inr h2
  exact isTotallyRamifiedIn_of_ramificationIdx_eq_finrank
    (R := 𝓞 Km) (S := 𝓞 Kn) Km Kn hPbot Q h_eQP_finrank

end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

open NumberField Ideal

variable {m : ℕ} [NeZero m] (q : ℕ) [hq : Fact q.Prime]
variable (Km' : Type*) [Field Km'] [NumberField Km'] [IsCyclotomicExtension {m} ℚ Km']

local notation3 "Q0" => (Ideal.span {(q : ℤ)})

/-- **Unramifiedness at `(p)` of an intermediate field of a tame cyclotomic field.**

If `F_tame ⊆ Km = ℚ(ζₘ)` with `p ∤ m`, then `(p)` is unramified in `𝓞 F_tame`: every prime
`𝔭` of `𝓞 F_tame` lying over `(p)` has ramification index 1. This is the F_tame-level part
of the discharge of `hF_tame_ramified` (DZCP witness 5); it is then tower-composed with the
relative total-ramification fact for `F/F_tame` to conclude. -/
theorem F_tame_unramified_at_p
    (hqm : ¬ q ∣ m)
    (F_tame : Type*) [Field F_tame] [NumberField F_tame]
    [Algebra F_tame Km'] [Algebra ℚ F_tame] [IsScalarTower ℚ F_tame Km']
    (𝔭 : Ideal (𝓞 F_tame)) [h𝔭p : 𝔭.IsPrime]
    [h𝔭o : 𝔭.LiesOver Q0] :
    ramificationIdx Q0 𝔭 = 1 := by
  -- Q0 ≠ ⊥, and 𝔭 ≠ ⊥ via LiesOver.
  have hq_ne : Q0 ≠ ⊥ := by simpa using hq.out.ne_zero
  have h𝔭bot : 𝔭 ≠ ⊥ := by
    intro hbot
    apply hq_ne
    have hover := h𝔭o.over
    rw [hbot, Ideal.under_def,
      Ideal.comap_bot_of_injective _
        (FaithfulSMul.algebraMap_injective ℤ (𝓞 F_tame))] at hover
    exact hover
  haveI : 𝔭.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔭bot h𝔭p
  -- Pick a prime 𝔓 of 𝓞 Km' lying over 𝔭.
  obtain ⟨𝔓, h𝔓_max, h𝔓o_𝔭⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral 𝔭 (S := 𝓞 Km')
  haveI h𝔓p : 𝔓.IsPrime := h𝔓_max.isPrime
  haveI : 𝔓.LiesOver 𝔭 := h𝔓o_𝔭
  haveI : 𝔓.LiesOver Q0 := Ideal.LiesOver.trans 𝔓 𝔭 Q0
  -- IsScalarTower ℤ (𝓞 F_tame) (𝓞 Km'): both algebraMaps factor through ℤ-cast uniqueness.
  haveI hST : IsScalarTower ℤ (𝓞 F_tame) (𝓞 Km') := by
    refine IsScalarTower.of_algebraMap_eq fun z => ?_
    exact RingHom.congr_fun
      (RingHom.ext_int (algebraMap ℤ (𝓞 Km'))
        ((algebraMap (𝓞 F_tame) (𝓞 Km')).comp (algebraMap ℤ (𝓞 F_tame)))) z
  -- e(𝔓|Q0) = 1 (since q ∤ m at Km' level).
  have h𝔓_e : ramificationIdx Q0 𝔓 = 1 :=
    ramificationIdx_eq_of_not_dvd (p := q) (K := Km') (m := m) 𝔓 hqm
  -- Tower: e(𝔓|Q0) = e(𝔭|Q0) * e(𝔓|𝔭).
  have h_tower : ramificationIdx Q0 𝔓 =
      ramificationIdx Q0 𝔭 * ramificationIdx 𝔭 𝔓 :=
    ramificationIdx_algebra_tower' (R := ℤ) (S := 𝓞 F_tame) (T := 𝓞 Km') Q0 𝔭 𝔓
  rw [h𝔓_e] at h_tower
  -- From 1 = a * b in ℕ, a = 1.
  exact (Nat.eq_one_of_mul_eq_one_right h_tower.symm)

end IsCyclotomicExtension.Rat

end
