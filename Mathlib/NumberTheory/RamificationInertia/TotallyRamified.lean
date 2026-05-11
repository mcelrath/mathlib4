/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Totally ramified extensions

We define `Ideal.IsTotallyRamifiedIn p S`: a prime `p` of `R` is *totally ramified* in an
`R`-algebra `S` if there is a unique prime `P` of `S` lying over `p`, the ramification index
`e(P|p)` equals `Module.finrank R S`, and the inertia degree `f(P|p)` equals `1`.

Equivalently, by the fundamental identity `Ideal.sum_ramification_inertia`, under the standard
Dedekind-domain hypotheses it suffices to require existence of a single prime `P` over `p` with
`e(P|p) = finrank R S`; uniqueness and `f(P|p) = 1` then follow.

## Main definitions

* `Ideal.IsTotallyRamifiedIn`: the predicate above.

## Main results

* `Ideal.isTotallyRamifiedIn_iff_exists_ramificationIdx_eq_finrank`: under the standard hypotheses
  (Dedekind, fraction fields, finite module), existence of one prime `P` of `S` over `p` with
  `e(P|p) = finrank R S` is equivalent to total ramification.
* `Ideal.isTotallyRamifiedIn_of_ramificationIdx_eq_finrank`: one-direction wrapper.
-/

public section

namespace Ideal

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- A prime ideal `p` of `R` is **totally ramified** in `S` if there is a unique prime `P` of `S`
lying over `p`, with ramification index equal to `Module.finrank R S` and inertia degree `1`. -/
def IsTotallyRamifiedIn (p : Ideal R) : Prop :=
  ∃! P : Ideal S, ∃ _ : P.IsPrime, ∃ _ : P.LiesOver p,
    ramificationIdx p P = Module.finrank R S ∧ inertiaDeg p P = 1

variable {S}

theorem IsTotallyRamifiedIn.exists {p : Ideal R} (h : p.IsTotallyRamifiedIn S) :
    ∃ P : Ideal S, ∃ _ : P.IsPrime, ∃ _ : P.LiesOver p,
      ramificationIdx p P = Module.finrank R S ∧ inertiaDeg p P = 1 := by
  obtain ⟨P, hP, _⟩ := h
  exact ⟨P, hP⟩

/-- The unique prime over `p` witnessing total ramification. -/
theorem IsTotallyRamifiedIn.unique {p : Ideal R} (h : p.IsTotallyRamifiedIn S)
    {P Q : Ideal S} [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (hP : ramificationIdx p P = Module.finrank R S) (hPf : inertiaDeg p P = 1)
    (hQ : ramificationIdx p Q = Module.finrank R S) (hQf : inertiaDeg p Q = 1) :
    P = Q := by
  obtain ⟨w, _, huniq⟩ := h
  rw [huniq P ⟨‹_›, ‹_›, hP, hPf⟩, ← huniq Q ⟨‹_›, ‹_›, hQ, hQf⟩]

section Dedekind

variable (R) in
/-- Equivalent characterization via the fundamental identity: under Dedekind-domain hypotheses,
`p` is totally ramified in `S` iff there exists a prime `P` of `S` lying over `p` with
ramification index `Module.finrank R S`. The uniqueness and `f(P|p) = 1` then follow from
`Ideal.sum_ramification_inertia`. -/
theorem isTotallyRamifiedIn_iff_exists_ramificationIdx_eq_finrank
    (K L : Type*) [Field K] [Field L] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
    [IsScalarTower R K L] [Module.Finite R S] [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    p.IsTotallyRamifiedIn S ↔
      ∃ P : Ideal S, ∃ _ : P.IsPrime, ∃ _ : P.LiesOver p,
        ramificationIdx p P = Module.finrank R S := by
  classical
  have hfaith : FaithfulSMul R S := FaithfulSMul.of_field_isFractionRing R S K L
  have halg : Algebra.IsAlgebraic R S := Algebra.IsAlgebraic.of_finite R S
  have hfr : Module.finrank K L = Module.finrank R S :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing R K S L
  refine ⟨fun h ↦ ?_, fun ⟨P, hP, hPo, hPe⟩ ↦ ?_⟩
  · obtain ⟨P, hP, hPo, hPe, _⟩ := h.exists
    exact ⟨P, hP, hPo, hPe⟩
  · -- We will use the fundamental identity to force uniqueness and f = 1.
    have hPmem : P ∈ IsDedekindDomain.primesOverFinset p S :=
      (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP, hPo⟩
    have hsum := sum_ramification_inertia S K L (p := p) hp0
    -- e(P|p) * f(P|p) ≤ sum = finrank K L = finrank R S = e(P|p).
    have hpos_e_other : ∀ Q ∈ IsDedekindDomain.primesOverFinset p S,
        0 < ramificationIdx p Q * inertiaDeg p Q := by
      intro Q hQ
      have hQp : Q.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hQ).1
      have hQo : Q.LiesOver p := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hQ).2
      refine Nat.mul_pos ?_ ?_
      · exact Nat.pos_iff_ne_zero.mpr <|
          IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hp0
      · exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg_ne_zero p Q
    have hf_pos : 0 < inertiaDeg p P :=
      Nat.pos_iff_ne_zero.mpr <| inertiaDeg_ne_zero p P
    have hsingle : IsDedekindDomain.primesOverFinset p S = {P} := by
      classical
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hPmem, fun Q hQ ↦ ?_⟩
      by_contra hQne
      have hsplit :
          ∑ Q' ∈ IsDedekindDomain.primesOverFinset p S,
              ramificationIdx p Q' * inertiaDeg p Q' =
            ramificationIdx p P * inertiaDeg p P +
              ∑ Q' ∈ (IsDedekindDomain.primesOverFinset p S).erase P,
                ramificationIdx p Q' * inertiaDeg p Q' :=
        (Finset.add_sum_erase _ _ hPmem).symm
      have hQmem_erase : Q ∈ (IsDedekindDomain.primesOverFinset p S).erase P :=
        Finset.mem_erase.mpr ⟨hQne, hQ⟩
      have herase_pos :
          0 < ∑ Q' ∈ (IsDedekindDomain.primesOverFinset p S).erase P,
                ramificationIdx p Q' * inertiaDeg p Q' :=
        Finset.sum_pos
          (fun Q' hQ' ↦ hpos_e_other Q' (Finset.mem_of_mem_erase hQ'))
          ⟨Q, hQmem_erase⟩
      have hPef : ramificationIdx p P * inertiaDeg p P = Module.finrank R S * inertiaDeg p P := by
        rw [hPe]
      have h_le :
          ramificationIdx p P * inertiaDeg p P < Module.finrank K L := by
        rw [← hsum, hsplit]
        have : ramificationIdx p P * inertiaDeg p P
            ≤ ramificationIdx p P * inertiaDeg p P := le_rfl
        omega
      rw [hPef] at h_le
      have hfrpos : 0 < Module.finrank R S := by
        have hcard_pos : 0 < (IsDedekindDomain.primesOverFinset p S).card :=
          Finset.card_pos.mpr ⟨P, hPmem⟩
        have hle := card_primesOverFinset_le_finrank S (K := K) (L := L) (p := p) hp0
        rw [← hfr]
        exact lt_of_lt_of_le hcard_pos hle
      -- h_le : finrank R S * inertiaDeg p P < finrank K L = finrank R S
      rw [hfr] at h_le
      nlinarith [hf_pos]
    -- With singleton, sum = e(P|p) * f(P|p) = finrank R S, and e(P|p) = finrank R S, so f = 1.
    have hf_one : inertiaDeg p P = 1 := by
      have hef_eq : ramificationIdx p P * inertiaDeg p P = Module.finrank K L := by
        rw [← hsum, hsingle, Finset.sum_singleton]
      rw [hPe, hfr] at hef_eq
      -- hef_eq : finrank R S * inertiaDeg p P = finrank R S
      have hfrpos : 0 < Module.finrank R S := by
        have hcard_pos : 0 < (IsDedekindDomain.primesOverFinset p S).card :=
          Finset.card_pos.mpr ⟨P, hPmem⟩
        have hle := card_primesOverFinset_le_finrank S (K := K) (L := L) (p := p) hp0
        rw [← hfr]
        exact lt_of_lt_of_le hcard_pos hle
      have hone : Module.finrank R S * inertiaDeg p P = Module.finrank R S * 1 := by
        rw [Nat.mul_one]; exact hef_eq
      exact Nat.eq_of_mul_eq_mul_left hfrpos hone
    refine ⟨P, ⟨hP, hPo, hPe, hf_one⟩, ?_⟩
    rintro Q ⟨hQp, hQo, hQe, hQf⟩
    have hQmem : Q ∈ IsDedekindDomain.primesOverFinset p S :=
      (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hQp, hQo⟩
    rw [hsingle, Finset.mem_singleton] at hQmem
    exact hQmem

/-- One-direction wrapper: existence of a prime `P` of `S` over `p` with `e(P|p) = finrank R S`
implies total ramification (under standard Dedekind hypotheses). -/
theorem isTotallyRamifiedIn_of_ramificationIdx_eq_finrank
    (K L : Type*) [Field K] [Field L] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
    [IsScalarTower R K L] [Module.Finite R S] [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥)
    (P : Ideal S) [hP : P.IsPrime] [hPo : P.LiesOver p]
    (hPe : ramificationIdx p P = Module.finrank R S) :
    p.IsTotallyRamifiedIn S :=
  (isTotallyRamifiedIn_iff_exists_ramificationIdx_eq_finrank (S := S) R K L hp0).mpr
    ⟨P, hP, hPo, hPe⟩

end Dedekind

section Tower

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- **Tower inheritance of total ramification.** Let `R → S → T` be a tower of Dedekind domains
with fraction fields `K ⊆ KS ⊆ L`. If a maximal ideal `p` of `R` is totally ramified in `T`,
then for the unique prime `P` of `S` lying over `p`, `P` is totally ramified in `T`.

Proof: let `Q` be the unique prime of `T` over `p`. The tower laws
`ramificationIdx_algebra_tower` and `inertiaDeg_algebra_tower` give
`e(Q|p) = e(P|p) · e(Q|P)` and `f(Q|p) = f(P|p) · f(Q|P)`. From `e(Q|p) = finrank R T`,
`f(Q|p) = 1`, and `finrank R T = finrank R S · finrank S T`, plus the bounds
`e(P|p) · f(P|p) ≤ finrank R S` (from `sum_ramification_inertia` at level `S`) and
`e(Q|P) · f(Q|P) ≤ finrank S T`, equality propagates and forces `e(Q|P) = finrank S T`. -/
theorem IsTotallyRamifiedIn.tower
    (K KS L : Type*) [Field K] [Field KS] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S KS] [IsFractionRing S KS]
    [Algebra T L] [IsFractionRing T L]
    [Algebra K KS] [Algebra R KS] [IsScalarTower R S KS] [IsScalarTower R K KS]
    [Algebra KS L] [Algebra S L] [IsScalarTower S T L] [IsScalarTower S KS L]
    [Algebra K L] [Algebra R L] [IsScalarTower R T L] [IsScalarTower R K L]
    [IsScalarTower K KS L]
    [Module.Finite R S] [Module.Finite S T] [Module.Finite R T]
    [NoZeroSMulDivisors R S] [NoZeroSMulDivisors S T] [NoZeroSMulDivisors R T]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥)
    (h : p.IsTotallyRamifiedIn T) :
    ∀ P : Ideal S, ∀ _ : P.IsPrime, ∀ _ : P.LiesOver p, P.IsTotallyRamifiedIn T := by
  classical
  -- Extract the unique prime Q of T over p.
  obtain ⟨Q, hQp, hQo, hQe, hQf⟩ := h.exists
  -- Standard auxiliary facts.
  have hfrST : Module.finrank KS L = Module.finrank S T :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing S KS T L
  have hfrRS : Module.finrank K KS = Module.finrank R S :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing R K S KS
  have hfrRT : Module.finrank K L = Module.finrank R T :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing R K T L
  -- finrank R T = finrank R S * finrank S T.
  have hfrmul_KL : Module.finrank K L = Module.finrank K KS * Module.finrank KS L :=
    (Module.finrank_mul_finrank K KS L).symm
  have hfrmul : Module.finrank R T = Module.finrank R S * Module.finrank S T := by
    rw [← hfrRT, hfrmul_KL, hfrRS, hfrST]
  -- The unique-prime statement.
  intro P hPp hPo
  -- Let P' = Q.under S. Show P' = P, then show e(Q|P) = finrank S T.
  set P' : Ideal S := Q.under S with hP'_def
  -- P' is prime and lies over p.
  have hP'_under : P'.IsPrime := Ideal.IsPrime.under S Q
  have hP'_liesOver_p : P'.LiesOver p := by
    refine ⟨?_⟩
    have hQRover : Q.LiesOver p := hQo
    -- Q.under R = p, and Q.under R = (Q.under S).under R by transitivity of comap.
    have h1 : Q.under R = p := hQRover.over.symm
    have h2 : Q.under R = (Q.under S).under R := by
      simp only [under_def]
      rw [IsScalarTower.algebraMap_eq R S T, ← Ideal.comap_comap]
    rw [← h1, h2]
  -- Q lies over P'.
  have hQ_liesOver_P' : Q.LiesOver P' := ⟨rfl⟩
  -- maximality of P' (Dedekind ⇒ dim ≤ 1).
  have hP'_ne_bot : P' ≠ ⊥ := by
    intro hbot
    have hp_eq : (P'.under R) = p := hP'_liesOver_p.over.symm
    rw [hbot] at hp_eq
    simp [under_def] at hp_eq
    exact hp0 hp_eq.symm
  letI : P'.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP'_ne_bot hP'_under
  -- maps non-bot.
  -- maps non-bot via injective algebraMap (from FaithfulSMul).
  have hinjRS : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have hinjST : Function.Injective (algebraMap S T) := FaithfulSMul.algebraMap_injective S T
  have hinjRT : Function.Injective (algebraMap R T) := FaithfulSMul.algebraMap_injective R T
  have hP'T_ne : map (algebraMap S T) P' ≠ ⊥ :=
    fun h => hP'_ne_bot ((map_eq_bot_iff_of_injective hinjST).mp h)
  have hpT_ne : map (algebraMap R T) p ≠ ⊥ :=
    fun h => hp0 ((map_eq_bot_iff_of_injective hinjRT).mp h)
  have hP'T_le_Q : map (algebraMap S T) P' ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def Q P'))
  -- e(Q|p) = e(P'|p) * e(Q|P')
  have h_e_tower : ramificationIdx p Q = ramificationIdx p P' * ramificationIdx P' Q :=
    ramificationIdx_algebra_tower hP'T_ne hpT_ne hP'T_le_Q
  -- f(Q|p) = f(P'|p) * f(Q|P')
  have h_f_tower : inertiaDeg p Q = inertiaDeg p P' * inertiaDeg P' Q :=
    inertiaDeg_algebra_tower p P' Q
  -- From hQf : f(Q|p) = 1, both factors equal 1.
  have hmul1 : inertiaDeg p P' * inertiaDeg P' Q = 1 := by rw [← h_f_tower]; exact hQf
  have h_fP' : inertiaDeg p P' = 1 := Nat.eq_one_of_mul_eq_one_right hmul1
  have h_fQP' : inertiaDeg P' Q = 1 := Nat.eq_one_of_mul_eq_one_left hmul1
  -- Bound e(P'|p) ≤ finrank R S via sum_ramification_inertia at S level.
  have hP'_mem : P' ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP'_under, hP'_liesOver_p⟩
  have hsumS := sum_ramification_inertia S K KS (p := p) hp0
  have h_eP'_le : ramificationIdx p P' ≤ Module.finrank R S := by
    have h_term_le :
        ramificationIdx p P' * inertiaDeg p P' ≤
          ∑ I ∈ IsDedekindDomain.primesOverFinset p S,
            ramificationIdx p I * inertiaDeg p I :=
      Finset.single_le_sum (f := fun I => ramificationIdx p I * inertiaDeg p I)
        (fun _ _ => Nat.zero_le _) hP'_mem
    rw [hsumS, hfrRS, h_fP', Nat.mul_one] at h_term_le
    exact h_term_le
  -- Similarly bound e(Q|P') ≤ finrank S KS = finrank S T.
  have hQ_mem : Q ∈ IsDedekindDomain.primesOverFinset P' T :=
    (IsDedekindDomain.mem_primesOverFinset_iff hP'_ne_bot _).mpr ⟨hQp, hQ_liesOver_P'⟩
  have hsumT := sum_ramification_inertia T KS L (p := P') hP'_ne_bot
  have h_eQP'_le : ramificationIdx P' Q ≤ Module.finrank S T := by
    have h_term_le :
        ramificationIdx P' Q * inertiaDeg P' Q ≤
          ∑ I ∈ IsDedekindDomain.primesOverFinset P' T,
            ramificationIdx P' I * inertiaDeg P' I :=
      Finset.single_le_sum (f := fun I => ramificationIdx P' I * inertiaDeg P' I)
        (fun _ _ => Nat.zero_le _) hQ_mem
    rw [hsumT, hfrST, h_fQP', Nat.mul_one] at h_term_le
    exact h_term_le
  -- Equality: e(Q|p) = finrank R T = finrank R S * finrank S T = e(P'|p) * e(Q|P').
  have h_prod_eq : ramificationIdx p P' * ramificationIdx P' Q =
      Module.finrank R S * Module.finrank S T := by
    rw [← h_e_tower, hQe, hfrmul]
  have h_eP'_pos : 0 < Module.finrank R S := by
    have : 0 < ramificationIdx p P' :=
      Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hp0
    exact lt_of_lt_of_le this h_eP'_le
  have h_eQP'_pos : 0 < Module.finrank S T := by
    have : 0 < ramificationIdx P' Q :=
      Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hP'_ne_bot
    exact lt_of_lt_of_le this h_eQP'_le
  have h_eP'_eq : ramificationIdx p P' = Module.finrank R S := by
    -- If either inequality were strict, product would be strict.
    rcases lt_or_eq_of_le h_eP'_le with hlt | heq
    · exfalso
      have : ramificationIdx p P' * ramificationIdx P' Q <
          Module.finrank R S * Module.finrank S T :=
        Nat.mul_lt_mul_of_lt_of_le hlt h_eQP'_le h_eQP'_pos
      omega
    · exact heq
  have h_eQP'_eq : ramificationIdx P' Q = Module.finrank S T := by
    have hrw : ramificationIdx p P' * ramificationIdx P' Q =
        ramificationIdx p P' * Module.finrank S T := by
      rw [h_prod_eq, h_eP'_eq]
    have h_eP'_pos' : 0 < ramificationIdx p P' := by rw [h_eP'_eq]; exact h_eP'_pos
    exact Nat.eq_of_mul_eq_mul_left h_eP'_pos' hrw
  -- P' = P via uniqueness in S (e(P'|p) = finrank R S and f = 1).
  have hS_tr : p.IsTotallyRamifiedIn S :=
    (isTotallyRamifiedIn_iff_exists_ramificationIdx_eq_finrank
      (S := S) R K KS hp0).mpr ⟨P', hP'_under, hP'_liesOver_p, h_eP'_eq⟩
  -- We don't yet know e(P|p), but we know e(P'|p) = finrank R S, f(P'|p) = 1, so P' is
  -- the unique prime witnessing total ramification at S level; in particular if P also
  -- lies over p then P = P'.
  obtain ⟨P'', ⟨hP''p, hP''o, hP''e, hP''f⟩, huniqS⟩ := hS_tr
  have hP'_eq_P'' : P' = P'' := huniqS P' ⟨hP'_under, hP'_liesOver_p, h_eP'_eq, h_fP'⟩
  -- Now show P = P' by showing P has same data. Since p is totally ramified in S, P = P''.
  -- All primes of S over p coincide. Use the singleton property from primesOverFinset.
  have hP_mem : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hPp, hPo⟩
  -- From sum and uniqueness arguments inside the iff proof we know the primesOverFinset
  -- is {P'}. Re-derive directly: the total-ram witness shows e * f = finrank, sum bound = finrank.
  have hsingle : IsDedekindDomain.primesOverFinset p S = {P'} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hP'_mem, fun I hI ↦ ?_⟩
    have hIp : I.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hI).1
    have hIo : I.LiesOver p := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hI).2
    by_contra hIne
    -- Sum over Finset includes both P' and I, contradicting sum = finrank R S.
    have hI_pos : 0 < ramificationIdx p I * inertiaDeg p I := by
      refine Nat.mul_pos ?_ ?_
      · exact Nat.pos_iff_ne_zero.mpr <|
          IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hp0
      · exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg_ne_zero p I
    have hsplit :
        ∑ J ∈ IsDedekindDomain.primesOverFinset p S,
            ramificationIdx p J * inertiaDeg p J =
          ramificationIdx p P' * inertiaDeg p P' +
            ∑ J ∈ (IsDedekindDomain.primesOverFinset p S).erase P',
              ramificationIdx p J * inertiaDeg p J :=
      (Finset.add_sum_erase _ _ hP'_mem).symm
    have hImem_erase : I ∈ (IsDedekindDomain.primesOverFinset p S).erase P' :=
      Finset.mem_erase.mpr ⟨hIne, hI⟩
    have herase_pos :
        0 < ∑ J ∈ (IsDedekindDomain.primesOverFinset p S).erase P',
              ramificationIdx p J * inertiaDeg p J := by
      refine Finset.sum_pos (fun J hJ ↦ ?_) ⟨I, hImem_erase⟩
      have hJp : J.IsPrime :=
        ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp
          (Finset.mem_of_mem_erase hJ)).1
      have hJo : J.LiesOver p :=
        ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp
          (Finset.mem_of_mem_erase hJ)).2
      refine Nat.mul_pos ?_ ?_
      · exact Nat.pos_iff_ne_zero.mpr <|
          IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hp0
      · exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg_ne_zero p J
    have : ∑ J ∈ IsDedekindDomain.primesOverFinset p S,
              ramificationIdx p J * inertiaDeg p J > Module.finrank R S := by
      rw [hsplit, h_eP'_eq, h_fP', Nat.mul_one]
      omega
    rw [hsumS, hfrRS] at this
    exact lt_irrefl _ this
  have hP_eq : P = P' := by
    have := hP_mem
    rw [hsingle, Finset.mem_singleton] at this
    exact this
  subst hP_eq
  -- Conclude P'.IsTotallyRamifiedIn T via iff at level S → T.
  exact (isTotallyRamifiedIn_iff_exists_ramificationIdx_eq_finrank
    (R := S) (S := T) KS L hP'_ne_bot).mpr ⟨Q, hQp, hQ_liesOver_P', h_eQP'_eq⟩

end Tower

end Ideal

end
