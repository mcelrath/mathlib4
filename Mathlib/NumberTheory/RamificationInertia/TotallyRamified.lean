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

end Ideal

end
