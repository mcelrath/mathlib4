/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Ideals factored on a finite set of primes

For a Dedekind domain `R` and a `Finset (Ideal R)` of prime ideals `s`, we define
`Ideal.factoredOnPrimes s` — the set of nonzero ideals whose prime factorization is supported
in `s`. This is the ideal-theoretic analog of `Nat.factoredNumbers` (in
`Mathlib.NumberTheory.SmoothNumbers`).

The main result is the bijection
`Ideal.equivProdNatFactoredOnPrimes : ℕ × factoredOnPrimes s ≃ factoredOnPrimes (insert 𝔭 s)`
for a prime ideal `𝔭 ∉ s`. This underlies an Euler-product-style summation over ideals on a
fixed set of primes (the local Euler factor at a rational prime in a number field).

## Main definitions

* `Ideal.factoredOnPrimes s` — set of nonzero ideals with prime factors in `s`.
* `Ideal.equivProdNatFactoredOnPrimes` — recurrence bijection.
-/

@[expose] public section

namespace Ideal

open UniqueFactorizationMonoid Multiset

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- The set of nonzero ideals of `R` whose prime factorization is supported in the
`Finset` `s`. -/
def factoredOnPrimes (s : Finset (Ideal R)) : Set (Ideal R) :=
  {I | I ≠ ⊥ ∧ ∀ 𝔭 ∈ normalizedFactors I, 𝔭 ∈ s}

omit [IsDomain R] in
lemma mem_factoredOnPrimes {s : Finset (Ideal R)} {I : Ideal R} :
    I ∈ factoredOnPrimes s ↔ I ≠ ⊥ ∧ ∀ 𝔭 ∈ normalizedFactors I, 𝔭 ∈ s :=
  Iff.rfl

omit [IsDomain R] in
lemma ne_bot_of_mem_factoredOnPrimes {s : Finset (Ideal R)} {I : Ideal R}
    (h : I ∈ factoredOnPrimes s) : I ≠ ⊥ :=
  h.1

omit [IsDomain R] in
lemma factoredOnPrimes_mono {s t : Finset (Ideal R)} (h : s ⊆ t) :
    factoredOnPrimes s ⊆ factoredOnPrimes t :=
  fun _ ⟨hI₀, hI⟩ => ⟨hI₀, fun 𝔭 hp => h (hI 𝔭 hp)⟩

@[simp]
lemma top_mem_factoredOnPrimes (s : Finset (Ideal R)) : (⊤ : Ideal R) ∈ factoredOnPrimes s := by
  refine ⟨(bot_lt_top (α := Ideal R)).ne', fun 𝔭 hp => ?_⟩
  rw [← Ideal.one_eq_top, normalizedFactors_one] at hp
  exact absurd hp (Multiset.notMem_zero _)

@[simp]
lemma factoredOnPrimes_empty : factoredOnPrimes (∅ : Finset (Ideal R)) = {(⊤ : Ideal R)} := by
  ext I
  refine ⟨fun ⟨hI₀, hI⟩ => ?_, fun hI => ?_⟩
  · -- I has no prime factors and is nonzero, hence I = ⊤.
    have hfac : normalizedFactors I = 0 :=
      Multiset.eq_zero_of_forall_notMem fun 𝔭 hp => Finset.notMem_empty 𝔭 (hI 𝔭 hp)
    have hprodone : (normalizedFactors I).prod = 1 := by rw [hfac, Multiset.prod_zero]
    have h_eq := prod_normalizedFactors_eq hI₀
    rw [hprodone, normalize_eq] at h_eq
    rw [Set.mem_singleton_iff, ← h_eq, Ideal.one_eq_top]
  · rw [Set.mem_singleton_iff] at hI
    rw [hI]
    exact top_mem_factoredOnPrimes ∅

/-- The product of a prime power and an `s`-factored ideal, where `𝔭 ∉ s`, is factored on
`insert 𝔭 s`. -/
lemma pow_mul_mem_factoredOnPrimes {s : Finset (Ideal R)} {𝔭 : Ideal R} (h𝔭 : Prime 𝔭)
    (e : ℕ) {I : Ideal R} (hI : I ∈ factoredOnPrimes s) :
    𝔭 ^ e * I ∈ factoredOnPrimes (insert 𝔭 s) := by
  obtain ⟨hI₀, hIs⟩ := hI
  refine ⟨mul_ne_zero (pow_ne_zero _ h𝔭.ne_zero) hI₀, fun q hq => ?_⟩
  rw [normalizedFactors_mul (pow_ne_zero _ h𝔭.ne_zero) hI₀, Multiset.mem_add,
    normalizedFactors_pow, mem_nsmul] at hq
  rcases hq with ⟨_, hq𝔭⟩ | hqs
  · rw [normalizedFactors_irreducible h𝔭.irreducible, Multiset.mem_singleton,
      normalize_eq] at hq𝔭
    exact hq𝔭 ▸ Finset.mem_insert_self 𝔭 s
  · exact Finset.mem_insert_of_mem (hIs q hqs)

/-- The "tail" of an ideal `J ≠ 0` after extracting all powers of a prime `𝔭`: the ideal
whose normalized factors are `J`'s factors that are different from `𝔭`. -/
noncomputable def tailAt (𝔭 : Ideal R) (J : Ideal R) : Ideal R :=
  ((normalizedFactors J).filter (· ≠ 𝔭)).prod

omit [IsDomain R] in
lemma tailAt_normalizedFactors_eq (𝔭 J : Ideal R) :
    normalizedFactors (tailAt 𝔭 J) = (normalizedFactors J).filter (· ≠ 𝔭) := by
  classical
  unfold tailAt
  apply normalizedFactors_prod_of_prime
  intro q hq
  exact prime_of_normalized_factor q (Multiset.mem_of_le (Multiset.filter_le _ _) hq)

omit [IsDomain R] in
lemma tailAt_ne_bot (𝔭 J : Ideal R) : tailAt 𝔭 J ≠ ⊥ := by
  unfold tailAt
  refine Multiset.prod_ne_zero ?_
  intro hzero
  have := prime_of_normalized_factor 0 (Multiset.mem_of_le (Multiset.filter_le _ _) hzero)
  exact this.ne_zero rfl

omit [IsDomain R] in
lemma pow_count_mul_tailAt {𝔭 J : Ideal R} (hJ₀ : J ≠ ⊥) :
    𝔭 ^ (Multiset.count 𝔭 (normalizedFactors J)) * tailAt 𝔭 J = J := by
  classical
  -- normalizedFactors J = (count 𝔭) • {𝔭} + filter (≠ 𝔭) (normalizedFactors J)
  have hsplit :
      normalizedFactors J =
        Multiset.replicate (Multiset.count 𝔭 (normalizedFactors J)) 𝔭 +
          (normalizedFactors J).filter (· ≠ 𝔭) := by
    have h1 :
        (normalizedFactors J).filter (· = 𝔭) =
          Multiset.replicate (Multiset.count 𝔭 (normalizedFactors J)) 𝔭 := by
      have := Multiset.filter_eq (normalizedFactors J) 𝔭
      simpa [Eq.comm] using this
    calc normalizedFactors J
        = (normalizedFactors J).filter (· = 𝔭) +
            (normalizedFactors J).filter (¬ · = 𝔭) := by
            rw [Multiset.filter_add_not]
      _ = Multiset.replicate (Multiset.count 𝔭 (normalizedFactors J)) 𝔭 +
            (normalizedFactors J).filter (· ≠ 𝔭) := by rw [h1]
  -- Take products on both sides.
  have hprod := congrArg Multiset.prod hsplit
  rw [Multiset.prod_add, Multiset.prod_replicate] at hprod
  have hnorm : (normalizedFactors J).prod = J := by
    rw [prod_normalizedFactors_eq hJ₀, normalize_eq]
  rw [hnorm] at hprod
  exact hprod.symm

omit [IsDomain R] in
lemma tailAt_mem_factoredOnPrimes {s : Finset (Ideal R)} {𝔭 : Ideal R}
    {J : Ideal R} (hJ : J ∈ factoredOnPrimes (insert 𝔭 s)) :
    tailAt 𝔭 J ∈ factoredOnPrimes s := by
  obtain ⟨_, hJs⟩ := hJ
  refine ⟨tailAt_ne_bot 𝔭 J, fun q hq => ?_⟩
  rw [tailAt_normalizedFactors_eq, Multiset.mem_filter] at hq
  obtain ⟨hqJ, hq_ne⟩ := hq
  exact (Finset.mem_insert.mp (hJs q hqJ)).resolve_left hq_ne

/-- The recurrence bijection `ℕ × factoredOnPrimes s ≃ factoredOnPrimes (insert 𝔭 s)`
for a prime ideal `𝔭 ∉ s`, given by `(e, I) ↦ 𝔭^e * I`. The inverse extracts the
`𝔭`-multiplicity and the prime-`𝔭`-removed part. -/
noncomputable def equivProdNatFactoredOnPrimes {s : Finset (Ideal R)} {𝔭 : Ideal R}
    (h𝔭 : Prime 𝔭) (hs : 𝔭 ∉ s) :
    ℕ × factoredOnPrimes s ≃ factoredOnPrimes (insert 𝔭 s) where
  toFun := fun ⟨e, I, hI⟩ => ⟨𝔭 ^ e * I, pow_mul_mem_factoredOnPrimes h𝔭 e hI⟩
  invFun := fun ⟨J, hJ⟩ =>
    (Multiset.count 𝔭 (normalizedFactors J),
      ⟨tailAt 𝔭 J, tailAt_mem_factoredOnPrimes hJ⟩)
  left_inv := by
    rintro ⟨e, I, hI₀, hIs⟩
    refine Prod.ext ?_ (Subtype.ext ?_)
    · -- Multiset.count 𝔭 (normalizedFactors (𝔭^e * I)) = e since I has no 𝔭 in factors.
      simp only
      rw [normalizedFactors_mul (pow_ne_zero _ h𝔭.ne_zero) hI₀, Multiset.count_add,
        normalizedFactors_pow, normalizedFactors_irreducible h𝔭.irreducible,
        normalize_eq, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
      have h_count_zero : Multiset.count 𝔭 (normalizedFactors I) = 0 :=
        Multiset.count_eq_zero.mpr fun hp => hs (hIs 𝔭 hp)
      rw [h_count_zero, add_zero]
    · -- tailAt 𝔭 (𝔭^e * I) = I
      change ((normalizedFactors (𝔭 ^ e * I)).filter (· ≠ 𝔭)).prod = I
      rw [normalizedFactors_mul (pow_ne_zero _ h𝔭.ne_zero) hI₀, Multiset.filter_add,
        normalizedFactors_pow, normalizedFactors_irreducible h𝔭.irreducible, normalize_eq]
      have h𝔭_filter : (e • ({𝔭} : Multiset (Ideal R))).filter (· ≠ 𝔭) = 0 := by
        rw [Multiset.filter_nsmul]
        simp
      have hI_filter : (normalizedFactors I).filter (· ≠ 𝔭) = normalizedFactors I :=
        Multiset.filter_eq_self.mpr fun q hq hq_eq => hs (hq_eq ▸ hIs q hq)
      rw [h𝔭_filter, hI_filter, Multiset.zero_add, prod_normalizedFactors_eq hI₀, normalize_eq]
  right_inv := by
    rintro ⟨J, hJ⟩
    apply Subtype.ext
    change 𝔭 ^ Multiset.count 𝔭 (normalizedFactors J) * tailAt 𝔭 J = J
    exact pow_count_mul_tailAt hJ.1

@[simp]
lemma equivProdNatFactoredOnPrimes_apply {s : Finset (Ideal R)} {𝔭 : Ideal R} (h𝔭 : Prime 𝔭)
    (hs : 𝔭 ∉ s) (e : ℕ) (I : factoredOnPrimes s) :
    (equivProdNatFactoredOnPrimes h𝔭 hs (e, I) : Ideal R) = 𝔭 ^ e * I.1 := rfl

end Ideal
