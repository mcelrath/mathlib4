/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ramification
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.DedekindZetaEulerProduct
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.TotallyRamified
public import Mathlib.RingTheory.DedekindDomain.IdealsOnPrimes
public import Mathlib.RingTheory.Ideal.GoingUp

set_option linter.style.longFile 2900

/-!
# The Dedekind zeta function of an abelian number field as a product of Dirichlet L-functions

For an abelian Galois extension `K/ℚ`, the Kronecker–Weber theorem embeds `K` into a cyclotomic
field `ℚ(ζₙ)`, and the Galois group `Gal(K/ℚ)` becomes a quotient of `(ℤ/nℤ)ˣ`. The
Pontryagin dual `Gal(K/ℚ)^∨` is then identified with a subgroup `Y` of the Dirichlet
character group `Xₙ` via `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar`.

In this regime the Dedekind zeta function factorizes as

  `dedekindZeta K s = ∏ χ ∈ Y, DirichletCharacter.LFunction χ.primitiveCharacter s`
  (for `1 < re s`).

The use of `primitiveCharacter` is essential: the imprimitive `LFunction χ` for `χ` of conductor
`m < n` differs from the primitive L-function `LFunction χ.primitiveCharacter` by the missing
Euler factors at primes `p ∣ n` with `p ∤ m`, where `χ p = 0` but `χ.primitiveCharacter p ≠ 0`.
Only the primitive product matches `dedekindZeta F s` globally; the imprimitive product would
miss the local Euler factors of `dedekindZeta` at the ramified primes of `F`.

This identity underlies class-field-theoretic constructions over abelian extensions of `ℚ`,
including L-value computations, density theorems, and Generalized Riemann Hypothesis chains in
applied frameworks.

## Status

This file contributes the **per-prime local factor identity at unramified primes** plus the
character-group product swap. The contributed theorems are all sorry-free.

Specifically:

* `dedekindZeta_eulerProduct_tprod` — proved: `tprod` reformulation of the prime-power Euler
  product `NumberField.dedekindZeta_eulerProduct`.
* `dedekindZetaSummand_localSum_eq_prod_inertia` — proved: Step A of the local factor identity.
  The sum `∑ e, dedekindZetaSummand F s (p^e)` equals the product over primes 𝔭 of `𝓞 F` above
  `p` of the geometric series `(1 - (absNorm 𝔭)^(-s))⁻¹`.
* `prod_chars_eq_prod_inertia` — proved (for `p` coprime to `n`): Step B, the character-side
  reduction. Equates the `Y`-product of primitive Dirichlet local Euler factors at `p` with the
  prime-side product over primes above `p`.
* `dedekindZeta_localFactor_eq_prod_dirichletLocal` — proved (for `p` coprime to `n`): Step A
  composed with Step B.
* `prod_dirichletLocal_eq_prod_LFunction` — proved: per-prime ↔ per-character product swap via
  `Multipliable.tprod_finsetProd`.

Mathlib-PR-shaped utility lemmas added in this file (independently of the analytic context):

* `prod_one_sub_nthRootsFinset_mul` — cyclotomic polynomial identity `∏ω∈μ_d (1 - ω·T) = 1 - T^d`.
* `prod_one_sub_groupHom_apply_mul` — abstract orthogonality: for `φ : G →* ℂˣ`,
  `∏ x : G, (1 - (φ x : ℂ) · T) = (1 - T^|range|)^|ker|`.
* `subgroupOfCoprimeConductor_iff_trivial_on_unitsMap_ker` — Pontryagin-conductor equivalence.
* `card_subgroupOfCoprimeConductor_eq_quotient` — cardinality via Pontryagin.
* `card_inter_Y_subgroupOfCoprimeConductor` — `|Y ⊓ Y_p| = |Y|/e` (general, for any prime `p`).
* `frobeniusAt` — the Frobenius element `σ_p ∈ Gal(F/ℚ)` for `p` coprime to `n`.
* `orderOf_restrictNormal_eq_inertiaDegIn` — `orderOf (σ_p|_F) = inertiaDegIn`.
* `evalAtPrime` (definition) — evaluation hom `Y_p →* ℂˣ`.
* `evalAtPrime_card_range_eq_inertiaDegIn` — `|range eval| = inertiaDegIn`.
* `evalAtPrime_card_ker_eq_primesAbove` — `|ker eval| = (primesAboveOf F p).card`.

Multiplicativity of `idealNormCount` (the splitting of `idealNormCount K (m * n)` for coprime
`m, n`) is already provided upstream as
`NumberField.idealNormCount_isMultiplicative` /
`NumberField.idealNormCount_mul_of_coprime` in
`Mathlib.NumberTheory.NumberField.DedekindZetaEulerProduct`.

## Out of scope

The local factor identity at **ramified primes** (`p ∣ n`) is left for follow-up. Once added, the
classical global factorization
`dedekindZeta F s = ∏ χ : Y, DirichletCharacter.LFunction χ.val.primitiveCharacter s`
follows by composition of the per-prime local factor identity (over all primes) with
`prod_dirichletLocal_eq_prod_LFunction`.
-/

-- The file is long due to the extended proof content for the global factorization theorem.
set_option linter.style.longFile 2900 in

@[expose] public section

public noncomputable section

open Filter Complex
open scoped LSeries.notation Topology

namespace NumberField

/-- Auxiliary: any subgroup of `DirichletCharacter ℂ n` is a `Fintype`. Derived from the
`noncomputable` global `Fintype (DirichletCharacter ℂ n)` instance via `Fintype.ofFinite`. -/
noncomputable instance subgroupDirichletCharacterFintype
    {n : ℕ} (Y : Subgroup (DirichletCharacter ℂ n)) : Fintype Y :=
  Fintype.ofFinite _

/-- Auxiliary: the conductor of a Dirichlet character at a positive level is itself positive. -/
instance dirichletCharacterConductorNeZero {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    (χ : DirichletCharacter R n) : NeZero χ.conductor :=
  ⟨DirichletCharacter.conductor_ne_zero _⟩

variable (K : Type*) [Field K] [NumberField K]

/-! ### Clean `tprod`-form of the prime-power Euler product

The upstream `dedekindZeta_eulerProduct` is stated as a `Tendsto` of finite partial products.
For analytic manipulation we package the same content as a `tprod` over the primes.
-/

/-- The Euler product for the Dedekind zeta function as a `tprod` over rational primes. -/
theorem dedekindZeta_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    ∏' p : Nat.Primes, ∑' e : ℕ, dedekindZetaSummand K s (p ^ e) = dedekindZeta K s := by
  rw [← tsum_dedekindZetaSummand K s]
  exact ArithmeticFunction.IsMultiplicative.eulerProduct_tprod
    (dedekindZetaSummand_isMultiplicative K s) (summable_dedekindZetaSummand K s hs)

/-! ### Local Euler factor: prime-power summand

The local Euler factor of `dedekindZeta F` at the rational prime `p` is the inner sum
`∑' e, dedekindZetaSummand F s (p ^ e)`. We factor the local-factor identity through a
"middle term" — the product of geometric series indexed by primes of `𝓞 F` above `p` —
which both sides equal:

* **Step A (analytic side).** Unique factorization in `𝓞 F` plus a Fubini-style swap of `tsum`
  and `Finset.prod` gives
  `∑' e, dedekindZetaSummand F s (p^e) = ∏_{𝔭∣p} (1 - (absNorm 𝔭 : ℂ)^(-s))⁻¹`.
* **Step B (character side).** Frobenius via `galEquivZMod_stabilizer` together with the
  cyclic-group character identity
  `∏_{χ ∈ Y} (1 - χ(g) T) = (1 - T^{ord g})^{|Y|/ord g}` gives
  `∏_{χ ∈ Y} (1 - χ̃(p) p^(-s))⁻¹ = ∏_{𝔭∣p} (1 - (absNorm 𝔭 : ℂ)^(-s))⁻¹`.

Composing Step A and Step B gives `dedekindZeta_localFactor_eq_prod_dirichletLocal`.
-/

/-- The Finset of prime ideals of `𝓞 F` lying over the rational prime `p`. -/
noncomputable def primesAboveOf (F : Type*) [Field F] [NumberField F] (p : ℕ) :
    Finset (Ideal (𝓞 F)) :=
  IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F)

/-- **A.5 (geometric series at one prime).** For a nonzero prime ideal `𝔭` of `𝓞 F` and `s` in
the absolute-convergence half-plane, the geometric series `∑'k absNorm(𝔭)^(-ks)` equals the
local Euler factor `(1 - absNorm(𝔭)^(-s))⁻¹`. -/
lemma tsum_absNorm_pow_neg_geom
    {F : Type*} [Field F] [NumberField F]
    {𝔭 : Ideal (𝓞 F)} (h𝔭_p : 𝔭.IsPrime) (h𝔭_ne : 𝔭 ≠ ⊥)
    {s : ℂ} (hs : 1 < s.re) :
    ∑' k : ℕ, ((Ideal.absNorm 𝔭 : ℂ) ^ (-s)) ^ k = (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  refine tsum_geometric_of_norm_lt_one ?_
  -- absNorm 𝔭 ≥ 2: prime ideal in 𝓞 F with N(𝔭) > 1 (since 𝔭 ≠ ⊤).
  have h𝔭_prime : Prime 𝔭 := Ideal.prime_of_isPrime h𝔭_ne h𝔭_p
  have h_norm_pos : 0 < Ideal.absNorm 𝔭 := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => h𝔭_ne (Ideal.absNorm_eq_zero_iff.mp h)
  have h_norm_ne_one : Ideal.absNorm 𝔭 ≠ 1 := by
    intro h
    have hutop : 𝔭 = ⊤ := Ideal.absNorm_eq_one_iff.mp h
    apply h𝔭_prime.not_unit
    rw [hutop, ← Ideal.one_eq_top]
    exact isUnit_one
  have h2 : 2 ≤ Ideal.absNorm 𝔭 := by omega
  rw [Complex.norm_natCast_cpow_of_pos h_norm_pos]
  -- (absNorm 𝔭 : ℝ)^(-s).re < 1.  Since (-s).re = -re s < -1 < 0, and absNorm ≥ 2 > 1.
  have h2real : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast h2
  have h1lt : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := lt_of_lt_of_le one_lt_two h2real
  have hneg_re : (-s).re < 0 := by
    rw [Complex.neg_re]; linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg h1lt hneg_re

/-- The forward direction of the Step A bijection: an ideal of `𝓞 F` with `absNorm = p^e` is
factored on primes above `p`. Each prime factor `𝔭` of `I` has `absNorm 𝔭 ∣ p^e`, so the rational
prime under `𝔭` (`absNorm (under ℤ 𝔭)` is itself prime by `Nat.absNorm_under_prime` and divides
`absNorm 𝔭 ∣ p^e`, hence equals `p`) determines that `under ℤ 𝔭 = span {(p : ℤ)}`. -/
lemma factoredOnPrimes_of_absNorm_pow
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) {I : Ideal (𝓞 F)} {e : ℕ} (hI : Ideal.absNorm I = p ^ e) :
    I ∈ Ideal.factoredOnPrimes (primesAboveOf F p) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_span_ne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by
    simp [hp.ne_zero]
  refine ⟨?_, ?_⟩
  · -- I ≠ ⊥
    intro h_bot
    rw [h_bot, Ideal.absNorm_bot] at hI
    exact (pow_pos hp.pos e).ne' hI.symm
  · intro 𝔭 h𝔭_in
    -- 𝔭 is a prime factor of I.
    have h𝔭_prime : Prime 𝔭 :=
      UniqueFactorizationMonoid.prime_of_normalized_factor 𝔭 h𝔭_in
    have h𝔭_isPrime : 𝔭.IsPrime := Ideal.isPrime_of_prime h𝔭_prime
    have h𝔭_ne : 𝔭 ≠ ⊥ := h𝔭_prime.ne_zero
    haveI : NeZero 𝔭 := ⟨h𝔭_ne⟩
    -- absNorm (under ℤ 𝔭) is a prime number.
    have hpunder_prime : (Ideal.absNorm (Ideal.under ℤ 𝔭)).Prime := Nat.absNorm_under_prime 𝔭
    -- absNorm (under ℤ 𝔭) ∣ absNorm 𝔭.
    have hpunder_dvd_p𝔭 : Ideal.absNorm (Ideal.under ℤ 𝔭) ∣ Ideal.absNorm 𝔭 :=
      Int.absNorm_under_dvd_absNorm 𝔭
    -- 𝔭 ⊇ I (because 𝔭 ∣ I as ideals), hence absNorm 𝔭 ∣ absNorm I = p^e.
    have h𝔭_dvd_I : 𝔭 ∣ I :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔭_in
    have hp𝔭_dvd_pI : Ideal.absNorm 𝔭 ∣ Ideal.absNorm I :=
      Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp h𝔭_dvd_I)
    have hp𝔭_dvd_pe : Ideal.absNorm 𝔭 ∣ p ^ e := hI ▸ hp𝔭_dvd_pI
    have hpunder_dvd_pe : Ideal.absNorm (Ideal.under ℤ 𝔭) ∣ p ^ e :=
      hpunder_dvd_p𝔭.trans hp𝔭_dvd_pe
    -- A prime divisor of p^e is p.
    have hpunder_eq_p : Ideal.absNorm (Ideal.under ℤ 𝔭) = p :=
      (Nat.prime_dvd_prime_iff_eq hpunder_prime hp).mp
        (hpunder_prime.dvd_of_dvd_pow hpunder_dvd_pe)
    -- Therefore under ℤ 𝔭 = span {(p:ℤ)}, so 𝔭 lies over span {(p:ℤ)}.
    have hunder_eq : Ideal.under ℤ 𝔭 = Ideal.span ({(p : ℤ)} : Set ℤ) := by
      have h1 := Int.ideal_span_absNorm_eq_self (Ideal.under ℤ 𝔭)
      rw [hpunder_eq_p] at h1
      exact h1.symm
    haveI hLies : 𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := ⟨hunder_eq.symm⟩
    -- Membership in primesAboveOf F p (which is primesOverFinset (span {(p:ℤ)}) (𝓞 F)).
    change 𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F)
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp_span_ne]
    exact ⟨h𝔭_isPrime, hLies⟩

/-- The backward direction of the Step A bijection: an ideal factored on primes above `p` has
`absNorm` equal to a power of `p`. -/
lemma exists_absNorm_pow_of_factoredOnPrimes
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) {I : Ideal (𝓞 F)}
    (hI : I ∈ Ideal.factoredOnPrimes (primesAboveOf F p)) :
    ∃ e : ℕ, Ideal.absNorm I = p ^ e := by
  obtain ⟨hI_ne, hI_factors⟩ := hI
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_span_ne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by simp [hp.ne_zero]
  have hp_span_isPrime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Int.ideal_span_isMaximal_of_prime p).isPrime
  have hN_span : Ideal.absNorm (Ideal.span ({(p : ℤ)} : Set ℤ)) = p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Int.card_ideal_quot p
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd ?_ ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI_ne
  · intro d hd hd_dvd
    -- absNorm I = product over normalized factors of absNorm 𝔭.
    have habs : Ideal.absNorm I =
        (Multiset.map Ideal.absNorm (UniqueFactorizationMonoid.normalizedFactors I)).prod := by
      have hprod := UniqueFactorizationMonoid.prod_normalizedFactors_eq hI_ne
      rw [normalize_eq] at hprod
      conv_lhs => rw [← hprod]
      exact Ideal.absNorm.toMonoidHom.map_multiset_prod _
    rw [habs] at hd_dvd
    -- d prime divides multiset prod → divides some element.
    have hd_prime : Prime d := hd.prime
    obtain ⟨q, hq_in, hd_q⟩ := hd_prime.exists_mem_multiset_dvd hd_dvd
    rw [Multiset.mem_map] at hq_in
    obtain ⟨𝔭, h𝔭_in, h𝔭_eq⟩ := hq_in
    -- 𝔭 ∈ primesAboveOf F p, so 𝔭 lies over span {(p:ℤ)}.
    have h𝔭_above : 𝔭 ∈ primesAboveOf F p := hI_factors 𝔭 h𝔭_in
    have h_in_primesOver :
        𝔭 ∈ Ideal.primesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
      have h_coe : 𝔭 ∈ ((IsDedekindDomain.primesOverFinset
          (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) : Finset _) : Set _) :=
        Finset.mem_coe.mpr h𝔭_above
      rwa [IsDedekindDomain.coe_primesOverFinset hp_span_ne] at h_coe
    haveI : 𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := h_in_primesOver.2
    -- absNorm 𝔭 = p ^ inertiaDeg, hence d | p^k → d = p.
    have hN := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔭 _ hp_span_isPrime hp_span_ne
    rw [hN_span] at hN
    rw [← h𝔭_eq, hN] at hd_q
    exact (Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow hd_q)

/-- The bijection witnessing that ideals in `factoredOnPrimes (primesAboveOf F p)` correspond
to pairs `(e, I)` with `absNorm I = p^e`. -/
private noncomputable def factoredOnPrimes_equiv_sigmaNormFiber
    {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    (Σ e : ℕ, NumberField.NormFiber F (p ^ e)) ≃
      Ideal.factoredOnPrimes (primesAboveOf F p) :=
  Equiv.ofBijective
    (fun σ => ⟨σ.2.1, factoredOnPrimes_of_absNorm_pow hp σ.2.2⟩)
    ⟨by
      -- Injective.
      rintro ⟨e₁, I₁, hI₁⟩ ⟨e₂, I₂, hI₂⟩ heq
      have hI_eq : I₁ = I₂ := congrArg Subtype.val heq
      have he_eq : e₁ = e₂ :=
        Nat.pow_right_injective hp.two_le (hI₁.symm.trans (hI_eq ▸ hI₂))
      subst he_eq
      subst hI_eq
      rfl,
     by
      -- Surjective.
      rintro ⟨I, hI⟩
      obtain ⟨e, he⟩ := exists_absNorm_pow_of_factoredOnPrimes hp hI
      exact ⟨⟨e, ⟨I, he⟩⟩, rfl⟩⟩

@[simp]
private lemma factoredOnPrimes_equiv_sigmaNormFiber_apply
    {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (σ : Σ e : ℕ, NumberField.NormFiber F (p ^ e)) :
    ((factoredOnPrimes_equiv_sigmaNormFiber hp σ : Ideal.factoredOnPrimes (primesAboveOf F p)).1)
      = σ.2.1 := rfl

/-- **Step A reindex.** The prime-power Dedekind sum equals the sum of `absNorm(I)^(-s)`
over ideals of `𝓞 F` whose prime support lies above `p`. -/
theorem tsum_dedekindZetaSummand_pow_eq_tsum_factoredOnPrimes
    (F : Type*) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ∑' e : ℕ, dedekindZetaSummand F s (p ^ e) =
      ∑' I : Ideal.factoredOnPrimes (primesAboveOf F p),
        (Ideal.absNorm I.1 : ℂ) ^ (-s) := by
  have hpe_ne : ∀ e : ℕ, (p ^ e : ℕ) ≠ 0 := fun e => pow_ne_zero e hp.ne_zero
  -- NormFiber Finite/Fintype instances.
  haveI : ∀ e : ℕ, Finite (NumberField.NormFiber F (p ^ e)) := by
    intro e
    change Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = p ^ e}
    exact (Ideal.finite_setOf_absNorm_eq _).to_subtype
  haveI : ∀ e : ℕ, Fintype (NumberField.NormFiber F (p ^ e)) := fun e => Fintype.ofFinite _
  -- Unfold dedekindZetaSummand for nonzero argument.
  have hsummand : ∀ e : ℕ,
      dedekindZetaSummand F s (p ^ e) =
        (NumberField.idealNormCount F (p ^ e) : ℂ) * ((p ^ e : ℕ) : ℂ) ^ (-s) := by
    intro e
    rw [NumberField.dedekindZetaSummand_apply, LSeries.term_def₀ (by simp)]
  -- Step 1: Inner sum over NormFiber F (p^e) equals dedekindZetaSummand F s (p^e).
  have hinner : ∀ e : ℕ,
      ∑' I : NumberField.NormFiber F (p ^ e), (Ideal.absNorm I.1 : ℂ) ^ (-s) =
        dedekindZetaSummand F s (p ^ e) := by
    intro e
    rw [tsum_eq_sum (s := (Finset.univ : Finset (NumberField.NormFiber F (p ^ e))))
      (fun I hI => absurd (Finset.mem_univ I) hI)]
    have hconst : ∀ I : NumberField.NormFiber F (p ^ e),
        ((Ideal.absNorm I.1 : ℂ) ^ (-s)) = ((p ^ e : ℕ) : ℂ) ^ (-s) := fun I => by rw [I.2]
    rw [Finset.sum_congr rfl (fun I _ => hconst I), Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card (NumberField.NormFiber F (p ^ e)) : ℂ) =
        (NumberField.idealNormCount F (p ^ e) : ℂ) := by
      rw [NumberField.idealNormCount_apply_of_ne_zero F (hpe_ne e), Fintype.card_eq_nat_card]
      rfl
    rw [hsummand, nsmul_eq_mul, hcard]
  -- Step 2: Inner summable for each e (Fintype).
  have hsumInner : ∀ e : ℕ,
      Summable (fun I : NumberField.NormFiber F (p ^ e) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)) :=
    fun e => Summable.of_finite
  -- Step 3: Sigma sum is summable: reduces to summability of LHS via norms.
  have hinner_norm : ∀ e : ℕ,
      ∑' I : NumberField.NormFiber F (p ^ e), ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ =
        ‖dedekindZetaSummand F s (p ^ e)‖ := by
    intro e
    rw [tsum_eq_sum (s := (Finset.univ : Finset _))
      (fun I hI => absurd (Finset.mem_univ I) hI)]
    have hconst : ∀ I : NumberField.NormFiber F (p ^ e),
        ‖((Ideal.absNorm I.1 : ℂ) ^ (-s))‖ = ‖(((p ^ e : ℕ) : ℂ) ^ (-s))‖ := fun I => by rw [I.2]
    rw [Finset.sum_congr rfl (fun I _ => hconst I), Finset.sum_const, Finset.card_univ]
    rw [hsummand, norm_mul]
    have hcardR : (Fintype.card (NumberField.NormFiber F (p ^ e)) : ℝ) =
        ‖(NumberField.idealNormCount F (p ^ e) : ℂ)‖ := by
      rw [NumberField.idealNormCount_apply_of_ne_zero F (hpe_ne e), Complex.norm_natCast,
        Fintype.card_eq_nat_card]
      rfl
    rw [nsmul_eq_mul]
    push_cast
    rw [hcardR]
  have hsumSigma : Summable
      (fun σ : (Σ e : ℕ, NumberField.NormFiber F (p ^ e)) ↦
        (Ideal.absNorm σ.2.1 : ℂ) ^ (-s)) := by
    rw [← summable_norm_iff]
    refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨fun e => (hsumInner e).norm, ?_⟩
    have hsumLHS : Summable (fun e : ℕ ↦ ‖dedekindZetaSummand F s (p ^ e)‖) :=
      (summable_dedekindZetaSummand F s hs).comp_injective
        (fun e e' h => Nat.pow_right_injective hp.two_le h)
    exact hsumLHS.congr fun e => (hinner_norm e).symm
  -- Step 4: Apply tsum_sigma' and equiv
  have hLHS : ∑' e : ℕ, dedekindZetaSummand F s (p ^ e) =
      ∑' σ : (Σ e : ℕ, NumberField.NormFiber F (p ^ e)),
        (Ideal.absNorm σ.2.1 : ℂ) ^ (-s) := by
    rw [hsumSigma.tsum_sigma' hsumInner]
    exact tsum_congr fun e => (hinner e).symm
  rw [hLHS, ← (factoredOnPrimes_equiv_sigmaNormFiber hp).tsum_eq
    (fun I : Ideal.factoredOnPrimes (primesAboveOf F p) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))]
  rfl

/-- **Step A.** The prime-power Dedekind summand factorizes as a product of local Euler factors
over the primes of `𝓞 F` lying above `p`. Composes the reindex
`tsum_dedekindZetaSummand_pow_eq_tsum_factoredOnPrimes`, the HasSum-form Euler product
`Ideal.tsum_factoredOnPrimes_eq_prod_tsum`, and the geometric-series identity
`tsum_absNorm_pow_neg_geom`. -/
theorem dedekindZetaSummand_localSum_eq_prod_inertia
    (F : Type*) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ∑' e : ℕ, dedekindZetaSummand F s (p ^ e) =
      ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  -- Define the function f I = (absNorm I : ℂ)^(-s).
  set f : Ideal (𝓞 F) → ℂ := fun I => (Ideal.absNorm I : ℂ) ^ (-s) with hf_def
  -- Hypotheses for tsum_factoredOnPrimes_eq_prod_tsum.
  have hf_top : f ⊤ = 1 := by
    simp [f, Ideal.absNorm_top]
  have hf_mul : ∀ I J : Ideal (𝓞 F), I ≠ ⊥ → J ≠ ⊥ → f (I * J) = f I * f J := by
    intro I J _ _
    simp only [f, map_mul, Nat.cast_mul]
    exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (-s)
  have hpow_eq : ∀ (𝔭 : Ideal (𝓞 F)) (k : ℕ),
      f (𝔭 ^ k) = ((Ideal.absNorm 𝔭 : ℂ) ^ (-s)) ^ k := by
    intro 𝔭 k
    change ((Ideal.absNorm (𝔭 ^ k) : ℕ) : ℂ) ^ (-s) = ((Ideal.absNorm 𝔭 : ℂ) ^ (-s)) ^ k
    rw [map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  have hsum_norm : ∀ {𝔭 : Ideal (𝓞 F)}, Prime 𝔭 →
      Summable (fun n : ℕ ↦ ‖f (𝔭 ^ n)‖) := by
    intro 𝔭 h𝔭_prime
    have h𝔭_ne : 𝔭 ≠ ⊥ := h𝔭_prime.ne_zero
    have hgeom : Summable (fun k : ℕ ↦ ((Ideal.absNorm 𝔭 : ℂ) ^ (-s)) ^ k) := by
      refine summable_geometric_of_norm_lt_one ?_
      have h_norm_pos : 0 < Ideal.absNorm 𝔭 := by
        rw [Nat.pos_iff_ne_zero]
        exact fun h => h𝔭_ne (Ideal.absNorm_eq_zero_iff.mp h)
      have h_norm_ne_one : Ideal.absNorm 𝔭 ≠ 1 := by
        intro h
        have : 𝔭 = ⊤ := Ideal.absNorm_eq_one_iff.mp h
        apply h𝔭_prime.not_unit
        rw [this, ← Ideal.one_eq_top]; exact isUnit_one
      have h2 : 2 ≤ Ideal.absNorm 𝔭 := by omega
      rw [Complex.norm_natCast_cpow_of_pos h_norm_pos]
      have h1lt : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
      have hneg : (-s).re < 0 := by rw [Complex.neg_re]; linarith
      exact Real.rpow_lt_one_of_one_lt_of_neg h1lt hneg
    have hconv : (fun n : ℕ ↦ ‖f (𝔭 ^ n)‖) =
        fun n : ℕ ↦ ‖((Ideal.absNorm 𝔭 : ℂ) ^ (-s)) ^ n‖ := by
      funext n; rw [hpow_eq]
    rw [hconv]
    exact hgeom.norm
  have hs_prime : ∀ 𝔭 ∈ primesAboveOf F p, Prime 𝔭 := by
    intro 𝔭 h𝔭
    have hp_span_ne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by
      simp [hp.ne_zero]
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hp_span_max : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
      Int.ideal_span_isMaximal_of_prime p
    have h_mem' : 𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) :=
      h𝔭
    have h_in : 𝔭 ∈ Ideal.primesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
      have h_coe : 𝔭 ∈ ((IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F)
          : Finset _) : Set _) := Finset.mem_coe.mpr h_mem'
      rwa [IsDedekindDomain.coe_primesOverFinset hp_span_ne] at h_coe
    exact Ideal.prime_of_mem_primesOver hp_span_ne h_in
  -- Compose.
  rw [tsum_dedekindZetaSummand_pow_eq_tsum_factoredOnPrimes F hp hs]
  rw [Ideal.tsum_factoredOnPrimes_eq_prod_tsum hf_top hf_mul hsum_norm hs_prime]
  refine Finset.prod_congr rfl fun 𝔭 hp_mem => ?_
  -- Per-prime: ∑'k f(𝔭^k) = (1 - (absNorm 𝔭 : ℂ)^(-s))⁻¹.
  have h𝔭_prime : Prime 𝔭 := hs_prime 𝔭 hp_mem
  have h𝔭_ne : 𝔭 ≠ ⊥ := h𝔭_prime.ne_zero
  have h𝔭_p : 𝔭.IsPrime := Ideal.isPrime_of_prime h𝔭_prime
  rw [tsum_congr (fun k => hpow_eq 𝔭 k)]
  exact tsum_absNorm_pow_neg_geom h𝔭_p h𝔭_ne hs

/-! ### Sub-lemma B.2 — cyclic-group character orthogonality (abstract)

A standalone abstract result: for a finite cyclic group of `d`-th roots of unity in `ℂ`, the
product `∏ω (1 - ω T) = 1 - T^d`. This is the polynomial form via
`Polynomial.X_pow_sub_one_eq_prod` evaluated at `X = T⁻¹` and rescaled by `T^d`.
-/

/-- For a positive integer `d` and `T : ℂ`, the product over the `d`-th roots of unity in `ℂ`
of `(1 - ω·T)` equals `1 - T^d`. This is the polynomial identity
`∏_{ω ∈ μ_d} (1 - ωX) = 1 - X^d` evaluated in `ℂ`. -/
lemma prod_one_sub_nthRootsFinset_mul (d : ℕ) (hd : 0 < d) (T : ℂ) :
    ∏ ω ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ω * T) = 1 - T ^ d := by
  by_cases hT : T = 0
  · subst hT
    simp only [mul_zero, sub_zero, Finset.prod_const_one, zero_pow hd.ne', sub_zero]
  · -- T ≠ 0: substitute X = T⁻¹ in `X^d - 1 = ∏ω (X - ω)` and rescale.
    have hζ := Complex.isPrimitiveRoot_exp d hd.ne'
    have hpoly := Polynomial.X_pow_sub_one_eq_prod hd hζ
    have h_eval := congr_arg (Polynomial.eval T⁻¹) hpoly
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_prod, Polynomial.eval_C] at h_eval
    -- h_eval : T⁻¹ ^ d - 1 = ∏ω (T⁻¹ - ω)
    have hTd : T ^ d ≠ 0 := pow_ne_zero d hT
    have hT_inv : T⁻¹ ^ d = (T ^ d)⁻¹ := inv_pow T d
    -- Multiply both sides by T^d.
    have key : (T ^ d) * (T⁻¹ ^ d - 1) =
        (T ^ d) * ∏ ω ∈ Polynomial.nthRootsFinset d (1 : ℂ), (T⁻¹ - ω) := by
      rw [h_eval]
    -- Rewrite both sides.
    have hLHS : T ^ d * (T⁻¹ ^ d - 1) = 1 - T ^ d := by
      rw [hT_inv, mul_sub, mul_one, mul_inv_cancel₀ hTd]
    have hRHS_card : (Polynomial.nthRootsFinset d (1 : ℂ)).card = d :=
      hζ.card_nthRootsFinset
    have hRHS : T ^ d * ∏ ω ∈ Polynomial.nthRootsFinset d (1 : ℂ), (T⁻¹ - ω) =
        ∏ ω ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ω * T) := by
      rw [show (T ^ d : ℂ) = ∏ _ω ∈ Polynomial.nthRootsFinset d (1 : ℂ), T from ?_]
      · rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun ω _ => ?_
        rw [mul_sub, mul_inv_cancel₀ hT, mul_comm]
      · rw [Finset.prod_const, hRHS_card]
    -- ∏ω (1 - ωT) = T^d · ∏ω (T⁻¹ - ω) = T^d · (T⁻¹^d - 1) = 1 - T^d
    rw [← hRHS, ← key, hLHS]

/-! ### Sub-lemma B.2 (continued) — fiber decomposition + range identification

The polynomial identity `prod_one_sub_nthRootsFinset_mul` lifts to an arbitrary finite group `G`
via fiber decomposition. For `φ : G →* ℂˣ` a hom from a finite group, every fiber of `φ` over
a value in the range has cardinality `Nat.card (ker φ)`, and the range (viewed as a Finset of
ℂˣ) consists of exactly the `d`-th roots of unity, where `d = Nat.card (range φ)`. Combining
yields the abstract orthogonality identity.
-/

/-- Fibers of a finite-group homomorphism over the range have size equal to the kernel. -/
private lemma card_fiber_eq_card_ker_aux {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂˣ) (y : φ.range) :
    Nat.card {x : G // φ.rangeRestrict x = y} = Nat.card φ.ker := by
  obtain ⟨x₀, hx₀⟩ := φ.rangeRestrict_surjective y
  have h_x₀ : φ x₀ = (y : ℂˣ) := congr_arg Subtype.val hx₀
  refine Nat.card_congr ?_
  refine
    { toFun := fun a => ⟨x₀⁻¹ * a.val, ?_⟩
      invFun := fun b => ⟨x₀ * b.val, ?_⟩
      left_inv := fun a => Subtype.ext (by simp [← mul_assoc])
      right_inv := fun b => Subtype.ext (by simp [← mul_assoc]) }
  · -- toFun: a in fiber → x₀⁻¹ * a in ker
    have ha : φ.rangeRestrict a.val = y := a.property
    have h_a : φ a.val = (y : ℂˣ) := congr_arg Subtype.val ha
    show φ (x₀⁻¹ * a.val) = 1
    rw [map_mul, map_inv, h_x₀, h_a, inv_mul_cancel]
  · -- invFun: b in ker → x₀ * b in fiber
    have hb : φ b.val = 1 := b.property
    apply Subtype.ext
    show φ (x₀ * b.val) = (y : ℂˣ)
    rw [map_mul, hb, mul_one, h_x₀]

/-- For a finite group `G` and a hom `φ : G →* ℂˣ`, the image-Finset
`(Finset.image (fun x => ((φ x : ℂˣ) : ℂ)) Finset.univ)` is exactly the `d`-th roots of unity in
`ℂ`, where `d = Nat.card φ.range`. -/
private lemma image_eq_nthRootsFinset_aux {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂˣ) :
    Finset.image (fun y : φ.range => ((y : ℂˣ) : ℂ)) Finset.univ =
      Polynomial.nthRootsFinset (Nat.card φ.range) (1 : ℂ) := by
  classical
  have hd_pos : 0 < Nat.card φ.range := Nat.card_pos
  -- Subset: every value (y : ℂ) for y : range satisfies y^d = 1.
  have h_subset : ∀ y : φ.range, ((y : ℂˣ) : ℂ) ∈
      Polynomial.nthRootsFinset (Nat.card φ.range) (1 : ℂ) := by
    intro y
    rw [Polynomial.mem_nthRootsFinset hd_pos]
    have hy : (y : φ.range) ^ (Nat.card φ.range) = 1 := pow_card_eq_one'
    have hy' : ((y : ℂˣ) : ℂ) ^ (Nat.card φ.range) = 1 := by
      have h1 : (y : ℂˣ) ^ (Nat.card φ.range) = 1 := by
        have := congr_arg (Subgroup.subtype φ.range) hy
        simpa using this
      have := congr_arg (Units.coeHom ℂ) h1
      simpa using this
    exact hy'
  -- Image is contained in nthRootsFinset.
  have h_sub : Finset.image (fun y : φ.range => ((y : ℂˣ) : ℂ)) Finset.univ ≤
      Polynomial.nthRootsFinset (Nat.card φ.range) (1 : ℂ) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, _, rfl⟩ := hz
    exact h_subset y
  -- Image has cardinality d.
  have h_inj : Function.Injective (fun y : φ.range => ((y : ℂˣ) : ℂ)) := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    exact h
  have h_card_image : (Finset.image (fun y : φ.range => ((y : ℂˣ) : ℂ)) Finset.univ).card =
      Nat.card φ.range := by
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_univ, Fintype.card_eq_nat_card]
  -- nthRootsFinset has cardinality d (using a primitive d-th root of unity in ℂ).
  have h_card_roots :
      (Polynomial.nthRootsFinset (Nat.card φ.range) (1 : ℂ)).card = Nat.card φ.range := by
    have hζ := Complex.isPrimitiveRoot_exp (Nat.card φ.range) hd_pos.ne'
    exact hζ.card_nthRootsFinset
  -- Equal Finsets.
  exact Finset.eq_of_subset_of_card_le h_sub (h_card_roots.symm ▸ h_card_image.ge)

/-- **Abstract orthogonality.** For a finite group `G` and a homomorphism `φ : G →* ℂˣ`, the
product `∏ x : G, (1 - φ(x) · T)` equals `(1 - T^d)^k`, where `d = Nat.card φ.range` is the
order of the image and `k = Nat.card φ.ker` is the order of the kernel.

This is the workhorse of Step B: we apply it with `G = Y`, `φ = (χ ↦ χ((p : (ZMod n)ˣ)))`, and
`T = (p : ℂ)^(-s)`, so `d` will be the inertia degree of any prime above `p` and `k` will be the
number of primes above `p`. -/
lemma prod_one_sub_groupHom_apply_mul {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂˣ) (T : ℂ) :
    ∏ x : G, (1 - (φ x : ℂ) * T) =
      (1 - T ^ Nat.card φ.range) ^ Nat.card φ.ker := by
  classical
  -- Step 1: fiberwise decomposition over φ.range.
  have h_maps_to : ∀ x ∈ (Finset.univ : Finset G), φ.rangeRestrict x ∈
      (Finset.univ : Finset φ.range) := fun _ _ => Finset.mem_univ _
  rw [← Finset.prod_fiberwise_of_maps_to h_maps_to (f := fun x => 1 - (φ x : ℂ) * T)]
  -- Step 2: each inner product evaluates to (1 - (y : ℂˣ) * T)^k.
  have h_inner : ∀ y : φ.range,
      ∏ x ∈ Finset.univ with φ.rangeRestrict x = y, (1 - (φ x : ℂ) * T) =
        (1 - ((y : ℂˣ) : ℂ) * T) ^ Nat.card φ.ker := by
    intro y
    -- Inner product: each x in the fiber satisfies φ x = (y : ℂˣ), so the integrand
    -- equals (1 - ((y : ℂˣ) : ℂ) * T) constantly. Use prod_const + fiber cardinality.
    rw [Finset.prod_congr rfl (g := fun _ => (1 - ((y : ℂˣ) : ℂ) * T)) ?_]
    · rw [Finset.prod_const]
      congr 1
      -- Match cardinalities.
      have hcard := card_fiber_eq_card_ker_aux φ y
      rw [Nat.card_eq_fintype_card] at hcard
      rw [show (Finset.univ.filter (fun x : G => φ.rangeRestrict x = y)).card =
            Fintype.card {x : G // φ.rangeRestrict x = y} from ?_, hcard]
      · rw [Fintype.card_subtype]
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hxy : φ.rangeRestrict x = y := hx.2
      have : φ x = (y : ℂˣ) := congr_arg Subtype.val hxy
      rw [this]
  rw [Finset.prod_congr rfl (fun y _ => h_inner y)]
  -- Step 3: pull out the power and use range = nthRootsFinset.
  rw [Finset.prod_pow]
  rw [show ∏ y : φ.range, (1 - ((y : ℂˣ) : ℂ) * T) =
        ∏ ω ∈ Polynomial.nthRootsFinset (Nat.card φ.range) (1 : ℂ), (1 - ω * T) from ?_]
  · -- Apply the polynomial identity.
    have hd_pos : 0 < Nat.card φ.range := Nat.card_pos
    rw [prod_one_sub_nthRootsFinset_mul _ hd_pos]
  · -- Reindex using the image bijection.
    rw [← image_eq_nthRootsFinset_aux φ]
    rw [Finset.prod_image (fun a _ b _ hab => ?_)]
    apply Subtype.ext
    apply Units.ext
    exact hab

/-! ### Step B sub-lemmas

Step B's proof decomposes into four sub-lemmas, each of independent interest:

* **B.1 — Frobenius element identification:** the Frobenius `σ_p ∈ Gal(F/ℚ)` corresponds to
  `(p : (ZMod n)ˣ)` under the composition `(ZMod n)ˣ ≃ Gal(ℚ(ζₙ)/ℚ) → Gal(F/ℚ)`, and
  `χ.primitiveCharacter (p : ℕ) = χ.val (σ_p)` for `χ ∈ Y` where `σ_p` is suitably interpreted.
* **B.2 — Cyclic-group character orthogonality (abstract):** for a finite abelian group `G`,
  subgroup `Y ⊆ Ĝ`, `g ∈ G`, `T : ℂ`:
  `∏ χ ∈ Y, (1 - χ(g) T) = (1 - T^d)^{|Y|/d}` where `d = ord(g) in G/Y^⊥`. The proof: each
  value `χ(g)` for `χ ∈ Y` is a `d`-th root of unity, with each root appearing `|Y|/d` times
  (Y → μ_d via χ ↦ χ(g) is surjective with kernel of index d). Then
  `∏_{ω ∈ μ_d} (1 - ω T) = 1 - T^d` (cyclotomic identity, see
  `Polynomial.X_pow_sub_one_eq_prod`).
* **B.3 — Inertia degree:** all primes `𝔭` above `p` in `𝓞 F` have the same inertia degree
  `f = ord(σ_p) in Gal(F/ℚ)/(I_𝔭)`; in particular, `absNorm 𝔭 = p^f`.
* **B.4 — Orbit count:** the number of primes above `p` is `|Y|/(e·f) = #(primesAboveOf F p)`,
  using the fundamental identity `e·f·g = [F:ℚ] = |Y|`.

Composing B.1–B.4 gives Step B.
-/

/-- **B.3 RHS reduction.** The product over primes above `p` in `𝓞 F` of the geometric local
factor `(1 - (absNorm 𝔭)^(-s))⁻¹` reduces, in a Galois extension, to a single factor raised to
the power `g = #(primesAboveOf F p)`, where the inertia degree `f = inertiaDegIn` is uniform
across primes above `p` (since they are all Galois-conjugate). -/
lemma prod_inertia_eq_pow_of_inertiaDegIn
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {s : ℂ}
    {p : ℕ} (hp : p.Prime) :
    ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ =
      ((1 - (p : ℂ) ^
          (-((Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) : ℂ) * s)))⁻¹) ^
        (primesAboveOf F p).card := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI hAG : IsAbelianGalois ℚ (F : Type _) := IsAbelianGalois.tower_bot ℚ F Kn
  haveI : IsGalois ℚ (F : Type _) := hAG.toIsGalois
  have hp_ne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by simp [hp.ne_zero]
  have h_unif : ∀ 𝔭 ∈ primesAboveOf F p,
      (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^
          (-((Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) : ℂ) * s)))⁻¹ := by
    intro 𝔭 h𝔭
    have h𝔭_in_set : 𝔭 ∈ Ideal.primesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
      have h_coe : 𝔭 ∈ ((IsDedekindDomain.primesOverFinset
          (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) : Finset _) : Set _) :=
        Finset.mem_coe.mpr h𝔭
      rwa [IsDedekindDomain.coe_primesOverFinset hp_ne] at h_coe
    haveI h𝔭_prime : 𝔭.IsPrime := h𝔭_in_set.1
    haveI h𝔭_lies : 𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := h𝔭_in_set.2
    -- absNorm 𝔭 = p ^ inertiaDeg
    have h_norm : Ideal.absNorm 𝔭 = p ^ ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg 𝔭) :=
      Ideal.absNorm_eq_pow_inertiaDeg' 𝔭 hp
    -- inertiaDeg = inertiaDegIn (Galois)
    have h_eq : (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg 𝔭 =
        Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) :=
      (Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span ({(p : ℤ)} : Set ℤ)) 𝔭 Gal(F/ℚ)).symm
    set f := Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F)
    rw [h_norm, h_eq]
    -- (p^f : ℕ : ℂ)^(-s) = (p:ℂ)^(-(f*s))
    have : ((p ^ f : ℕ) : ℂ) ^ (-s) = (p : ℂ) ^ (-((f : ℂ) * s)) := by
      rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
      congr 1; ring
    rw [this]
  rw [Finset.prod_congr rfl h_unif, Finset.prod_const]

/-! ### LHS reduction — Phase 2: restrict to coprime-conductor characters

Characters `χ ∈ Y` with `¬ p.Coprime χ.val.conductor` (equivalently `p ∣ conductor χ.val`, since
`p` is prime) have `χ.val.primitiveCharacter (p : ℕ) = 0`, contributing factor `(1 - 0)⁻¹ = 1` to
the product. So the product over all of `Y` equals the product over only the coprime-conductor
subset. This isolates the analytically nontrivial factors.
-/

/-- A primitive character vanishes at any natural number sharing a prime factor with the level. -/
private lemma DirichletCharacter.primitiveCharacter_eval_eq_zero
    {n : ℕ} (χ : DirichletCharacter ℂ n) {p : ℕ} (hp_dvd : p ∣ χ.conductor)
    (hp1 : 1 < p) :
    χ.primitiveCharacter (p : ℕ) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro h_coprime
  -- p | conductor and p coprime to conductor ⟹ p = 1, contra hp1.
  have h : p = 1 := Nat.eq_one_of_dvd_coprimes h_coprime (dvd_refl p) hp_dvd
  exact absurd h hp1.ne'

/-- **Phase 2.** Restriction to the coprime-conductor subset of Y. -/
private lemma prod_chars_eq_prod_coprime_conductor
    {n : ℕ} [NeZero n] (Y : Subgroup (DirichletCharacter ℂ n))
    {p : ℕ} (hp : p.Prime) (T : ℂ) :
    ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹ =
    ∏ χ ∈ (Finset.univ : Finset Y).filter (fun χ => p.Coprime χ.val.conductor),
      (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹ := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset Y)
        (fun χ : Y => p.Coprime χ.val.conductor)]
  -- Show second factor is 1.
  have h_not : ∀ χ ∈ (Finset.univ : Finset Y).filter
      (fun χ : Y => ¬ p.Coprime χ.val.conductor),
      (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹ = 1 := by
    intro χ hχ
    rw [Finset.mem_filter] at hχ
    have h_dvd : p ∣ χ.val.conductor := by
      have h := hχ.2
      rw [Nat.Prime.coprime_iff_not_dvd hp, not_not] at h
      exact h
    have h_zero : χ.val.primitiveCharacter (p : ℕ) = 0 :=
      DirichletCharacter.primitiveCharacter_eval_eq_zero χ.val h_dvd hp.one_lt
    rw [h_zero, zero_mul, sub_zero, inv_one]
  rw [Finset.prod_congr rfl h_not, Finset.prod_const_one, mul_one]

/-! ### LHS reduction — Phase 3: lift evaluation to a multiplicative hom

For χ ∈ Y with `p` coprime to `χ.val.conductor`, the value `χ.val.primitiveCharacter (p : ℕ)` is
nonzero (a root of unity). We construct a `MonoidHom` from the intersection subgroup
`Y ⊓ subgroupOfCoprimeConductor p` to `ℂˣ` whose value matches the primitive character
evaluation.

Multiplicativity in `χ` is proved at the lcm-level: for χ, ψ in the coprime-conductor subgroup,
`(χ·ψ).primitiveCharacter (p)` and `χ.primitiveCharacter (p) · ψ.primitiveCharacter (p)` agree
because they both arise from the same level-`m` character (where `m = lcm(conductor χ, conductor ψ)`,
coprime to `p`), differing by `changeLevel` lifts that are injective on level-`n` characters.
-/

open DirichletCharacter in
/-- For `c ∣ m` and `k` coprime to `m`, evaluating `changeLevel ξ` at the natural cast `(k : ZMod m)`
gives the same value as evaluating `ξ` at the natural cast `(k : ZMod c)`. -/
private lemma changeLevel_eval_natCast_of_coprime
    {c m : ℕ} [NeZero m] (h : c ∣ m) (ξ : DirichletCharacter ℂ c) {k : ℕ}
    (hk : k.Coprime m) :
    (DirichletCharacter.changeLevel h ξ) ((k : ℕ) : ZMod m) = ξ ((k : ℕ) : ZMod c) := by
  have hk_unit : IsUnit ((k : ℕ) : ZMod m) := by
    rw [ZMod.isUnit_iff_coprime]; exact hk
  rw [show ((k : ℕ) : ZMod m) = (hk_unit.unit : ZMod m) from (IsUnit.unit_spec _).symm]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  rw [IsUnit.unit_spec, ZMod.cast_natCast h]

open DirichletCharacter in
/-- For `χ, ψ : DirichletCharacter ℂ n` whose conductors are both coprime to `p`, the primitive
character of the product evaluates multiplicatively at `p`. -/
private lemma primitiveCharacter_mul_apply_of_coprime
    {n : ℕ} [NeZero n] (χ ψ : DirichletCharacter ℂ n) {p : ℕ}
    (hχ : p.Coprime χ.conductor) (hψ : p.Coprime ψ.conductor) :
    (χ * ψ).primitiveCharacter ((p : ℕ) : ZMod (χ * ψ).conductor) =
      χ.primitiveCharacter ((p : ℕ) : ZMod χ.conductor) *
      ψ.primitiveCharacter ((p : ℕ) : ZMod ψ.conductor) := by
  -- Set m = lcm of the two conductors.
  set m := χ.conductor.lcm ψ.conductor with hm_eq
  have hχ_m : χ.conductor ∣ m := Nat.dvd_lcm_left _ _
  have hψ_m : ψ.conductor ∣ m := Nat.dvd_lcm_right _ _
  have hχψ_m : (χ * ψ).conductor ∣ m := DirichletCharacter.conductor_mul_dvd_lcm_conductor χ ψ
  -- p coprime to m via the bound m ∣ χ.conductor * ψ.conductor.
  have hp_m : p.Coprime m :=
    (Nat.Coprime.mul_right hχ hψ).coprime_dvd_right (Nat.lcm_dvd_mul _ _)
  have hm_n : m ∣ n :=
    Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  -- m is nonzero since n is.
  haveI hm_ne : NeZero m := by
    refine ⟨fun h0 => ?_⟩
    rw [h0] at hm_n
    exact (NeZero.ne n) (Nat.eq_zero_of_zero_dvd hm_n)
  -- Identity at level m: lift to level n and apply changeLevel_injective.
  have h_id : DirichletCharacter.changeLevel hχψ_m (χ * ψ).primitiveCharacter =
      DirichletCharacter.changeLevel hχ_m χ.primitiveCharacter *
        DirichletCharacter.changeLevel hψ_m ψ.primitiveCharacter := by
    apply DirichletCharacter.changeLevel_injective hm_n
    rw [map_mul]
    rw [← DirichletCharacter.changeLevel_trans χ.primitiveCharacter hχ_m hm_n,
        ← DirichletCharacter.changeLevel_trans ψ.primitiveCharacter hψ_m hm_n,
        ← DirichletCharacter.changeLevel_trans (χ * ψ).primitiveCharacter hχψ_m hm_n,
        DirichletCharacter.changeLevel_primitiveCharacter,
        DirichletCharacter.changeLevel_primitiveCharacter,
        DirichletCharacter.changeLevel_primitiveCharacter]
  -- Evaluate at (p : ZMod m).
  rw [← changeLevel_eval_natCast_of_coprime hχψ_m _ hp_m,
      ← changeLevel_eval_natCast_of_coprime hχ_m _ hp_m,
      ← changeLevel_eval_natCast_of_coprime hψ_m _ hp_m,
      h_id, MulChar.mul_apply]

/-- The evaluation hom `Y_p → ℂˣ` given by `χ ↦ χ.val.primitiveCharacter (p : ℕ)`, well-defined
because the value is a nonzero root of unity for `χ` in the coprime-conductor subgroup, and
multiplicative by `primitiveCharacter_mul_apply_of_coprime`. -/
private noncomputable def evalAtPrime
    {n : ℕ} [NeZero n] (Y : Subgroup (DirichletCharacter ℂ n)) (p : ℕ) :
    ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p) →* ℂˣ where
  toFun χ := Units.mk0 (χ.val.primitiveCharacter (p : ℕ)) (by
    have h_coprime : p.Coprime χ.val.conductor :=
      DirichletCharacter.mem_subgroupOfCoprimeConductor.mp χ.property.2
    have h_unit : IsUnit ((p : ℕ) : ZMod χ.val.conductor) := by
      rw [ZMod.isUnit_iff_coprime]; exact h_coprime
    rw [← IsUnit.unit_spec h_unit, ← MulChar.coe_toUnitHom]
    exact Units.ne_zero _)
  map_one' := by
    apply Units.ext
    show (1 : DirichletCharacter ℂ n).primitiveCharacter ((p : ℕ) : ZMod _) = 1
    have hc : (1 : DirichletCharacter ℂ n).conductor = 1 := DirichletCharacter.conductor_one
    have h_subsingleton :
        Subsingleton (ZMod (1 : DirichletCharacter ℂ n).conductor) := by
      rw [hc]; infer_instance
    rw [DirichletCharacter.primitiveCharacter_one]
    exact MulChar.one_apply (@isUnit_of_subsingleton _ _ h_subsingleton _)
  map_mul' a b := by
    apply Units.ext
    show (a.val * b.val).primitiveCharacter ((p : ℕ) : ZMod _) =
      a.val.primitiveCharacter ((p : ℕ) : ZMod _) *
      b.val.primitiveCharacter ((p : ℕ) : ZMod _)
    have hχ : p.Coprime a.val.conductor :=
      DirichletCharacter.mem_subgroupOfCoprimeConductor.mp a.property.2
    have hψ : p.Coprime b.val.conductor :=
      DirichletCharacter.mem_subgroupOfCoprimeConductor.mp b.property.2
    exact primitiveCharacter_mul_apply_of_coprime a.val b.val hχ hψ

/-- The underlying complex value of `evalAtPrime χ` is `χ.val.primitiveCharacter (p : ℕ)`. -/
@[simp] private lemma evalAtPrime_val
    {n : ℕ} [NeZero n] {Y : Subgroup (DirichletCharacter ℂ n)} {p : ℕ}
    (χ : ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p)) :
    ((evalAtPrime Y p χ : ℂˣ) : ℂ) = χ.val.primitiveCharacter (p : ℕ) := rfl

/-! ### B.1 — Frobenius element and B.2 — evalAtPrime vs natCast eval

These sub-lemmas connect the prime evaluation map `evalAtPrime` to the Galois Frobenius
element `σ_p ∈ Gal(F/ℚ)` constructed from the canonical `galEquivZMod` isomorphism.
-/

/-- **B.1.** The Frobenius element `σ_p ∈ Gal(F/ℚ)` for a prime `p` coprime to `n`.
Constructed by applying the inverse of the `galEquivZMod` isomorphism to the canonical unit
`(p : (ZMod n)ˣ)` and restricting the resulting automorphism of `ℚ(ζₙ)` to `F`. -/
private noncomputable def frobeniusAt
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn)
    {p : ℕ} (hp : p.Coprime n) : Gal(F/ℚ) :=
  haveI : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  ((IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp)).restrictNormal F

/-- **B.2 (intermediate).** For `χ` in `Y ⊓ subgroupOfCoprimeConductor p` and `p` coprime to `n`,
the complex value of `evalAtPrime Y p χ` equals `χ.val` evaluated at the natural cast of `p` in
`ZMod n`.  The proof uses `changeLevel_primitiveCharacter` to lift `χ.val.primitiveCharacter`
back to level `n`, then `changeLevel_eval_natCast_of_coprime` to identify the evaluations. -/
private lemma evalAtPrime_eq_natCast
    {n : ℕ} [NeZero n] (Y : Subgroup (DirichletCharacter ℂ n))
    {p : ℕ} (hp_n : p.Coprime n)
    (χ : ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p)) :
    (evalAtPrime Y p χ : ℂ) = χ.val ((p : ℕ) : ZMod n) := by
  simp only [evalAtPrime_val]
  -- χ.val.primitiveCharacter (p:ℕ) = χ.val ((p:ℕ) : ZMod n)
  -- via: χ.val = changeLevel h χ.val.primitiveCharacter  (changeLevel_primitiveCharacter)
  -- and: (changeLevel h prim) ((p:ZMod n)) = prim ((p:ZMod c))  (changeLevel_eval_natCast_of_coprime)
  rw [show χ.val ((p : ℕ) : ZMod n) =
      (DirichletCharacter.changeLevel χ.val.conductor_dvd_level
        χ.val.primitiveCharacter) ((p : ℕ) : ZMod n) from by
    rw [DirichletCharacter.changeLevel_primitiveCharacter]]
  exact (changeLevel_eval_natCast_of_coprime χ.val.conductor_dvd_level
    χ.val.primitiveCharacter hp_n).symm

/-- **B.2 (Galois form).** For `χ` in `Y ⊓ subgroupOfCoprimeConductor p` and `p` coprime to `n`,
the complex value of `evalAtPrime Y p χ` equals `χ.val` evaluated at the unit class of `p` in
`(ZMod n)ˣ`, viewed via the `galEquivZMod` round-trip. This connects the analytic prime
evaluation to the Galois-theoretic evaluation at the Frobenius preimage in `Gal(Kn/ℚ)`. -/
private lemma evalAtPrime_eq_eval_galois
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (Y : Subgroup (DirichletCharacter ℂ n))
    {p : ℕ} (hp_n : p.Coprime n)
    (χ : ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p)) :
    (evalAtPrime Y p χ : ℂ) =
      χ.val (IsCyclotomicExtension.Rat.galEquivZMod n Kn
        ((IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm
          (ZMod.unitOfCoprime p hp_n)) : ZMod n) := by
  rw [evalAtPrime_eq_natCast Y hp_n χ, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime]

/-! ### B.3–B.4: Frobenius-in-stabilizer sub-lemmas

These helper lemmas show that the canonical Frobenius element `σ₀ = (galEquivZMod)⁻¹(p mod n)`
lies in the stabilizer of `P` under `Gal(Kn/ℚ)` (B.3), that `algebraMap (𝓞 F → 𝓞 Kn)` is
equivariant under `restrictNormal` (B.4a), and that the restriction `frobeniusAt F hp_n` lies
in the stabilizer of `P_F = P.comap` under `Gal(F/ℚ)` (B.4b). -/

section FrobeniusStabilizer

open scoped Pointwise

/-- **B.3.** The element σ₀ = `(galEquivZMod n Kn).symm (unitOfCoprime p hp_n)` lies in
the stabilizer of `P` under `Gal(Kn/ℚ)`. Derived from `galEquivZMod_stabilizer`. -/
private lemma sigma0_mem_stabilizer
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    {p : ℕ} [hp : Fact (Nat.Prime p)] (hp_n : p.Coprime n)
    (P : Ideal (𝓞 Kn)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp_n) ∈
        MulAction.stabilizer Gal(Kn/ℚ) P := by
  have hmem : ZMod.unitOfCoprime p hp_n ∈
      (IsCyclotomicExtension.Rat.galEquivZMod n Kn).mapSubgroup
        (MulAction.stabilizer Gal(Kn/ℚ) P) :=
    (IsCyclotomicExtension.Rat.galEquivZMod_stabilizer n Kn p P hp_n) ▸ Subgroup.mem_zpowers _
  rw [MulEquiv.mapSubgroup_apply, Subgroup.mem_map] at hmem
  obtain ⟨σ, hσ_mem, hσ_eq⟩ := hmem
  rwa [show (IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm
        (ZMod.unitOfCoprime p hp_n) = σ from
    (IsCyclotomicExtension.Rat.galEquivZMod n Kn).injective
      (hσ_eq.symm ▸ (MulEquiv.apply_symm_apply _ _))]

/-- **B.4a.** The map `algebraMap (𝓞 F → 𝓞 Kn)` is equivariant under `restrictNormal`:
`algebraMap(σ|_F • x) = σ • algebraMap(x)` for `σ : Gal(Kn/ℚ)`, `x : 𝓞 F`. -/
private lemma algebraMap_restrictNormal_smul_compat
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (σ₀ : Gal(Kn/ℚ)) (x : 𝓞 F) :
    haveI : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
    algebraMap (𝓞 F) (𝓞 Kn) (σ₀.restrictNormal F • x) = σ₀ • algebraMap (𝓞 F) (𝓞 Kn) x := by
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  ext
  simp only [NumberField.RingOfIntegers.coe_eq_algebraMap]
  have rhs_eq : (algebraMap (𝓞 Kn) Kn) (σ₀ • (algebraMap (𝓞 F) (𝓞 Kn)) x) =
      σ₀ ((algebraMap (𝓞 Kn) Kn) ((algebraMap (𝓞 F) (𝓞 Kn)) x)) := by
    have h := algebraMap.coe_smul' σ₀ (algebraMap (𝓞 F) (𝓞 Kn) x) Kn
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, AlgEquiv.smul_def] at h; exact h
  rw [rhs_eq, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 Kn) Kn,
      ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 Kn) Kn,
      IsScalarTower.algebraMap_apply (𝓞 F) F Kn, IsScalarTower.algebraMap_apply (𝓞 F) F Kn]
  have htau : (algebraMap (𝓞 F) F) (σ₀.restrictNormal F • x) =
      (σ₀.restrictNormal F) ((algebraMap (𝓞 F) F) x) := by
    have h := algebraMap.coe_smul' (σ₀.restrictNormal F) x F
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, AlgEquiv.smul_def] at h
    exact h.symm
  rw [htau, AlgEquiv.restrictNormal_commutes σ₀ F (algebraMap (𝓞 F) F x)]

/-- **B.4b.** The Frobenius element `frobeniusAt F hp_n = σ₀|_F` lies in the stabilizer
of `P_F = P.comap(algebraMap (𝓞 F) (𝓞 Kn))` under `Gal(F/ℚ)`. -/
private lemma frobeniusAt_mem_stabilizer_PF
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {p : ℕ} [hp : Fact (Nat.Prime p)] (hp_n : p.Coprime n)
    (P : Ideal (𝓞 Kn)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    haveI : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
    let σ₀ := (IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp_n)
    σ₀.restrictNormal F ∈
      MulAction.stabilizer Gal(F/ℚ) (P.comap (algebraMap (𝓞 F) (𝓞 Kn))) := by
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  let σ₀ : Gal(Kn/ℚ) :=
    (IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp_n)
  have hσ₀_stab : σ₀ ∈ MulAction.stabilizer Gal(Kn/ℚ) P :=
    sigma0_mem_stabilizer hp_n P
  rw [MulAction.mem_stabilizer_iff] at hσ₀_stab ⊢
  ext x
  simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  let τ_inv : Gal(Kn/ℚ) := σ₀⁻¹
  have hkey : algebraMap (𝓞 F) (𝓞 Kn) ((σ₀.restrictNormal F)⁻¹ • x) =
      τ_inv • algebraMap (𝓞 F) (𝓞 Kn) x := by
    rw [show (σ₀.restrictNormal F)⁻¹ = τ_inv.restrictNormal F from
      (map_inv (AlgEquiv.restrictNormalHom F) σ₀).symm]
    exact algebraMap_restrictNormal_smul_compat (n := n) (Kn := Kn) F τ_inv x
  rw [hkey, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hσ₀_stab]

end FrobeniusStabilizer

section OrderOfFrobenius

open scoped Pointwise
open IsCyclotomicExtension.Rat IntermediateField

/-- Helper: `F.fixingSubgroup` is a Galois group for `F' / L'` whenever `L'/K'` is Galois.
Wraps `IsGaloisGroup.intermediateField` to avoid `(L := ...)` named argument clash with
the `L` LSeries notation opened file-wide by `open scoped LSeries.notation`. -/
private lemma isGaloisGroup_fixingSubgroup
    {K' L' : Type*} [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L']
    [FiniteDimensional K' L']
    (F' : IntermediateField K' L') :
    IsGaloisGroup F'.fixingSubgroup F' L' := by
  apply IsGaloisGroup.subgroup_iff.mpr
  exact IsGalois.fixedField_fixingSubgroup (K := F')

/-- **B.5 helper.** The stabilizer of `P` under `Gal(Kn/ℚ)` equals the cyclic subgroup generated
by `σ₀ = (galEquivZMod n Kn).symm (unitOfCoprime p hp_n)`. Derived from `galEquivZMod_stabilizer`
by conjugating with `MulEquiv.mapSubgroup`. -/
private lemma stabilizer_eq_zpowers_sigma0
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn]
    {p : ℕ} [hp : Fact (Nat.Prime p)] (hp_n : p.Coprime n)
    (P : Ideal (𝓞 Kn)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    MulAction.stabilizer Gal(Kn/ℚ) P =
      Subgroup.zpowers ((galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp_n)) := by
  conv_lhs =>
    rw [show MulAction.stabilizer Gal(Kn/ℚ) P =
      (MulEquiv.mapSubgroup (galEquivZMod n Kn)).symm
        ((MulEquiv.mapSubgroup (galEquivZMod n Kn)) (MulAction.stabilizer Gal(Kn/ℚ) P)) from
      ((MulEquiv.mapSubgroup (galEquivZMod n Kn)).left_inv _).symm]
  rw [galEquivZMod_stabilizer n Kn p P hp_n, MulEquiv.symm_mapSubgroup,
    MulEquiv.coe_mapSubgroup, MonoidHom.map_zpowers]
  simp

attribute [local instance] Ideal.Quotient.field in
/-- **B.5.** The order of the Frobenius element `frobeniusAt F hp_n = σ₀|_F` in `Gal(F/ℚ)`
equals the inertia degree `inertiaDegIn(p, 𝓞 F)`, for any prime `p` coprime to `n`. -/
private lemma orderOf_restrictNormal_eq_inertiaDegIn
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {p : ℕ} [hp : Fact (Nat.Prime p)] (hp_n : p.Coprime n)
    (P : Ideal (𝓞 Kn)) [hPmax : P.IsMaximal] [hPover : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    haveI : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
    orderOf ((IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp_n)
              |>.restrictNormal F) =
      Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  haveI hKnGal : IsGalois ℚ Kn := IsCyclotomicExtension.isGalois {n} ℚ Kn
  let σ₀ : Gal(Kn/ℚ) := (galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp_n)
  let PF := P.comap (algebraMap (𝓞 F) (𝓞 Kn))
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp_ideal_ne_bot : p_ideal ≠ ⊥ := by
    simp only [p_ideal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  haveI hP_liesover_PF : P.LiesOver PF := inferInstance
  haveI h_PF_max : PF.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hPF_ne_bot : PF ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h_PF_max (RingOfIntegers.not_isField F)
  have hstab : MulAction.stabilizer Gal(Kn/ℚ) P = Subgroup.zpowers σ₀ :=
    stabilizer_eq_zpowers_sigma0 hp_n P
  have h_ord_σ₀ : orderOf σ₀ = p_ideal.inertiaDegIn (𝓞 Kn) := by
    have hcard_stab := Ideal.card_stabilizer_eq (G := Gal(Kn/ℚ)) p_ideal hp_ideal_ne_bot P
    rw [← Nat.card_zpowers, ← hstab, hcard_stab,
      IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p Kn
        ((Nat.Prime.coprime_iff_not_dvd hp.out).mp hp_n),
      one_mul]
  have h_relIndex : F.fixingSubgroup.relIndex (Subgroup.zpowers σ₀) =
      orderOf (σ₀.restrictNormal F) := by
    have key := Subgroup.relIndex_ker (f := AlgEquiv.restrictNormalHom F)
      (K := Subgroup.zpowers σ₀)
    have hker : (AlgEquiv.restrictNormalHom F).ker = F.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker F
    rw [hker, MonoidHom.map_zpowers, Nat.card_zpowers] at key
    exact key
  have h_card_eq : Nat.card (F.fixingSubgroup.subgroupOf (Subgroup.zpowers σ₀)) *
      orderOf (σ₀.restrictNormal F) = orderOf σ₀ := by
    rw [← h_relIndex, ← Nat.card_zpowers]
    exact (F.fixingSubgroup.subgroupOf (Subgroup.zpowers σ₀)).card_mul_index
  haveI hGalFKn : IsGaloisGroup F.fixingSubgroup F Kn :=
    isGaloisGroup_fixingSubgroup F
  letI hmsa : MulSemiringAction (↥F.fixingSubgroup) Kn := inferInstance
  letI hsd : SMulDistribClass (↥F.fixingSubgroup) (𝓞 Kn) Kn := inferInstance
  haveI hGalFKn_oi : IsGaloisGroup F.fixingSubgroup (𝓞 F) (𝓞 Kn) :=
    IsGaloisGroup.of_isFractionRing F.fixingSubgroup (𝓞 F) (𝓞 Kn) F Kn
  have h_inter_card : Nat.card (F.fixingSubgroup.subgroupOf (Subgroup.zpowers σ₀)) =
      Nat.card (MulAction.stabilizer F.fixingSubgroup P) := by
    apply Nat.card_congr
    exact {
      toFun := fun ⟨⟨σ, hσ_zpow⟩, hσ_fix⟩ => ⟨⟨σ, hσ_fix⟩, by
        rw [MulAction.mem_stabilizer_iff]
        have hmem : σ ∈ MulAction.stabilizer Gal(Kn/ℚ) P := hstab ▸ hσ_zpow
        rw [MulAction.mem_stabilizer_iff] at hmem
        exact_mod_cast hmem⟩
      invFun := fun ⟨⟨σ, hσ_fix⟩, hσ_stab⟩ => ⟨⟨σ, by
        rw [← hstab]
        rw [MulAction.mem_stabilizer_iff]
        rw [MulAction.mem_stabilizer_iff] at hσ_stab
        exact_mod_cast hσ_stab⟩, hσ_fix⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  have h_stab_F_card : Nat.card (MulAction.stabilizer F.fixingSubgroup P) =
      PF.ramificationIdxIn (𝓞 Kn) * PF.inertiaDegIn (𝓞 Kn) :=
    Ideal.card_stabilizer_eq (G := F.fixingSubgroup) PF hPF_ne_bot P
  have h_ramIdx_PF : PF.ramificationIdxIn (𝓞 Kn) = 1 := by
    have htower : p_ideal.ramificationIdxIn (𝓞 F) * PF.ramificationIdxIn (𝓞 Kn) =
        p_ideal.ramificationIdxIn (𝓞 Kn) :=
      Ideal.ramificationIdxIn_mul_ramificationIdxIn' PF
        (G := Gal(F/ℚ)) (GAC := Gal(Kn/ℚ)) (GBC := F.fixingSubgroup) (𝓞 Kn)
    rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p Kn
        ((Nat.Prime.coprime_iff_not_dvd hp.out).mp hp_n)] at htower
    have h1 : p_ideal.ramificationIdxIn (𝓞 F) ≠ 0 :=
      Ideal.ramificationIdxIn_ne_zero (G := Gal(F/ℚ)) hp_ideal_ne_bot
    have h2 : PF.ramificationIdxIn (𝓞 Kn) ≠ 0 :=
      Ideal.ramificationIdxIn_ne_zero (G := F.fixingSubgroup) hPF_ne_bot
    nlinarith [Nat.one_le_iff_ne_zero.mpr h1, Nat.one_le_iff_ne_zero.mpr h2]
  have h_tower : p_ideal.inertiaDegIn (𝓞 F) * PF.inertiaDegIn (𝓞 Kn) =
      p_ideal.inertiaDegIn (𝓞 Kn) :=
    Ideal.inertiaDegIn_mul_inertiaDegIn p_ideal PF
      (G := Gal(F/ℚ)) (GAC := Gal(Kn/ℚ)) (GBC := F.fixingSubgroup) (𝓞 Kn)
  have h_inter_eq : Nat.card (F.fixingSubgroup.subgroupOf (Subgroup.zpowers σ₀)) =
      PF.inertiaDegIn (𝓞 Kn) := by
    rw [h_inter_card, h_stab_F_card, h_ramIdx_PF, one_mul]
  rw [h_inter_eq, h_ord_σ₀] at h_card_eq
  have hPF_ine : PF.inertiaDegIn (𝓞 Kn) ≠ 0 :=
    Ideal.inertiaDegIn_ne_zero (G := F.fixingSubgroup)
  have h_mul_eq : PF.inertiaDegIn (𝓞 Kn) * orderOf (σ₀.restrictNormal F) =
      PF.inertiaDegIn (𝓞 Kn) * p_ideal.inertiaDegIn (𝓞 F) := by
    rw [h_card_eq]
    linarith [h_tower, Nat.mul_comm (p_ideal.inertiaDegIn (𝓞 F)) (PF.inertiaDegIn (𝓞 Kn))]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hPF_ine) h_mul_eq

end OrderOfFrobenius


/-- Auxiliary: `Nat.divMaxPow n p` divides `n`.
Follows from `Nat.divMaxPow n p * p ^ padicValNat p n = n`. -/
private lemma divMaxPow_dvd' (n p : ℕ) : Nat.divMaxPow n p ∣ n :=
  ⟨p ^ padicValNat p n, (Nat.divMaxPow_mul_pow_padicValNat p n).symm⟩

/-- **A.1.** A Dirichlet character χ of level n belongs to `subgroupOfCoprimeConductor p`
(equivalently: conductor of χ is coprime to p) if and only if χ is trivial on the kernel
of the natural unit-group map `(ZMod n)ˣ → (ZMod (Nat.divMaxPow n p))ˣ`.

The proof chains: `p.Coprime χ.conductor ↔ χ.conductor ∣ Nat.divMaxPow n p`
(using that `divMaxPow n p` is the p'-part of n) then applies
`DirichletCharacter.factorsThrough_iff_ker_unitsMap`. -/
private lemma subgroupOfCoprimeConductor_iff_trivial_on_unitsMap_ker
    {n : ℕ} [NeZero n] {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ n) :
    χ ∈ DirichletCharacter.subgroupOfCoprimeConductor p ↔
      ∀ u ∈ (ZMod.unitsMap (divMaxPow_dvd' n p)).ker, χ.toUnitHom u = 1 := by
  rw [DirichletCharacter.mem_subgroupOfCoprimeConductor]
  -- Step 1: p.Coprime χ.conductor ↔ χ.conductor ∣ Nat.divMaxPow n p
  have h_key : p.Coprime χ.conductor ↔ χ.conductor ∣ Nat.divMaxPow n p := by
    constructor
    · intro h_cop
      have h_ndvd : ¬p ∣ χ.conductor := hp.coprime_iff_not_dvd.mp h_cop
      have h_cop2 : Nat.Coprime χ.conductor (p ^ padicValNat p n) :=
        hp.coprime_pow_of_not_dvd h_ndvd
      have h_dvd_mp : χ.conductor ∣ Nat.divMaxPow n p * p ^ padicValNat p n :=
        (Nat.divMaxPow_mul_pow_padicValNat p n).symm ▸ χ.conductor_dvd_level
      exact h_cop2.dvd_mul_right.mp h_dvd_mp
    · intro h_dvd
      refine hp.coprime_iff_not_dvd.mpr ?_
      exact fun h_pdvd =>
        Nat.not_dvd_divMaxPow hp.one_lt (NeZero.ne n) (h_pdvd.trans h_dvd)
  -- Step 2: chain through conductorSet and factorsThrough
  rw [h_key,
      ← DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ (divMaxPow_dvd' n p),
      DirichletCharacter.mem_conductorSet_iff χ,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap (divMaxPow_dvd' n p)]
  simp [SetLike.le_def, MonoidHom.mem_ker]

/-- **A.2.** The cardinality of `subgroupOfCoprimeConductor p` equals the index of the
kernel of `ZMod.unitsMap (Nat.divMaxPow n p ∣ n)` in `(ZMod n)ˣ`, i.e. the order of the
image of `(ZMod n)ˣ → (ZMod (Nat.divMaxPow n p))ˣ`.

Proof: by A.1 the subgroup equals the Pontryagin dual of `(ZMod.unitsMap _).ker`, so its
cardinality equals the index by `MulChar.card_subgroupOrderIsoSubgroupMulChar`. -/
private lemma card_subgroupOfCoprimeConductor_eq_quotient
    {n : ℕ} [NeZero n] {p : ℕ} (hp : p.Prime)
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod n)ˣ)] :
    Nat.card (DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := n) p) =
      Nat.card ((ZMod n)ˣ ⧸ (ZMod.unitsMap (divMaxPow_dvd' n p)).ker) := by
  have h_sg_eq : DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := n) p =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ
        (ZMod.unitsMap (divMaxPow_dvd' n p)).ker).ofDual := by
    ext χ
    rw [subgroupOfCoprimeConductor_iff_trivial_on_unitsMap_ker hp χ,
        MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    simp only [← MulChar.coe_toUnitHom, Units.val_eq_one]
  rw [h_sg_eq]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar
/-- **R2.** The cardinality of the inertia group of `Gal(F/ℚ)` at a prime `PF` of `𝓞 F` above `p`
equals the ramification index of `p` in `𝓞 F`.

This is a thin wrapper around `Ideal.card_inertia_eq_ramificationIdxIn`, specialized to the
setting of an intermediate field `F` of a cyclotomic abelian extension `Kn/ℚ`. -/
private lemma card_inertia_in_F_eq_ramificationIdxIn
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {p : ℕ} [hpFact : Fact p.Prime]
    (PF : Ideal (𝓞 F)) [hPFmax : PF.IsMaximal]
    [hPFlies : PF.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    haveI : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
    Nat.card (PF.inertia Gal(F/ℚ)) =
      Ideal.ramificationIdxIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  haveI hGalFQ : IsGaloisGroup Gal(F/ℚ) ℚ F := IsGaloisGroup.of_isGalois ℚ F
  haveI hGalFZ : IsGaloisGroup Gal(F/ℚ) ℤ (𝓞 F) := inferInstance
  have hp := hpFact.out
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp_ideal_ne_bot : p_ideal ≠ ⊥ := by
    simp only [p_ideal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hPF_ne_bot : PF ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPFmax (RingOfIntegers.not_isField F)
  letI hFieldZ : Field (ℤ ⧸ p_ideal) := Ideal.Quotient.field _
  letI hFieldF : Field (𝓞 F ⧸ PF) := Ideal.Quotient.field _
  haveI h_isSep : Algebra.IsSeparable (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF) := by
    haveI : Finite (𝓞 F ⧸ PF) := Ring.HasFiniteQuotients.finiteQuotient hPF_ne_bot
    haveI : Finite (ℤ ⧸ p_ideal) := inferInstance
    haveI : PerfectField (ℤ ⧸ p_ideal) := inferInstance
    haveI : Module.Finite (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF) :=
      (Module.finite_iff_finite (R := ℤ ⧸ p_ideal)).mpr ‹_›
    haveI : Algebra.IsAlgebraic (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF) :=
      Algebra.IsAlgebraic.of_finite (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF)
    exact inferInstance
  exact Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(F/ℚ)) p_ideal hp_ideal_ne_bot PF

/-- **R1.** The image of the inertia group `P.inertia Gal(Kn/ℚ)` under the canonical isomorphism
`galEquivZMod n Kn : Gal(Kn/ℚ) ≃* (ZMod n)ˣ` equals the kernel of the projection
`ZMod.unitsMap (Nat.divMaxPow n p ∣ n) : (ZMod n)ˣ → (ZMod m)ˣ`
where `m = Nat.divMaxPow n p` is the p'-part of n.

**Proof:** ⊆ follows from the action of inertia on a primitive m-th root of unity mod P
(using IsPrimitiveRoot.idealQuotient_mk + pow_inj_mod). The reverse inclusion follows by
cardinality: |ker| = φ(n)/φ(m) = φ(p^v) = ramificationIdxIn p Kn = |inertia|. -/
private lemma galEquivZMod_mapSubgroup_inertia_eq_kernel
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [hKn : IsCyclotomicExtension {n} ℚ Kn]
    (p : ℕ) [hp : Fact p.Prime]
    (P : Ideal (𝓞 Kn)) [hPmax : P.IsMaximal]
    [hPlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsCyclotomicExtension.Rat.galEquivZMod n Kn).mapSubgroup (P.inertia Gal(Kn/ℚ)) =
      (ZMod.unitsMap (divMaxPow_dvd' n p)).ker := by
  classical
  haveI hGalKn : IsGalois ℚ Kn := IsCyclotomicExtension.isGalois {n} ℚ Kn
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  let m := Nat.divMaxPow n p
  let v := padicValNat p n
  have hm_dvd : m ∣ n := divMaxPow_dvd' n p
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
    let k := (IsCyclotomicExtension.Rat.galEquivZMod n Kn σ).val.val
    have hsmul : σ • ζm = ζm ^ k :=
      IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq n Kn σ hζm_pow_n
    have hmem_P : σ • ζm - ζm ∈ P := AddSubgroup.mem_inertia.mp hσ_inertia ζm
    have hmap_eq : (Ideal.Quotient.mk P ζm) ^ k = (Ideal.Quotient.mk P ζm) ^ 1 := by
      rw [pow_one, ← map_pow, ← hsmul]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hmem_P
    -- k ≡ 1 (mod m) by primitivity
    have hk_mod : k % m = 1 % m := by
      have h := (hζm_prim_mod.isOfFinOrder (NeZero.ne m)).pow_inj_mod.mp hmap_eq
      rwa [← hζm_prim_mod.eq_orderOf] at h
    -- Conclude unitsMap = 1: (galEquivZMod σ).val.val % m = 1 % m implies unitsMap = 1
    rw [Units.ext_iff, ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val]
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' k 1 m).mpr hk_mod
  · -- card inequality: |ker(unitsMap)| ≤ |image of inertia|
    -- Both equal ramificationIdxIn p Kn
    rw [Subgroup.card_mapSubgroup]
    -- |image| = |inertia| = ramificationIdxIn
    -- First, set up instances for card_inertia_eq_ramificationIdxIn
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
      -- First isomorphism: |ker| * φ(m) = φ(n)
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
      -- ramificationIdxIn * φ(m) = φ(n)
      have hram_tot : Ideal.ramificationIdxIn p_ideal (𝓞 Kn) * Nat.totient m =
          Nat.totient n := by
        rcases Nat.eq_zero_or_pos v with hv | hv
        · -- v = 0: p ∤ n, ramification = 1, n = m
          have hn_eq_m : n = m := by
            have : p ^ v = 1 := by rw [hv, pow_zero]
            rw [hn_eq, this, one_mul]
          rw [← hn_eq_m]
          have hram1 : Ideal.ramificationIdxIn p_ideal (𝓞 Kn) = 1 :=
            IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p Kn (hn_eq_m ▸ hm_ndvd)
          simp [hram1]
        · -- v ≥ 1
          obtain ⟨k', hv_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hv)
          have hn_eq' : n = p ^ (k' + 1) * m := by rw [hn_eq, hv_eq]
          have hram : Ideal.ramificationIdxIn p_ideal (𝓞 Kn) = p ^ k' * (p - 1) :=
            IsCyclotomicExtension.Rat.ramificationIdxIn_eq n Kn hn_eq' hm_ndvd
          have hcop : Nat.Coprime (p ^ (k' + 1)) m :=
            Nat.Coprime.pow_left _ (hp.out.coprime_iff_not_dvd.mpr hm_ndvd)
          rw [hram, hn_eq', Nat.totient_mul hcop, Nat.totient_prime_pow_succ hp.out]
      -- Conclude |ker| = ramification
      exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr (NeZero.pos m))
        (hfirst_iso.trans hram_tot.symm)
    linarith [hcard_inertia, hcard_ker]

section R4

open scoped Pointwise

/-- **R4.** The order of the Frobenius modulo inertia: for any prime `PF` of `𝓞 F` above `p`,
the cardinality of the decomposition group divided by the cardinality of the inertia group equals
the inertia degree.

**Proof:** `card_stabilizer_eq` gives `|stab| = e * f`; `card_inertia_in_F_eq_ramificationIdxIn`
(R2) gives `|inertia| = e`; so `|stab| / |inertia| = e * f / e = f`. -/
private lemma orderOf_decompositionRep_mod_inertia
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 Kn)) [hPmax : P.IsMaximal]
    [hPover : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    haveI : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
    Nat.card (MulAction.stabilizer Gal(F/ℚ) (P.comap (algebraMap (𝓞 F) (𝓞 Kn)))) /
      Nat.card ((P.comap (algebraMap (𝓞 F) (𝓞 Kn))).inertia Gal(F/ℚ)) =
        Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  haveI hGalFQ : IsGaloisGroup Gal(F/ℚ) ℚ F := IsGaloisGroup.of_isGalois ℚ F
  haveI hGalFZ : IsGaloisGroup Gal(F/ℚ) ℤ (𝓞 F) := inferInstance
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp_ideal_ne_bot : p_ideal ≠ ⊥ := by
    simp only [p_ideal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  let PF := P.comap (algebraMap (𝓞 F) (𝓞 Kn))
  haveI h_PF_max : PF.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hPF_ne_bot : PF ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h_PF_max (RingOfIntegers.not_isField F)
  letI hFieldZ : Field (ℤ ⧸ p_ideal) := Ideal.Quotient.field _
  letI hFieldF : Field (𝓞 F ⧸ PF) := Ideal.Quotient.field _
  haveI h_isSep : Algebra.IsSeparable (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF) := by
    haveI : Finite (𝓞 F ⧸ PF) := Ring.HasFiniteQuotients.finiteQuotient hPF_ne_bot
    haveI : Finite (ℤ ⧸ p_ideal) := inferInstance
    haveI : PerfectField (ℤ ⧸ p_ideal) := inferInstance
    haveI : Module.Finite (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF) :=
      (Module.finite_iff_finite (R := ℤ ⧸ p_ideal)).mpr ‹_›
    haveI : Algebra.IsAlgebraic (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF) :=
      Algebra.IsAlgebraic.of_finite (ℤ ⧸ p_ideal) (𝓞 F ⧸ PF)
    exact inferInstance
  -- |stabilizer| = e * f
  have h_stab : Nat.card (MulAction.stabilizer Gal(F/ℚ) PF) =
      p_ideal.ramificationIdxIn (𝓞 F) * p_ideal.inertiaDegIn (𝓞 F) :=
    Ideal.card_stabilizer_eq (G := Gal(F/ℚ)) p_ideal hp_ideal_ne_bot PF
  -- |inertia| = e (by R2)
  haveI h_PF_liesover : PF.LiesOver p_ideal := inferInstance
  have h_inertia : Nat.card (PF.inertia Gal(F/ℚ)) =
      Ideal.ramificationIdxIn p_ideal (𝓞 F) :=
    card_inertia_in_F_eq_ramificationIdxIn (n := n) (Kn := Kn) F PF
  -- e ≠ 0
  have he_ne_zero : p_ideal.ramificationIdxIn (𝓞 F) ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (G := Gal(F/ℚ)) hp_ideal_ne_bot
  -- |stab| / |inertia| = e * f / e = f
  rw [h_stab, h_inertia, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he_ne_zero)]

end R4

/-! ### Lemma A.3 — cardinality of `Y ⊓ subgroupOfCoprimeConductor p`

The intersection of the character subgroup `Y` with the coprime-conductor subgroup `Y_p`
has cardinality `|Y| / e` where `e` is the ramification index of `p` in `𝓞 F`.

**Proof sketch (Pontryagin duality):**

1. Identify `Y = (subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ H_F_map).ofDual`
   where `H_F_map = (galEquivZMod n Kn).mapSubgroup F.fixingSubgroup`.
   This follows directly from the definition `intermediateFieldEquivSubgroupChar =
   IsGalois.intermediateFieldEquivSubgroup.trans (subgroupGalEquivSubgroupChar.dual.trans dualDual⁻¹)`.

2. Identify `subgroupOfCoprimeConductor p = (subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ I_p).ofDual`
   where `I_p = (ZMod.unitsMap (m_dvd_n : Nat.divMaxPow n p ∣ n)).ker`.
   This follows from `mem_subgroupOfCoprimeConductor` + `factorsThrough_iff_ker_unitsMap` +
   `mem_subgroupOrderIsoSubgroupMulChar_iff`.

3. Apply the anti-isomorphism's lattice law (via `OrderIso.map_sup` in the dual order):
   `Y ⊓ Y_p = (subgroupOrderIsoSubgroupMulChar ... (H_F_map ⊔ I_p)).ofDual`

4. Apply `card_subgroupOrderIsoSubgroupMulChar`:
   `Nat.card (Y ⊓ Y_p) = Nat.card ((ZMod n)ˣ ⧸ (H_F_map ⊔ I_p))`

5. Reduce `|(ZMod n)ˣ ⧸ (H_F_map ⊔ I_p)| = |Y|/e` using the
   `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` identity for `F` and the
   second-isomorphism identification of `H_F_map ⊔ I_p` with `e * |H_F_map|`
   (the inertia group `I_p^F ≅ I_p/(H_F_map ∩ I_p)` of `p` in `F` has order `e`).
-/

/-- **A.3.** The cardinality of `Y ⊓ subgroupOfCoprimeConductor p` equals `|Y|` divided
by the ramification index `e = ramificationIdxIn p (𝓞 F)`.

The proof proceeds via Pontryagin duality:
- Identify `Y` and `subgroupOfCoprimeConductor p` as dual subgroups of subgroups of `(ZMod n)ˣ`
  under `MulChar.subgroupOrderIsoSubgroupMulChar`.
- Use the anti-isomorphism's sup/inf exchange: intersection = dual of join.
- Apply `card_subgroupOrderIsoSubgroupMulChar` to get the quotient cardinality.
- Identify the quotient cardinality as `|Y|/e` via R1 (inertia identification) + R2 (cardinality).

Proof sub-steps:
- `hYp_eq`: `subgroupOfCoprimeConductor p = dual of (ZMod.unitsMap hm_dvd).ker`
  via `factorsThrough_iff_ker_unitsMap` + the `Nat.Coprime.conductor_dvd` chain.
- `hY_eq`: `Y = dual of (galEquivZMod n Kn).mapSubgroup F.fixingSubgroup` via
  `mem_intermediateFieldEquivSubgroupChar_iff`.
- `hInter`: intersection of duals = dual of sup, via `OrderIso.map_sup` in the dual order.
- Sub-step E: Use R1 + relIndex chain + first iso to identify
  `|(ZMod n)ˣ ⧸ (H_map ⊔ I_p)| = |Y| / ramificationIdxIn p (𝓞 F)`.
-/
private lemma card_inter_Y_subgroupOfCoprimeConductor
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {p : ℕ} (hp : p.Prime) :
    Nat.card (↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p)) =
      Nat.card Y / Ideal.ramificationIdxIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
  -- H_map: image of F.fixingSubgroup in (ZMod n)ˣ under galEquivZMod.
  let H_map := (IsCyclotomicExtension.Rat.galEquivZMod n Kn).mapSubgroup F.fixingSubgroup
  -- hm_dvd: Nat.divMaxPow n p divides n (n = p^k * divMaxPow n p).
  have hm_dvd : Nat.divMaxPow n p ∣ n :=
    ⟨p ^ padicValNat p n, (Nat.divMaxPow_mul_pow_padicValNat p n).symm⟩
  haveI hm_ne : NeZero (Nat.divMaxPow n p) :=
    ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) hm_dvd⟩
  -- I_p: kernel of ZMod.unitsMap (Nat.divMaxPow n p ∣ n) in (ZMod n)ˣ.
  let I_p := (ZMod.unitsMap hm_dvd).ker
  -- Sub-step A: subgroupOfCoprimeConductor p = dual of I_p under
  -- subgroupOrderIsoSubgroupMulChar.
  have hYp_eq : DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := n) p =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ I_p).ofDual := by
    rw [show I_p = (ZMod.unitsMap (divMaxPow_dvd' n p)).ker from rfl]
    ext χ
    rw [subgroupOfCoprimeConductor_iff_trivial_on_unitsMap_ker hp χ,
        MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    simp only [← MulChar.coe_toUnitHom, Units.val_eq_one]
  -- Sub-step B: Y = dual of H_map under subgroupOrderIsoSubgroupMulChar.
  have hY_eq : Y = (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ H_map).ofDual := by
    rw [hY]
    ext χ
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff,
        IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff]
    constructor
    · intro h u hu
      simp only [H_map, MulEquiv.coe_mapSubgroup, Subgroup.mem_map] at hu
      obtain ⟨σ, hσ, rfl⟩ := hu
      exact h σ hσ
    · intro h σ hσ
      apply h
      simp only [H_map, MulEquiv.coe_mapSubgroup, Subgroup.mem_map]
      exact ⟨σ, hσ, rfl⟩
  -- Sub-step C: Y ⊓ Y_p = dual of (H_map ⊔ I_p).
  have hInter : Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := n) p =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ (H_map ⊔ I_p)).ofDual := by
    rw [hY_eq, hYp_eq]
    rw [← ofDual_sup, ← (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ).map_sup]
  -- Sub-step D: cardinality via card_subgroupOrderIsoSubgroupMulChar.
  rw [hInter]
  simp only [MulChar.card_subgroupOrderIsoSubgroupMulChar]
  -- Goal: Nat.card ((ZMod n)ˣ ⧸ (H_map ⊔ I_p)) = Nat.card Y / ramificationIdxIn p (𝓞 F).
  -- Sub-step E: general case via R1 + relIndex chain + first iso.
  haveI hpFact : Fact (Nat.Prime p) := ⟨hp⟩
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  haveI hKnGal : IsGalois ℚ Kn := IsCyclotomicExtension.isGalois {n} ℚ Kn
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp_ideal_ne_bot : p_ideal ≠ ⊥ := by
    simp only [p_ideal, ne_eq, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  -- Obtain a prime P of 𝓞 Kn above p_ideal, set PF = P.comap in 𝓞 F.
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := p_ideal.nonempty_primesOver (S := 𝓞 Kn)
  haveI hP_IsPrime : P.IsPrime := hPprime
  haveI hP_LiesOver : P.LiesOver p_ideal := hPover
  have h_P_ne_bot : P ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver hp_ideal_ne_bot ⟨hPprime, hPover⟩
  haveI hPmax : P.IsMaximal := hPprime.isMaximal h_P_ne_bot
  let PF := P.comap (algebraMap (𝓞 F) (𝓞 Kn))
  haveI h_PF_liesover_p : PF.LiesOver p_ideal := inferInstance
  haveI h_PF_max : PF.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hPF_ne_bot : PF ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h_PF_max (RingOfIntegers.not_isField F)
  haveI hGalFKn : IsGaloisGroup F.fixingSubgroup F Kn := isGaloisGroup_fixingSubgroup F
  letI hmsa : MulSemiringAction (↥F.fixingSubgroup) Kn := inferInstance
  letI hsd : SMulDistribClass (↥F.fixingSubgroup) (𝓞 Kn) Kn := inferInstance
  haveI hGalFKn_oi : IsGaloisGroup F.fixingSubgroup (𝓞 F) (𝓞 Kn) :=
    IsGaloisGroup.of_isFractionRing F.fixingSubgroup (𝓞 F) (𝓞 Kn) F Kn
  -- (E.1) Nat.card Y = Nat.card ((ZMod n)ˣ ⧸ H_map) by Pontryagin duality.
  have hcard_Y : Nat.card Y = Nat.card ((ZMod n)ˣ ⧸ H_map) := by
    rw [hY_eq]; exact MulChar.card_subgroupOrderIsoSubgroupMulChar
  -- (E.2) H_map is normal in the abelian group (ZMod n)ˣ.
  haveI hH_map_normal : H_map.Normal :=
    ⟨fun n hn g => by rw [mul_comm g n, mul_assoc, mul_inv_cancel g, mul_one]; exact hn⟩
  -- (E.3) relIndex chain:
  -- H_map.relIndex(H_map ⊔ I_p) = H_map.relIndex(I_p) [relIndex_sup_left].
  have hrel_sup : H_map.relIndex (H_map ⊔ I_p) = H_map.relIndex I_p :=
    @Subgroup.relIndex_sup_left _ _ I_p H_map hH_map_normal
  -- R1: I_p = galEquivZMod.mapSubgroup(P.inertia Gal(Kn/ℚ)).
  have hI_p_eq : I_p = (IsCyclotomicExtension.Rat.galEquivZMod n Kn).mapSubgroup
      (P.inertia Gal(Kn/ℚ)) :=
    (galEquivZMod_mapSubgroup_inertia_eq_kernel p P).symm
  -- H_map.relIndex(I_p) = F.fixingSubgroup.relIndex(P.inertia Gal(Kn/ℚ))
  -- [relIndex_map_map_of_injective].
  have hrel_galois : H_map.relIndex I_p =
      F.fixingSubgroup.relIndex (P.inertia Gal(Kn/ℚ)) := by
    rw [hI_p_eq]
    simp only [H_map, MulEquiv.coe_mapSubgroup]
    exact Subgroup.relIndex_map_map_of_injective _ _
      (IsCyclotomicExtension.Rat.galEquivZMod n Kn).injective
  -- F.fixingSubgroup.relIndex(P.inertia) = Nat.card(image) [relIndex_ker].
  let restrictF : Gal(Kn/ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  have hker_F_eq : restrictF.ker = F.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker F
  have hrel_restrict : F.fixingSubgroup.relIndex (P.inertia Gal(Kn/ℚ)) =
      Nat.card ((P.inertia Gal(Kn/ℚ)).map restrictF) := by
    have h := Subgroup.relIndex_ker (f := restrictF) (K := P.inertia Gal(Kn/ℚ))
    rw [hker_F_eq] at h
    exact h
  -- (E.4) Compute Nat.card(image) = ramificationIdxIn p (𝓞 F) via first iso.
  -- Let f_r = restrictF restricted to (P.inertia Gal(Kn/ℚ)).
  let f_r := restrictF.restrict (P.inertia Gal(Kn/ℚ))
  have hrange_f_r : f_r.range = (P.inertia Gal(Kn/ℚ)).map restrictF :=
    MonoidHom.restrict_range _ _
  -- First iso: Nat.card(f_r.ker) * Nat.card(f_r.range) = Nat.card(P.inertia Gal(Kn/ℚ)).
  have hfirst_iso : Nat.card f_r.ker * Nat.card f_r.range =
      Nat.card (P.inertia Gal(Kn/ℚ)) := by
    have h := f_r.ker.card_mul_index
    rw [Subgroup.index_ker] at h
    exact h
  -- Kernel of f_r: (restrictNormalHom F).ker.subgroupOf(P.inertia).
  have hker_f_r : f_r.ker = F.fixingSubgroup.subgroupOf (P.inertia Gal(Kn/ℚ)) := by
    rw [MonoidHom.ker_restrict, hker_F_eq]
  -- Nat.card(F.fixingSubgroup.subgroupOf(P.inertia)) = Nat.card(P.inertia F.fixingSubgroup).
  -- Use: (H.subgroupOf K).map K.subtype = H ⊓ K (subgroupOf_map_subtype)
  -- and equivMapOfInjective for cardinality.
  have hcard_ker_f_r : Nat.card f_r.ker = Nat.card (P.inertia F.fixingSubgroup) := by
    rw [hker_f_r]
    -- f_r.ker = F.fixingSubgroup.subgroupOf (P.inertia Gal(Kn/ℚ)) as a subgroup of P.inertia Gal(Kn/ℚ)
    -- P.inertia F.fixingSubgroup = (P.inertia Gal(Kn/ℚ)).subgroupOf F.fixingSubgroup via subgroupOf_inertia
    have h1 : Nat.card ↥(F.fixingSubgroup.subgroupOf (P.inertia Gal(Kn/ℚ))) =
        Nat.card ↥((F.fixingSubgroup.subgroupOf (P.inertia Gal(Kn/ℚ))).map
          (P.inertia Gal(Kn/ℚ)).subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv
    have h2 : (F.fixingSubgroup.subgroupOf (P.inertia Gal(Kn/ℚ))).map
        (P.inertia Gal(Kn/ℚ)).subtype = F.fixingSubgroup ⊓ P.inertia Gal(Kn/ℚ) :=
      Subgroup.subgroupOf_map_subtype _ _
    have h3 : Nat.card ↥(P.inertia F.fixingSubgroup) =
        Nat.card ↥((P.inertia F.fixingSubgroup).map F.fixingSubgroup.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv
    have h4 : (P.inertia F.fixingSubgroup).map F.fixingSubgroup.subtype =
        P.inertia Gal(Kn/ℚ) ⊓ F.fixingSubgroup :=
      AddSubgroup.inertia_map_subtype P.toAddSubgroup F.fixingSubgroup
    rw [h1, h2, h3, h4, inf_comm]
  -- Nat.card(P.inertia Gal(Kn/ℚ)) = ramificationIdxIn p (𝓞 Kn) [from R1 proof].
  haveI hGalKnQ : IsGaloisGroup Gal(Kn/ℚ) ℚ Kn := IsGaloisGroup.of_isGalois ℚ Kn
  haveI hGalKnZ : IsGaloisGroup Gal(Kn/ℚ) ℤ (𝓞 Kn) := inferInstance
  letI hFieldZ : Field (ℤ ⧸ p_ideal) := Ideal.Quotient.field _
  letI hFieldKn : Field (𝓞 Kn ⧸ P) := Ideal.Quotient.field _
  haveI h_isSepKn : Algebra.IsSeparable (ℤ ⧸ p_ideal) (𝓞 Kn ⧸ P) := by
    haveI : Finite (𝓞 Kn ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient h_P_ne_bot
    haveI : PerfectField (ℤ ⧸ p_ideal) := inferInstance
    haveI : Module.Finite (ℤ ⧸ p_ideal) (𝓞 Kn ⧸ P) :=
      (Module.finite_iff_finite (R := ℤ ⧸ p_ideal)).mpr ‹_›
    haveI : Algebra.IsAlgebraic (ℤ ⧸ p_ideal) (𝓞 Kn ⧸ P) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact inferInstance
  have hcard_inertia_Kn : Nat.card (P.inertia Gal(Kn/ℚ)) =
      p_ideal.ramificationIdxIn (𝓞 Kn) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(Kn/ℚ)) p_ideal hp_ideal_ne_bot P
  -- Nat.card(P.inertia F.fixingSubgroup) = PF.ramificationIdxIn(𝓞 Kn).
  haveI hP_LiesOver_PF : P.LiesOver PF := inferInstance
  letI hFieldF : Field (𝓞 F ⧸ PF) := Ideal.Quotient.field _
  haveI h_isSepFKn : Algebra.IsSeparable (𝓞 F ⧸ PF) (𝓞 Kn ⧸ P) := by
    haveI : Finite (𝓞 Kn ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient h_P_ne_bot
    haveI : Finite (𝓞 F ⧸ PF) := Ring.HasFiniteQuotients.finiteQuotient hPF_ne_bot
    haveI : PerfectField (𝓞 F ⧸ PF) := inferInstance
    haveI : Module.Finite (𝓞 F ⧸ PF) (𝓞 Kn ⧸ P) :=
      (Module.finite_iff_finite (R := 𝓞 F ⧸ PF)).mpr ‹_›
    haveI : Algebra.IsAlgebraic (𝓞 F ⧸ PF) (𝓞 Kn ⧸ P) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact inferInstance
  have hcard_inertia_FKn : Nat.card (P.inertia F.fixingSubgroup) =
      PF.ramificationIdxIn (𝓞 Kn) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := F.fixingSubgroup) PF hPF_ne_bot P
  -- Tower law: ramificationIdxIn p (𝓞 F) * PF.ramificationIdxIn(𝓞 Kn) = ramificationIdxIn p (𝓞 Kn).
  have htower : p_ideal.ramificationIdxIn (𝓞 F) * PF.ramificationIdxIn (𝓞 Kn) =
      p_ideal.ramificationIdxIn (𝓞 Kn) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn' PF
      (G := Gal(F/ℚ)) (GAC := Gal(Kn/ℚ)) (GBC := F.fixingSubgroup) (𝓞 Kn)
  -- Non-zero values.
  have hram_F_ne_zero : p_ideal.ramificationIdxIn (𝓞 F) ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (G := Gal(F/ℚ)) hp_ideal_ne_bot
  have hram_FKn_ne_zero : PF.ramificationIdxIn (𝓞 Kn) ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (G := F.fixingSubgroup) hPF_ne_bot
  -- From first iso: Nat.card(image) = ramificationIdxIn p (𝓞 F).
  have hcard_image : Nat.card f_r.range = p_ideal.ramificationIdxIn (𝓞 F) := by
    have hfiso2 := hfirst_iso
    rw [hcard_ker_f_r, hcard_inertia_FKn, hcard_inertia_Kn] at hfiso2
    -- hfiso2 : PF.ramificationIdxIn(𝓞 Kn) * Nat.card(range) = ramificationIdxIn p (𝓞 Kn)
    -- htower: p_ideal.ramificationIdxIn(𝓞 F) * PF.ramificationIdxIn(𝓞 Kn) = ramificationIdxIn p(𝓞 Kn)
    -- So PF.ramIdx * card = PF.ramIdx * ram_F, cancel PF.ramIdx.
    have hkey : PF.ramificationIdxIn (𝓞 Kn) * Nat.card f_r.range =
        PF.ramificationIdxIn (𝓞 Kn) * p_ideal.ramificationIdxIn (𝓞 F) := by
      rw [hfiso2, ← htower, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hram_FKn_ne_zero) hkey
  -- (E.5) Put it all together.
  -- relIndex chain: H_map.relIndex(H_map ⊔ I_p) = Nat.card(image) = ramificationIdxIn p F.
  have hrelIndex_eq : H_map.relIndex (H_map ⊔ I_p) = p_ideal.ramificationIdxIn (𝓞 F) := by
    rw [hrel_sup, hrel_galois, hrel_restrict, ← hrange_f_r, hcard_image]
  -- |(ZMod n)ˣ / (H_map ⊔ I_p)| = |(ZMod n)ˣ / H_map| / relIndex.
  have hle : H_map ≤ H_map ⊔ I_p := le_sup_left
  have hrelIndex_mul : H_map.relIndex (H_map ⊔ I_p) *
      Nat.card ((ZMod n)ˣ ⧸ (H_map ⊔ I_p)) = Nat.card ((ZMod n)ˣ ⧸ H_map) := by
    have h := H_map.relIndex_mul_index hle
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at h
    exact h
  rw [hcard_Y, ← hrelIndex_mul, hrelIndex_eq]
  exact (Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hram_F_ne_zero)).symm

/-- **Phase 4.** The image of `evalAtPrime` has cardinality equal to the inertia degree,
for primes `p` coprime to the level `n`. This is the Frobenius identification: the eval
at `p` corresponds to evaluating the Galois character at the Frobenius element
σ_p ∈ Gal(F/ℚ), whose order in Gal(F/ℚ) equals the inertia degree (B.5). -/
private lemma evalAtPrime_card_range_eq_inertiaDegIn
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {p : ℕ} (hp : p.Prime) (hp_n : p.Coprime n) :
    Nat.card (evalAtPrime Y p).range =
      Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  haveI hKnGal : IsGalois ℚ Kn := IsCyclotomicExtension.isGalois {n} ℚ Kn
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  let σ₀ : Gal(Kn/ℚ) :=
    (IsCyclotomicExtension.Rat.galEquivZMod n Kn).symm (ZMod.unitOfCoprime p hp_n)
  let u_p : (ZMod n)ˣ := ZMod.unitOfCoprime p hp_n
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  -- Obtain a prime P above p in 𝓞 Kn.
  obtain ⟨⟨P, hP_prime, hP_over⟩⟩ := p_ideal.nonempty_primesOver (S := 𝓞 Kn)
  haveI hp_ideal_max : p_ideal.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  haveI hP_prime_inst : P.IsPrime := hP_prime
  haveI hP_liesover : P.LiesOver p_ideal := hP_over
  haveI hP_max : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := p_ideal) (P := P)
  -- H_map: image of F.fixingSubgroup in (ZMod n)ˣ under galEquivZMod.
  let H_map := (IsCyclotomicExtension.Rat.galEquivZMod n Kn).mapSubgroup F.fixingSubgroup
  -- Step 1: Nat.card range = ker.index, by the first isomorphism theorem.
  rw [← Subgroup.index_ker (evalAtPrime Y p)]
  -- Step 2: When p ∤ n, all chars in Y have conductor dividing n and p-coprime.
  have hY_sub_coprime : Y ≤ DirichletCharacter.subgroupOfCoprimeConductor p := by
    intro χ hχY
    exact DirichletCharacter.mem_subgroupOfCoprimeConductor.mpr
      (hp_n.coprime_dvd_right (DirichletCharacter.conductor_dvd_level χ))
  have hInter_eq : Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p = Y :=
    inf_eq_left.mpr hY_sub_coprime
  -- Step 3: Identify Y = dual of H_map via Pontryagin (same as A.3).
  have hY_eq : Y = (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ H_map).ofDual := by
    rw [hY]; ext χ
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff,
        IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff]
    constructor
    · intro h u hu
      obtain ⟨σ, hσ, rfl⟩ := (by simp only [H_map, MulEquiv.coe_mapSubgroup, Subgroup.mem_map]
                                     at hu; exact hu)
      exact h σ hσ
    · intro h σ hσ
      exact h _ (by simp only [H_map, MulEquiv.coe_mapSubgroup, Subgroup.mem_map]; exact ⟨σ, hσ, rfl⟩)
  -- Step 4: The kernel of evalAtPrime Y p (via the bijection Y ⊓ sub = Y when coprime).
  -- evalAtPrime χ = χ(u_p) by B.2.
  -- ker = {χ ∈ Y : χ(u_p) = 1} = Y ∩ dual(zpowers u_p) = dual(H_map ⊔ zpowers u_p).
  -- χ(u_p) = 1 ↔ χ annihilates all zpowers of u_p.
  have hχ_zpow : ∀ (χ : DirichletCharacter ℂ n), χ ↑u_p = 1 →
      ∀ k : ℤ, χ ↑(u_p ^ k) = 1 := by
    intro χ hχ k
    induction k using Int.induction_on with
    | zero => simp [map_one]
    | succ k ih =>
      rw [zpow_add_one u_p, Units.val_mul, map_mul, ih, one_mul, hχ]
    | pred k ih =>
      have hχinv : χ ↑(u_p⁻¹) = 1 := by
        have h1 : χ ↑(u_p * u_p⁻¹) = 1 := by
          rw [mul_inv_cancel, Units.val_one, map_one]
        rw [Units.val_mul, map_mul, hχ, one_mul] at h1; exact h1
      rw [zpow_sub_one u_p, Units.val_mul, map_mul, ih, one_mul, hχinv]
  have hK_up_eq : ∀ χ : DirichletCharacter ℂ n,
      χ ∈ (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ (Subgroup.zpowers u_p)).ofDual ↔
      χ u_p = 1 := fun χ => by
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    constructor
    · intro h; exact h u_p (Subgroup.mem_zpowers u_p)
    · intro hχ u hu
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [← hk]; exact hχ_zpow χ hχ k
  -- Step 4b: Map the kernel to DirichletCharacter ℂ n via the subtype inclusion, and identify
  -- its image as the Pontryagin dual of H_map ⊔ zpowers u_p.
  -- The kernel consists of χ ∈ Y ⊓ coprime with χ(u_p) = 1.
  -- Since Y ⊆ coprime (hY_sub_coprime), this equals {χ ∈ Y : χ(u_p) = 1}.
  -- By Pontryagin: ofDual(iso H_map) ∩ ofDual(iso(zpowers u_p)) = ofDual(iso(H_map ⊔ zpowers u_p)).
  have hker_map_eq :
      (evalAtPrime Y p).ker.map (Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p).subtype =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ (H_map ⊔ Subgroup.zpowers u_p)).ofDual := by
    ext χ
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype]
    rw [(MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ).map_sup, ofDual_sup,
        Subgroup.mem_inf, ← hY_eq, hK_up_eq]
    constructor
    · rintro ⟨⟨χ', hχ'_Y, hχ'_cop⟩, hker, rfl⟩
      -- hker : evalAtPrime Y p ⟨χ', ...⟩ = 1 (in ℂˣ)
      -- hv : (evalAtPrime : ℂ) = χ' ((p : ℕ) : ZMod n)
      -- Since u_p = ZMod.unitOfCoprime p hp_n and (u_p : ZMod n) = (p : ZMod n),
      -- χ' u_p = χ' (p : ZMod n) = (evalAtPrime : ℂ) = 1.
      have hval : χ' ((p : ℕ) : ZMod n) = 1 := by
        have hv := evalAtPrime_eq_natCast Y hp_n ⟨χ', hχ'_Y, hχ'_cop⟩
        have hker_val : (evalAtPrime Y p ⟨χ', hχ'_Y, hχ'_cop⟩ : ℂ) = 1 :=
          congr_arg Units.val hker
        rw [hv] at hker_val; exact_mod_cast hker_val
      refine ⟨hχ'_Y, ?_⟩
      -- Goal: χ' u_p = 1, i.e., χ' (ZMod.unitOfCoprime p hp_n) = 1
      -- But χ' : ZMod n → ℂ (MulChar), and u_p = ZMod.unitOfCoprime p hp_n,
      -- so χ' u_p = χ' ((unitOfCoprime p hp_n : ZMod n)) = χ' (p : ZMod n) = 1.
      change χ' (ZMod.unitOfCoprime p hp_n) = 1
      rw [ZMod.coe_unitOfCoprime]; exact hval
    · intro ⟨hχY, hχup⟩
      -- hχup : χ u_p = 1 (i.e., χ (ZMod.unitOfCoprime p hp_n) = 1)
      refine ⟨⟨χ, hχY, hY_sub_coprime hχY⟩, ?_, rfl⟩
      apply Units.ext; rw [Units.val_one]
      have hv := evalAtPrime_eq_natCast Y hp_n ⟨χ, hχY, hY_sub_coprime hχY⟩
      -- hv : (evalAtPrime : ℂ) = χ ((p : ℕ) : ZMod n)
      rw [hv]
      have hχup' : χ ((p : ℕ) : ZMod n) = 1 := by
        have := hχup  -- χ (ZMod.unitOfCoprime p hp_n) = 1
        rw [show (ZMod.unitOfCoprime p hp_n : ZMod n) = (p : ZMod n) from
            ZMod.coe_unitOfCoprime p hp_n] at this
        exact_mod_cast this
      exact_mod_cast hχup'
  -- Kernel cardinality = Nat.card (dual of H_map ⊔ zpowers u_p).
  have hker_card : Nat.card (evalAtPrime Y p).ker =
      Nat.card ((MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ
        (H_map ⊔ Subgroup.zpowers u_p)).ofDual) := by
    calc Nat.card (evalAtPrime Y p).ker
        = Nat.card ((evalAtPrime Y p).ker.map
              (Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p).subtype) :=
              Nat.card_congr (Subgroup.equivMapOfInjective _
                (Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p).subtype
                (Subgroup.subtype_injective _)).toEquiv
      _ = _ := by rw [hker_map_eq]
  -- Step 5: Cardinalities.
  have hcard_Y : Nat.card Y = Nat.card ((ZMod n)ˣ ⧸ H_map) := by
    rw [hY_eq]; exact MulChar.card_subgroupOrderIsoSubgroupMulChar
  have hcard_ker : Nat.card (evalAtPrime Y p).ker =
      Nat.card ((ZMod n)ˣ ⧸ (H_map ⊔ Subgroup.zpowers u_p)) := by
    rw [hker_card]; exact MulChar.card_subgroupOrderIsoSubgroupMulChar
  -- Step 6: Lagrange: ker.index = Nat.card domain / Nat.card ker.
  have hcard_domain : Nat.card (↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p)) =
      Nat.card Y := Nat.card_congr (Equiv.subtypeEquivRight (fun χ => by
        constructor
        · exact fun h => hInter_eq ▸ h
        · exact fun h => hInter_eq.symm ▸ h))
  have hindex_eq : (evalAtPrime Y p).ker.index =
      Nat.card (↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p)) /
      Nat.card (evalAtPrime Y p).ker := by
    have h := (evalAtPrime Y p).ker.card_mul_index
    exact Nat.eq_div_of_mul_eq_right (Nat.card_pos.ne') h
  rw [hindex_eq, hcard_domain, hcard_ker, hcard_Y]
  -- Goal: |(ZMod n)ˣ / H_map| / |(ZMod n)ˣ / (H_map ⊔ zpowers u_p)| = inertiaDegIn.
  -- Step 7: relIndex computation.
  -- H_map.relIndex (H_map ⊔ zpowers u_p) = |(ZMod n)ˣ / H_map| / |(ZMod n)ˣ / (H_map ⊔ zpowers u_p)|.
  have hle : H_map ≤ H_map ⊔ Subgroup.zpowers u_p := le_sup_left
  have hrelIndex_eq :
      H_map.relIndex (H_map ⊔ Subgroup.zpowers u_p) =
      Nat.card ((ZMod n)ˣ ⧸ H_map) / Nat.card ((ZMod n)ˣ ⧸ (H_map ⊔ Subgroup.zpowers u_p)) := by
    have h_mul := H_map.relIndex_mul_index hle
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at h_mul
    exact Nat.eq_div_of_mul_eq_right (Nat.card_pos.ne')
      (mul_comm (H_map.relIndex (H_map ⊔ Subgroup.zpowers u_p))
        (Nat.card ((ZMod n)ˣ ⧸ H_map ⊔ Subgroup.zpowers u_p)) ▸ h_mul)
  rw [← hrelIndex_eq]
  -- Step 8: relIndex_sup_left — H_map.relIndex (H_map ⊔ zpowers u_p) = H_map.relIndex (zpowers u_p).
  -- (Since (ZMod n)ˣ is abelian, H_map is normal.)
  haveI hH_map_normal : H_map.Normal := ⟨fun n hn g => by
    rw [mul_comm g n, mul_assoc, mul_inv_cancel g, mul_one]; exact hn⟩
  have hrel_eq2 : H_map.relIndex (H_map ⊔ Subgroup.zpowers u_p) =
      H_map.relIndex (Subgroup.zpowers u_p) :=
    @Subgroup.relIndex_sup_left _ _ (Subgroup.zpowers u_p) H_map hH_map_normal
  rw [hrel_eq2]
  -- Step 9: H_map.relIndex (zpowers u_p) = F.fixingSubgroup.relIndex (zpowers σ₀)
  -- via galEquivZMod: H_map = galEquivZMod.mapSubgroup F.fixingSubgroup,
  -- zpowers u_p = galEquivZMod.mapSubgroup (zpowers σ₀).
  have hzpowers_u_p : Subgroup.zpowers u_p =
      (IsCyclotomicExtension.Rat.galEquivZMod n Kn).mapSubgroup (Subgroup.zpowers σ₀) := by
    simp only [MulEquiv.coe_mapSubgroup, MonoidHom.map_zpowers, σ₀, u_p]
    congr 1
    exact ((IsCyclotomicExtension.Rat.galEquivZMod n Kn).apply_symm_apply _).symm
  have hrelIndex_galois : H_map.relIndex (Subgroup.zpowers u_p) =
      F.fixingSubgroup.relIndex (Subgroup.zpowers σ₀) := by
    rw [hzpowers_u_p]
    simp only [H_map, MulEquiv.coe_mapSubgroup]
    exact Subgroup.relIndex_map_map_of_injective _ _
      (IsCyclotomicExtension.Rat.galEquivZMod n Kn).injective
  rw [hrelIndex_galois]
  -- Step 10: F.fixingSubgroup.relIndex (zpowers σ₀) = orderOf (σ₀.restrictNormal F) by B.5's h_relIndex.
  have h_relIndex : F.fixingSubgroup.relIndex (Subgroup.zpowers σ₀) =
      orderOf (σ₀.restrictNormal F) := by
    have key := Subgroup.relIndex_ker (f := AlgEquiv.restrictNormalHom F)
      (K := Subgroup.zpowers σ₀)
    have hker : (AlgEquiv.restrictNormalHom F).ker = F.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker F
    rw [hker, MonoidHom.map_zpowers, Nat.card_zpowers] at key
    exact key
  rw [h_relIndex]
  -- Step 11: Apply B.5.
  exact orderOf_restrictNormal_eq_inertiaDegIn F hp_n P

/-- **Phase 5.** The kernel of `evalAtPrime` has cardinality equal to the number of primes
of `𝓞 F` above `p`. Proved via the fundamental identity `e·f·g = [F:ℚ] = |Y|` with `e = 1`
(unramified, since `p` is coprime to `n`), the first isomorphism theorem, and Phase 4. -/
private lemma evalAtPrime_card_ker_eq_primesAbove
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {p : ℕ} (hp : p.Prime) (hp_n : p.Coprime n) :
    Nat.card (evalAtPrime Y p).ker = (primesAboveOf F p).card := by
  haveI hFGal : IsGalois ℚ F := (IsAbelianGalois.tower_bot ℚ F Kn).toIsGalois
  haveI hKnGal : IsGalois ℚ Kn := IsCyclotomicExtension.isGalois {n} ℚ Kn
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  let p_ideal := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp_ideal_ne_bot : p_ideal ≠ ⊥ := by
    simp only [p_ideal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI hp_ideal_max : p_ideal.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  -- Step 1: Since p coprime to n, all chars in Y have coprime conductor, so Y ⊆ Y_p.
  have hY_sub_coprime : Y ≤ DirichletCharacter.subgroupOfCoprimeConductor p := by
    intro χ hχY
    exact DirichletCharacter.mem_subgroupOfCoprimeConductor.mpr
      (hp_n.coprime_dvd_right (DirichletCharacter.conductor_dvd_level χ))
  -- Domain of evalAtPrime is Y ⊓ Y_p = Y.
  have hInter_eq : Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p = Y :=
    inf_eq_left.mpr hY_sub_coprime
  have hcard_domain : Nat.card (↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p)) =
      Nat.card Y := Nat.card_congr (Equiv.subtypeEquivRight (fun χ => by
        constructor
        · exact fun h => hInter_eq ▸ h
        · exact fun h => hInter_eq.symm ▸ h))
  -- Step 2: First isomorphism theorem: |Y| = |range| * |ker|.
  -- card_mul_index: |ker| * ker.index = |domain|;  index_ker: ker.index = |range|.
  have hfirst_iso : Nat.card Y =
      Nat.card (evalAtPrime Y p).range * Nat.card (evalAtPrime Y p).ker := by
    have h := (evalAtPrime Y p).ker.card_mul_index
    rw [Subgroup.index_ker] at h
    -- h : Nat.card ker * Nat.card range = Nat.card (↥(Y ⊓ Y_p))
    rw [mul_comm, hcard_domain] at h
    -- h : Nat.card range * Nat.card ker = Nat.card Y
    exact h.symm
  -- Step 3: Phase 4 gives range cardinality = inertiaDeg = f.
  have hrange_eq : Nat.card (evalAtPrime Y p).range =
      Ideal.inertiaDegIn p_ideal (𝓞 F) :=
    evalAtPrime_card_range_eq_inertiaDegIn F Y hY hp hp_n
  -- Step 4: Ramification index e = 1 (p coprime to n → unramified in F).
  have hp_not_dvd : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp hp_n
  -- Obtain a prime P above p in 𝓞 Kn, then PF = P.comap in 𝓞 F.
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := p_ideal.nonempty_primesOver (S := 𝓞 Kn)
  haveI hP_prime_inst : P.IsPrime := hPprime
  haveI hP_liesover : P.LiesOver p_ideal := hPover
  haveI hP_max : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := p_ideal) (P := P)
  let PF := P.comap (algebraMap (𝓞 F) (𝓞 Kn))
  haveI h_PF_liesover_p : PF.LiesOver p_ideal := inferInstance
  haveI h_PF_max : PF.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hPF_ne_bot : PF ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h_PF_max (RingOfIntegers.not_isField F)
  haveI hGalFKn : IsGaloisGroup F.fixingSubgroup F Kn := isGaloisGroup_fixingSubgroup F
  letI hmsa : MulSemiringAction (↥F.fixingSubgroup) Kn := inferInstance
  letI hsd : SMulDistribClass (↥F.fixingSubgroup) (𝓞 Kn) Kn := inferInstance
  haveI hGalFKn_oi : IsGaloisGroup F.fixingSubgroup (𝓞 F) (𝓞 Kn) :=
    IsGaloisGroup.of_isFractionRing F.fixingSubgroup (𝓞 F) (𝓞 Kn) F Kn
  have hramIdx_Kn : p_ideal.ramificationIdxIn (𝓞 Kn) = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p Kn hp_not_dvd
  have htower_ram : p_ideal.ramificationIdxIn (𝓞 F) * PF.ramificationIdxIn (𝓞 Kn) =
      p_ideal.ramificationIdxIn (𝓞 Kn) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn' PF
      (G := Gal(F/ℚ)) (GAC := Gal(Kn/ℚ)) (GBC := F.fixingSubgroup) (𝓞 Kn)
  rw [hramIdx_Kn] at htower_ram
  have h1 : p_ideal.ramificationIdxIn (𝓞 F) ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (G := Gal(F/ℚ)) hp_ideal_ne_bot
  have h2 : PF.ramificationIdxIn (𝓞 Kn) ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (G := F.fixingSubgroup) hPF_ne_bot
  have hramIdx_F : p_ideal.ramificationIdxIn (𝓞 F) = 1 := by
    nlinarith [Nat.one_le_iff_ne_zero.mpr h1, Nat.one_le_iff_ne_zero.mpr h2]
  -- Step 5: Fundamental identity g * (e * f) = |Gal(F/ℚ)| with e = 1.
  -- Need IsGaloisGroup Gal(F/ℚ) ℤ (𝓞 F).
  haveI hGalF_oi : IsGaloisGroup Gal(F/ℚ) ℤ (𝓞 F) :=
    IsGaloisGroup.of_isFractionRing Gal(F/ℚ) ℤ (𝓞 F) ℚ F
  have hefg : (p_ideal.primesOver (𝓞 F)).ncard *
      (p_ideal.ramificationIdxIn (𝓞 F) * p_ideal.inertiaDegIn (𝓞 F)) =
      Nat.card Gal(F/ℚ) :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp_ideal_ne_bot (𝓞 F) Gal(F/ℚ)
  rw [hramIdx_F, one_mul] at hefg
  -- Step 6: Nat.card Y = [F:ℚ] = Nat.card Gal(F/ℚ).
  have hcard_Y_eq : Nat.card Y = Nat.card Gal(F/ℚ) := by
    rw [hY, IsCyclotomicExtension.Rat.card_intermediateFieldEquivSubgroupChar]
    exact (IsGalois.card_aut_eq_finrank ℚ F).symm
  -- Step 7: (primesAboveOf F p).card = g = (p_ideal.primesOver (𝓞 F)).ncard.
  have hcard_g : (primesAboveOf F p).card = (p_ideal.primesOver (𝓞 F)).ncard := by
    unfold primesAboveOf
    rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hp_ideal_ne_bot]
  -- Step 8: Arithmetic conclusion: g = ker (and hence (primesAboveOf F p).card = Nat.card ker).
  -- (i) g * f = |Y|  (from hefg with e=1 and hcard_Y_eq)
  -- (ii) f * ker = |Y|  (from hfirst_iso and hrange_eq)
  -- (iii) f ≠ 0
  -- Therefore g * f = ker * f, so g = ker.
  have hf_ne : p_ideal.inertiaDegIn (𝓞 F) ≠ 0 :=
    Ideal.inertiaDegIn_ne_zero (G := Gal(F/ℚ))
  -- (i): g * f = |Gal| = |Y|
  have hgf_eq_Y : (p_ideal.primesOver (𝓞 F)).ncard * p_ideal.inertiaDegIn (𝓞 F) =
      Nat.card Y := hefg.trans hcard_Y_eq.symm
  -- (ii): f * ker = |Y|  (= range * ker after substituting range = f)
  have hf_ker_eq_Y : Nat.card Y =
      p_ideal.inertiaDegIn (𝓞 F) * Nat.card (evalAtPrime Y p).ker := hrange_eq ▸ hfirst_iso
  -- Conclude: g = ker via mul cancellation.
  -- From hgf_eq_Y: g * f = |Y|; from hf_ker_eq_Y: |Y| = f * ker.
  -- We have f * ker = |Y| = g * f = f * g, so f * ker = f * g, giving ker = g.
  rw [hcard_g]
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf_ne) ?_
  -- subgoal: f * ker = f * g  (proves ker = g, so we need to prove f * g = f * ker first,
  -- but Lean's convention seems reversed; after refine, goal should be one direction)
  -- From error: expected LHS is f * ker, RHS is f * g.
  -- f * ker = |Y| = g * f = f * g
  calc p_ideal.inertiaDegIn (𝓞 F) * Nat.card (evalAtPrime Y p).ker
      = Nat.card Y := hf_ker_eq_Y.symm
    _ = (p_ideal.primesOver (𝓞 F)).ncard * p_ideal.inertiaDegIn (𝓞 F) := hgf_eq_Y.symm
    _ = p_ideal.inertiaDegIn (𝓞 F) * (p_ideal.primesOver (𝓞 F)).ncard := mul_comm _ _


/-- **B.1+B.4 LHS reduction.** The character-side product collapses to the same
geometric form as the prime-side, namely `((1 - p^(-fs))⁻¹)^g`. Composes Phase 2
(restriction to coprime conductors), Phase 3 (eval hom + multiplicativity), the abstract
orthogonality lemma `prod_one_sub_groupHom_apply_mul`, and the Frobenius/orbit-count
identifications (Phase 4 + 5). Requires `p` coprime to the cyclotomic level `n` (unramified
case; the ramified case is handled separately at the top level). -/
private lemma prod_chars_eq_pow_of_inertiaDegIn
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime) (hp_n : p.Coprime n) :
    ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ((1 - (p : ℂ) ^
          (-((Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) : ℂ) * s)))⁻¹) ^
        (primesAboveOf F p).card := by
  classical
  set T := (p : ℂ) ^ (-s) with hT_def
  set f := Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) with hf_def
  set g := (primesAboveOf F p).card with hg_def
  -- Phase 2: restrict to coprime-conductor characters.
  rw [prod_chars_eq_prod_coprime_conductor Y hp]
  -- Bijection: Finset.filter on ↥Y ↔ Finset.univ on ↥(Y ⊓ subgroupOfCoprimeConductor p).
  let e : { χ : ↥Y // p.Coprime χ.val.conductor } ≃
      ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p) :=
    { toFun := fun χ => ⟨χ.val.val, χ.val.property,
        DirichletCharacter.mem_subgroupOfCoprimeConductor.mpr χ.property⟩
      invFun := fun χ => ⟨⟨χ.val, χ.property.1⟩,
        DirichletCharacter.mem_subgroupOfCoprimeConductor.mp χ.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Finset.prod_subtype_eq_prod_filter (s := (Finset.univ : Finset Y))
        (p := fun χ : Y => p.Coprime χ.val.conductor)
        (f := fun χ : Y => (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹),
      Finset.subtype_univ,
      Fintype.prod_equiv e
        (fun χ : { χ : ↥Y // p.Coprime χ.val.conductor } =>
          (1 - χ.val.val.primitiveCharacter (p : ℕ) * T)⁻¹)
        (fun χ : ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p) =>
          (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹) (fun _ => rfl)]
  -- Now: ∏ χ : ↥(Y ⊓ ...), (1 - χ.val.primitive(p) * T)⁻¹ = (...)
  -- Convert each factor to use evalAtPrime.
  have h_eq : ∀ χ : ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p),
      (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹ =
      (1 - ((evalAtPrime Y p χ : ℂˣ) : ℂ) * T)⁻¹ := fun χ => by rw [evalAtPrime_val]
  rw [Finset.prod_congr rfl (fun χ _ => h_eq χ)]
  -- Pull out the inverse.
  rw [Finset.prod_inv_distrib]
  -- Apply abstract orthogonality.
  rw [prod_one_sub_groupHom_apply_mul (evalAtPrime Y p) T]
  -- Identify cardinalities (Phase 4 + 5).
  rw [evalAtPrime_card_range_eq_inertiaDegIn F Y hY hp hp_n,
      evalAtPrime_card_ker_eq_primesAbove F Y hY hp hp_n]
  -- ((1 - T^f)^g)⁻¹ = ((1 - T^f)⁻¹)^g.
  rw [← inv_pow]
  -- T^f = p^(-(f*s)) since T = p^(-s).  Need: T^f = (p:ℂ)^(-(f * s)).
  congr 2
  rw [hT_def, ← Complex.cpow_mul_nat (p : ℂ) (-s) f]
  ring_nf

/-- **Step B.** The product of primitive Dirichlet local Euler factors over the character group
`Y` equals the product of geometric series over primes above `p` (in absolute-norm form).

The proof is by composition of two reductions, each to the same closed form `((1 - p^(-fs))⁻¹)^g`:
* the prime-side reduction (`prod_inertia_eq_pow_of_inertiaDegIn`), which uses
  `absNorm_eq_pow_inertiaDeg'` and the Galois invariance of inertia degree;
* the character-side reduction (`prod_chars_eq_pow_of_inertiaDegIn`), which uses
  Frobenius identification (B.1) and the orbit count (B.4).

Requires `p` coprime to the cyclotomic level `n` (unramified case).
-/
theorem prod_chars_eq_prod_inertia
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime) (hp_n : p.Coprime n) :
    ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  rw [prod_chars_eq_pow_of_inertiaDegIn F Y hY hp hp_n,
      ← prod_inertia_eq_pow_of_inertiaDegIn (n := n) F hp]

/-- **Local-factor matching.** For an intermediate field `F` of `ℚ(ζₙ)/ℚ` and a prime `p`
coprime to the cyclotomic level `n`, the prime-power Dedekind summand at `p` factorizes as a
product of primitive Dirichlet local Euler factors indexed by the character subgroup `Y`
corresponding to `F`. Composes Step A (`dedekindZetaSummand_localSum_eq_prod_inertia`) and
Step B (`prod_chars_eq_prod_inertia`). -/
theorem dedekindZeta_localFactor_eq_prod_dirichletLocal
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ} (hs : 1 < s.re)
    {p : ℕ} (hp : p.Prime) (hp_n : p.Coprime n) :
    ∑' e : ℕ, dedekindZetaSummand F s (p ^ e) =
      ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ := by
  rw [dedekindZetaSummand_localSum_eq_prod_inertia (F := F) hp hs,
      ← prod_chars_eq_prod_inertia F Y hY hp hp_n]

/-! ### Character-group product assembly

Given the per-prime local factor identity (in primitive form), the global identity follows
by taking the product over primes and exchanging it with the product over characters (a finite
group), using absolute convergence on the analytic side and
`DirichletCharacter.LSeries_eulerProduct_tprod` on each per-character side.
-/

/-- **Character-group product.** The prime-by-prime product of *primitive* Dirichlet local
Euler factors over a character subgroup `Y` reassembles to a product of (primitive)
L-functions over `Y`. -/
theorem prod_dirichletLocal_eq_prod_LFunction
    {n : ℕ} [NeZero n] (Y : Subgroup (DirichletCharacter ℂ n)) {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, ∏ χ : Y,
        (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ χ : Y, DirichletCharacter.LFunction χ.val.primitiveCharacter s := by
  have hMult : ∀ χ : Y,
      Multipliable (fun p : Nat.Primes ↦
        (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹) :=
    fun χ => (DirichletCharacter.LSeries_eulerProduct_hasProd
      χ.val.primitiveCharacter hs).multipliable
  rw [Multipliable.tprod_finsetProd (s := (Finset.univ : Finset Y))
        (fun χ _ => hMult χ)]
  refine Finset.prod_congr rfl fun χ _ => ?_
  haveI : NeZero χ.val.conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
  rw [DirichletCharacter.LSeries_eulerProduct_tprod χ.val.primitiveCharacter hs,
      ← DirichletCharacter.LFunction_eq_LSeries χ.val.primitiveCharacter hs]

/-! ### Ramified-case local factor identity

For primes `p ∣ n`, the local factor identity requires a tame-level reduction. The key steps are:
1. Characters `χ ∈ Y` with `p ∣ conductor χ` contribute factor `(1 - 0 · T)⁻¹ = 1` (Phase 2).
2. The remaining characters `Y ⊓ subgroupOfCoprimeConductor p` have conductor dividing
   `m := Nat.divMaxPow n p` (the p'-part of n), and correspond to the character group of the
   "tame intermediate field" `F_tame = F ⊓ Km` where `Km = ℚ(ζₘ) ⊆ ℚ(ζₙ)`.
3. At level m (with `p.Coprime m`), the unramified result applies to `F_tame ⊆ Km`.
4. The prime product for `F` equals the prime product for `F_tame` because `F/F_tame` is
   totally ramified at `p` (a subextension of the totally ramified `Kn/Km`), giving:
   same number of primes above `p` and same inertia degree.

The proof requires the following key lemmas not yet in Mathlib:
- Conductor equality under `changeLevel`: `(changeLevel h χ).conductor = χ.conductor`
- Totally-ramified tower law for `F/F_tame` at `p`
These are left as `sorry` markers below.
-/

/-- **Conductor of `changeLevel`.** Lifting a character to a higher level preserves conductor.

The key equivalence: for `c ∣ m`, `FactorsThrough (changeLevel h χ) c ↔ FactorsThrough χ c`.
This follows from `changeLevel_injective h` and `changeLevel_trans`.
Since both `conductor(χ)` and `conductor(changeLevel h χ)` are the minimum of their respective
conductor sets restricted to divisors of `m`, and these sets agree, the conductors are equal. -/
private lemma conductor_changeLevel {n m : ℕ} [NeZero n] [NeZero m] (h : m ∣ n)
    (χ : DirichletCharacter ℂ m) :
    (DirichletCharacter.changeLevel h χ).conductor = χ.conductor := by
  -- Key equivalence: for c ∣ m, FactorsThrough (changeLevel h χ) c ↔ FactorsThrough χ c.
  -- Proof: changeLevel h χ = changeLevel (c_dvd_n) ξ iff χ = changeLevel (c_dvd_m) ξ
  --        by changeLevel_trans + changeLevel_injective h.
  have key : ∀ (c : ℕ) (_ : c ∣ m),
      (DirichletCharacter.changeLevel h χ).FactorsThrough c ↔ χ.FactorsThrough c := fun c hc ↦ by
    constructor
    · -- Forward: changeLevel h χ = changeLevel hc_n ξ (hc_n : c ∣ n), so χ = changeLevel hc ξ.
      rintro ⟨hc_n, ξ, hξ⟩
      refine ⟨hc, ξ, DirichletCharacter.changeLevel_injective h ?_⟩
      -- Goal: changeLevel h χ = changeLevel h (changeLevel hc ξ)
      -- Rewrite RHS: changeLevel h (changeLevel hc ξ) = changeLevel (dvd_trans hc h) ξ [trans]
      --            = changeLevel hc_n ξ [proof irrel] = LHS [by hξ.symm]
      have hrw : DirichletCharacter.changeLevel h (DirichletCharacter.changeLevel hc ξ) =
                 DirichletCharacter.changeLevel hc_n ξ :=
        by rw [← DirichletCharacter.changeLevel_trans]
      rw [hrw]; exact hξ
    · -- Backward: χ = changeLevel hc_m ξ (hc_m : c ∣ m), so changeLevel h χ = changeLevel hc_n ξ.
      rintro ⟨hc_m, ξ, hξ⟩
      refine ⟨hc.trans h, ξ, ?_⟩
      -- Goal: changeLevel h χ = changeLevel (hc.trans h) ξ
      -- changeLevel h (changeLevel hc_m ξ) = changeLevel (hc_m.trans h) ξ [trans]
      --                                    = changeLevel (hc.trans h) ξ   [proof irrel]
      have hrw : DirichletCharacter.changeLevel h (DirichletCharacter.changeLevel hc_m ξ) =
                 DirichletCharacter.changeLevel (hc.trans h) ξ :=
        by rw [← DirichletCharacter.changeLevel_trans]
      rw [hξ]; exact hrw
  -- conductor(χ) ∈ conductorSet(changeLevel h χ)
  have h1 : χ.conductor ∈ (DirichletCharacter.changeLevel h χ).conductorSet :=
    (DirichletCharacter.mem_conductorSet_iff _).mpr
      ((key _ χ.conductor_dvd_level).mpr (DirichletCharacter.factorsThrough_conductor χ))
  -- conductor(changeLevel h χ) ∣ conductor(χ)  [direction 1]
  have hdir1 : (DirichletCharacter.changeLevel h χ).conductor ∣ χ.conductor :=
    DirichletCharacter.conductor_dvd_of_mem_conductorSet _ h1
  -- conductor(changeLevel h χ) ∣ m  (since it divides conductor(χ) which divides m)
  have hc_dvd_m : (DirichletCharacter.changeLevel h χ).conductor ∣ m :=
    hdir1.trans χ.conductor_dvd_level
  -- conductor(changeLevel h χ) ∈ conductorSet(χ)
  have h2 : (DirichletCharacter.changeLevel h χ).conductor ∈ χ.conductorSet :=
    (DirichletCharacter.mem_conductorSet_iff _).mpr
      ((key _ hc_dvd_m).mp (DirichletCharacter.factorsThrough_conductor _))
  -- conclude: conductor(χ) ∣ conductor(changeLevel h χ), then both divide each other
  exact Nat.dvd_antisymm hdir1 (DirichletCharacter.conductor_dvd_of_mem_conductorSet _ h2)

/-- **`primitiveCharacter` of `changeLevel`.** Lifting a character to a higher level preserves
its primitive character (up to the conductor equality `conductor_changeLevel`).

Stated in evaluation form: applying `(changeLevel h χ).primitiveCharacter` and
`χ.primitiveCharacter` to the same natural number `a` (each cast to its own conductor's `ZMod`)
yields the same value.

Proof: substitute the conductor equality `conductor_changeLevel` to align types, then use that
both primitive characters lift via `changeLevel` (along divisibilities to level `n`) to
`changeLevel h χ`, and `changeLevel_injective` to identify them. -/
private lemma primitiveCharacter_changeLevel {n m : ℕ} [NeZero n] [NeZero m] (h : m ∣ n)
    (χ : DirichletCharacter ℂ m) (a : ℕ) :
    (DirichletCharacter.changeLevel h χ).primitiveCharacter
        ((a : ℕ) : ZMod (DirichletCharacter.changeLevel h χ).conductor) =
      χ.primitiveCharacter ((a : ℕ) : ZMod χ.conductor) := by
  -- Conductor equality and the lifting fact `changeLevel_primitiveCharacter` for `changeLevel h χ`.
  have hcond : (DirichletCharacter.changeLevel h χ).conductor = χ.conductor :=
    conductor_changeLevel h χ
  have hlift_lhs : DirichletCharacter.changeLevel
      (DirichletCharacter.changeLevel h χ).conductor_dvd_level
      (DirichletCharacter.changeLevel h χ).primitiveCharacter = DirichletCharacter.changeLevel h χ :=
    DirichletCharacter.changeLevel_primitiveCharacter _
  -- Package the goal as `∀`-application of a helper that takes the conductor as a fresh
  -- variable, then we `subst` the conductor equality to merge it with `χ.conductor`.
  have key : ∀ (c : ℕ) (_hc : c = χ.conductor)
      (ψ : DirichletCharacter ℂ c)
      (hdvd : c ∣ n)
      (_hψ_lift : DirichletCharacter.changeLevel hdvd ψ = DirichletCharacter.changeLevel h χ),
      ψ ((a : ℕ) : ZMod c) = χ.primitiveCharacter ((a : ℕ) : ZMod χ.conductor) := by
    intro c hc ψ hdvd hψ_lift
    subst hc
    -- Goal: `ψ a = χ.primitiveCharacter a` in `ℂ`, with `ψ, χ.primitiveCharacter :
    -- DirichletCharacter ℂ χ.conductor`. Show `ψ = χ.primitiveCharacter`, then rewrite.
    have hψ_eq : ψ = χ.primitiveCharacter := by
      -- `changeLevel h χ = changeLevel hdvd χ.primitiveCharacter` (since
      -- `hdvd = χ.conductor_dvd_level.trans h` by proof irrelevance, and
      -- `changeLevel h χ = changeLevel h (changeLevel χ.conductor_dvd_level χ.primitiveCharacter)
      --                  = changeLevel (χ.conductor_dvd_level.trans h) χ.primitiveCharacter`).
      have hrhs : DirichletCharacter.changeLevel hdvd χ.primitiveCharacter
          = DirichletCharacter.changeLevel h χ := by
        rw [show hdvd = χ.conductor_dvd_level.trans h from rfl,
            DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level h,
            DirichletCharacter.changeLevel_primitiveCharacter]
      -- Then `changeLevel hdvd ψ = changeLevel hdvd χ.primitiveCharacter`; use injectivity.
      exact DirichletCharacter.changeLevel_injective hdvd (hψ_lift.trans hrhs.symm)
    rw [hψ_eq]
  exact key (DirichletCharacter.changeLevel h χ).conductor hcond
    (DirichletCharacter.changeLevel h χ).primitiveCharacter
    (DirichletCharacter.changeLevel h χ).conductor_dvd_level hlift_lhs

/-- **A.4 (subgroupOfCoprimeConductor as a cyclotomic-subfield character group).** Let `n` be a
positive level, `p` a prime, and `Km` the cyclotomic subfield `ℚ(ζₘ)` of `Kn = ℚ(ζₙ)` where
`m = Nat.divMaxPow n p` is the prime-to-`p` part of `n`. Then the subgroup of Dirichlet characters
of level `n` whose conductor is coprime to `p` equals the character subgroup associated to `Km`
under `intermediateFieldEquivSubgroupChar`.

Proof: both sides are characterised by the same divisibility `χ.conductor ∣ m`. For the LHS this
is the chain `p.Coprime χ.conductor ↔ χ.conductor ∣ Nat.divMaxPow n p` already proved inside
`subgroupOfCoprimeConductor_iff_trivial_on_unitsMap_ker`. For the RHS it is
`mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd`. -/
private lemma subgroupOfCoprimeConductor_eq_intermediateFieldEquivSubgroupChar
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    {p : ℕ} (hp : p.Prime)
    (Km : IntermediateField ℚ Kn) [NumberField Km] [IsGalois ℚ Km]
    [IsCyclotomicExtension {Nat.divMaxPow n p} ℚ Km] :
    DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := n) p =
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ Km := by
  haveI hm_ne : NeZero (Nat.divMaxPow n p) :=
    ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (divMaxPow_dvd' n p)⟩
  ext χ
  rw [DirichletCharacter.mem_subgroupOfCoprimeConductor,
      IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd
        (n := n) (K := Kn) (R := ℂ) Km (m := Nat.divMaxPow n p) (divMaxPow_dvd' n p) χ]
  -- p.Coprime χ.conductor ↔ χ.conductor ∣ Nat.divMaxPow n p.
  constructor
  · intro h_cop
    have h_ndvd : ¬p ∣ χ.conductor := hp.coprime_iff_not_dvd.mp h_cop
    have h_cop2 : Nat.Coprime χ.conductor (p ^ padicValNat p n) :=
      hp.coprime_pow_of_not_dvd h_ndvd
    have h_dvd_mp : χ.conductor ∣ Nat.divMaxPow n p * p ^ padicValNat p n :=
      (Nat.divMaxPow_mul_pow_padicValNat p n).symm ▸ χ.conductor_dvd_level
    exact h_cop2.dvd_mul_right.mp h_dvd_mp
  · intro h_dvd
    refine hp.coprime_iff_not_dvd.mpr ?_
    exact fun h_pdvd =>
      Nat.not_dvd_divMaxPow hp.one_lt (NeZero.ne n) (h_pdvd.trans h_dvd)

/-- **(a) Character-group tame intersection.** For `F` an intermediate field of `Kn = ℚ(ζₙ)`,
`p` a prime, and `Km = ℚ(ζₘ)` (`m = Nat.divMaxPow n p`) the tame cyclotomic subfield, the
intersection of the character subgroup `Y` associated to `F` with the coprime-conductor subgroup
`subgroupOfCoprimeConductor p` equals the character subgroup associated to the tame intermediate
field `F ⊓ Km`.

This is the character-side half of the tame-level reduction in `prod_chars_eq_prod_inertia_ramified`
(piece (a) of secular-constraints-7hra).

Proof: combine `subgroupOfCoprimeConductor_eq_intermediateFieldEquivSubgroupChar` with the fact that
`intermediateFieldEquivSubgroupChar` is an `OrderIso` and so preserves `⊓` (`OrderIso.map_inf`). -/
private lemma Y_inter_subgroupOfCoprimeConductor_eq_tame
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn)
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {p : ℕ} (hp : p.Prime)
    (Km : IntermediateField ℚ Kn) [NumberField Km] [IsGalois ℚ Km]
    [IsCyclotomicExtension {Nat.divMaxPow n p} ℚ Km] :
    Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p =
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ (F ⊓ Km) := by
  rw [hY, subgroupOfCoprimeConductor_eq_intermediateFieldEquivSubgroupChar hp Km,
      ← OrderIso.map_inf]

/-! ### Ramified case: scaffolded sub-lemmas

The ramified-case identity `prod_chars_eq_prod_inertia_ramified` is decomposed into four
named sub-lemmas, each of which can be proved independently:

* `prod_chars_ramified_LHS_eq_prod_tame` — character-side reduction (combines Phase 2 with
  `Y_inter_subgroupOfCoprimeConductor_eq_tame`).
* `prod_chars_tame_descend_to_level_m` — descent of the level-`n` tame character product to a
  level-`m` character product, using `primitiveCharacter_changeLevel`.
* `primesAboveOf_F_tame_eq_F_of_totally_ramified` — prime-side reduction: the totally ramified
  tower `F/F_tame` at primes above `p` forces `primesAboveOf F p` and `primesAboveOf F_tame p`
  to give the same absolute-norm product.
* `prod_chars_eq_prod_inertia_tame_m` — at the tame level `m`, the unramified case
  `prod_chars_eq_prod_inertia` applies to `F_tame_in_Km : IntermediateField ℚ Km`.

The main lemma `prod_chars_eq_prod_inertia_ramified` is then a short composition of these. -/

/-- **Ramified-case scaffold (a): character-side tame reduction.** Phase 2 plus
`Y_inter_subgroupOfCoprimeConductor_eq_tame` together identify the level-`n` character product
over `Y` with the level-`n` product over the tame subgroup `Y_tame`, defined as
the image of `F ⊓ Km` under `intermediateFieldEquivSubgroupChar`.

Existing API to compose:
* `prod_chars_eq_prod_coprime_conductor` (Phase 2) — drop characters with `p ∣ conductor`.
* `Y_inter_subgroupOfCoprimeConductor_eq_tame` — identify the surviving subgroup with `Y_tame`.

The output is a level-`n` product indexed by `Y_tame := intermediateFieldEquivSubgroupChar (F ⊓ Km)`. -/
private lemma prod_chars_ramified_LHS_eq_prod_tame
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn)
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime)
    (Km : IntermediateField ℚ Kn) [NumberField Km] [IsGalois ℚ Km]
    [IsCyclotomicExtension {Nat.divMaxPow n p} ℚ Km]
    (Y_tame : Subgroup (DirichletCharacter ℂ n))
    (hY_tame : Y_tame =
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ (F ⊓ Km)) :
    ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ χ : Y_tame, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ := by
  classical
  set T := (p : ℂ) ^ (-s) with hT_def
  -- Phase 2: restrict to coprime-conductor characters.
  rw [prod_chars_eq_prod_coprime_conductor Y hp]
  -- Bijection: filter on ↥Y ↔ Finset.univ on ↥(Y ⊓ subgroupOfCoprimeConductor p).
  let e : { χ : ↥Y // p.Coprime χ.val.conductor } ≃
      ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p) :=
    { toFun := fun χ => ⟨χ.val.val, χ.val.property,
        DirichletCharacter.mem_subgroupOfCoprimeConductor.mpr χ.property⟩
      invFun := fun χ => ⟨⟨χ.val, χ.property.1⟩,
        DirichletCharacter.mem_subgroupOfCoprimeConductor.mp χ.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Finset.prod_subtype_eq_prod_filter (s := (Finset.univ : Finset Y))
        (p := fun χ : Y => p.Coprime χ.val.conductor)
        (f := fun χ : Y => (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹),
      Finset.subtype_univ,
      Fintype.prod_equiv e
        (fun χ : { χ : ↥Y // p.Coprime χ.val.conductor } =>
          (1 - χ.val.val.primitiveCharacter (p : ℕ) * T)⁻¹)
        (fun χ : ↥(Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p) =>
          (1 - χ.val.primitiveCharacter (p : ℕ) * T)⁻¹) (fun _ => rfl)]
  -- Identify `Y ⊓ subgroupOfCoprimeConductor p` with `Y_tame` and reindex.
  have h_subgroup : Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor p = Y_tame := by
    rw [Y_inter_subgroupOfCoprimeConductor_eq_tame F Y hY hp Km, hY_tame]
  subst h_subgroup
  rfl

/-- **Ramified-case scaffold (b): level-`n` to level-`m` character descent.** At level `m`,
the corresponding character subgroup `Y_tame_m` (image of `F_tame_in_Km : IntermediateField ℚ Km`)
is in bijection with the level-`n` group `Y_tame` via `DirichletCharacter.changeLevel hm_dvd`.
Under this bijection, the primitive-character evaluation at `p` is preserved
(`primitiveCharacter_changeLevel` together with `changeLevel_eval_natCast_of_coprime` since
`p.Coprime m`).

Existing API to compose:
* `primitiveCharacter_changeLevel` — primitive character is preserved under `changeLevel`.
* `conductor_changeLevel` — conductor is preserved.
* Bijection level-`n`-tame ↔ level-`m`-tame via `changeLevel hm_dvd` restricted to `Y_tame_m`.

The link between `Y_tame` (level `n`) and `Y_tame_m` (level `m`) is taken as the hypothesis
`hYlink`: every level-`n` tame character is the `changeLevel` lift of a unique level-`m`
character in `Y_tame_m`. The caller discharges `hYlink` when choosing `F_tame_in_Km` to be
`F ⊓ Km` viewed inside `Km`, so the two character subgroups correspond under `changeLevel`. -/
private lemma prod_chars_tame_descend_to_level_m
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime)
    (Km : IntermediateField ℚ Kn) [NumberField Km] [IsGalois ℚ Km] [IsAbelianGalois ℚ Km]
    [hm_cyclo : IsCyclotomicExtension {Nat.divMaxPow n p} ℚ Km]
    (Y_tame : Subgroup (DirichletCharacter ℂ n))
    (hY_tame : Y_tame =
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ (F ⊓ Km))
    (F_tame_in_Km : IntermediateField ℚ Km)
    [hm_ne : NeZero (Nat.divMaxPow n p)]
    (Y_tame_m : Subgroup (DirichletCharacter ℂ (Nat.divMaxPow n p)))
    (hY_tame_m : Y_tame_m =
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar
        (Nat.divMaxPow n p) Km ℂ F_tame_in_Km)
    (hYlink : ∀ χ : DirichletCharacter ℂ n, χ ∈ Y_tame ↔
      ∃ ψ : DirichletCharacter ℂ (Nat.divMaxPow n p), ψ ∈ Y_tame_m ∧
        DirichletCharacter.changeLevel (divMaxPow_dvd' n p) ψ = χ) :
    ∏ χ : Y_tame, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ χ : Y_tame_m, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ := by
  -- The `changeLevel hm_dvd : DirichletCharacter ℂ m →* DirichletCharacter ℂ n` gives a group
  -- iso `Y_tame_m ≃* Y_tame`. Under this iso, `primitiveCharacter_changeLevel` shows the
  -- evaluated factor is preserved. Reindex the product via this bijection.
  set hm_dvd : Nat.divMaxPow n p ∣ n := divMaxPow_dvd' n p with hm_dvd_def
  -- Bijection `Y_tame_m ≃ Y_tame` induced by `changeLevel hm_dvd`.
  let toFun : Y_tame_m → Y_tame := fun ψ =>
    ⟨DirichletCharacter.changeLevel hm_dvd ψ.val,
      (hYlink _).mpr ⟨ψ.val, ψ.property, rfl⟩⟩
  have hInj : Function.Injective toFun := by
    intro ψ₁ ψ₂ hψ
    apply Subtype.ext
    have := congrArg Subtype.val hψ
    exact DirichletCharacter.changeLevel_injective hm_dvd this
  have hSurj : Function.Surjective toFun := by
    intro χ
    obtain ⟨ψ, hψ_mem, hψ_eq⟩ := (hYlink _).mp χ.property
    exact ⟨⟨ψ, hψ_mem⟩, Subtype.ext hψ_eq⟩
  let e : Y_tame_m ≃ Y_tame := Equiv.ofBijective toFun ⟨hInj, hSurj⟩
  refine (Fintype.prod_equiv e _ _ ?_).symm
  intro ψ
  -- `(e ψ).val = changeLevel hm_dvd ψ.val` by definition of `Equiv.ofBijective`.
  have heval : (e ψ).val = DirichletCharacter.changeLevel hm_dvd ψ.val := rfl
  rw [heval, primitiveCharacter_changeLevel hm_dvd ψ.val p]

/-- **Ramified-case scaffold (c): totally-ramified prime-side reduction.** For `p ∣ n`,
the extension `F/F_tame` (where `F_tame = F ⊓ Km`, `Km = ℚ(ζₘ)`) is totally ramified at every
prime of `F_tame` above `p`. Hence each prime of `F_tame` above `p` has a *unique* prime of
`F` above it with inertia degree `1`, so the absolute norms match
(`absNorm 𝔓 = absNorm 𝔭^{f(𝔓|𝔭)} = absNorm 𝔭`). The resulting bijection
`primesAboveOf F p ≃ primesAboveOf F_tame p` preserves the absolute-norm factor.

Existing API to compose:
* `IsTotallyRamifiedIn.tower` (Mathlib/NumberTheory/RamificationInertia/TotallyRamified.lean) —
  total ramification inherited from `Kn/Km` totally ramified at `p`-primes.
* `IsCyclotomicExtension.relative_of_dvd` — supplies the relative cyclotomic structure
  `Kn = Km(ζ_{p^{padicValNat p n}})` needed to invoke the totally-ramified-at-p result for the
  tower `Km → Kn`. The 7hra.8 follow-up will package this as "primes of `Km` over `p` are totally
  ramified in `Kn`"; this lemma consumes that result.
* `absNorm_eq_pow_inertiaDeg'` — to identify `absNorm 𝔓 = (absNorm 𝔭)^1` when `f(𝔓|𝔭) = 1`. -/
private lemma primesAboveOf_F_tame_eq_F_of_totally_ramified
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {s : ℂ}
    {p : ℕ} (hp : p.Prime) (hp_n_dvd : p ∣ n)
    (Km : IntermediateField ℚ Kn) [NumberField Km] [IsGalois ℚ Km]
    [IsCyclotomicExtension {Nat.divMaxPow n p} ℚ Km]
    (F_tame : IntermediateField ℚ Kn) (hF_tame : F_tame = F ⊓ Km)
    [NumberField (F_tame : Type _)]
    -- Algebra plumbing: F_tame ≤ F gives an algebra structure on F_tame → F, supplied here as an
    -- instance argument. The caller builds it from `IntermediateField.inclusion (le_inf_left)`.
    -- The 𝓞-level algebra and scalar-tower instances follow automatically via
    -- `NumberField.inst_ringOfIntegersAlgebra` and `RingOfIntegers.inst_isScalarTower`.
    [Algebra F_tame F] [IsScalarTower ℚ F_tame F]
    -- The totally-ramified-tower fact: every prime of `𝓞 F_tame` above `p` is totally ramified
    -- in `𝓞 F`. Caller derives this from `relative_isTotallyRamifiedIn` (`Kn/Km` totally ramified
    -- at `p`-primes) plus `IsTotallyRamifiedIn.tower` restriction along `F_tame ≤ F`.
    (hF_tame_ramified : ∀ 𝔭 : Ideal (𝓞 F_tame), 𝔭.IsPrime →
      𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) →
        𝔭.IsTotallyRamifiedIn (𝓞 F)) :
    ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ =
      ∏ 𝔭 ∈ primesAboveOf F_tame p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  -- The bijection `primesAboveOf F p ≃ primesAboveOf F_tame p` sends 𝔓 ↦ 𝔓 ∩ 𝓞 F_tame,
  -- with `absNorm` preserved because `f(𝔓|𝔭) = 1` by total ramification.
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_span_ne : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by simp [hp.ne_zero]
  have h_mem_F : ∀ 𝔓 : Ideal (𝓞 F),
      𝔓 ∈ primesAboveOf F p ↔
        𝔓.IsPrime ∧ 𝔓.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    intro 𝔓
    change 𝔓 ∈ IsDedekindDomain.primesOverFinset _ (𝓞 F) ↔ _
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp_span_ne]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have h_mem_Ft : ∀ 𝔭 : Ideal (𝓞 F_tame),
      𝔭 ∈ primesAboveOf F_tame p ↔
        𝔭.IsPrime ∧ 𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    intro 𝔭
    change 𝔭 ∈ IsDedekindDomain.primesOverFinset _ (𝓞 F_tame) ↔ _
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp_span_ne]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  haveI : Module.Finite (𝓞 F_tame) (𝓞 F) := Module.IsNoetherian.finite _ _
  haveI : NoZeroSMulDivisors (𝓞 F_tame) (𝓞 F) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · left
      exact (FaithfulSMul.algebraMap_injective (𝓞 F_tame) (𝓞 F))
        (by simp [h])
    · right; exact h
  refine Finset.prod_nbij (fun 𝔓 => 𝔓.under (𝓞 F_tame)) ?hi ?hinj ?hsurj ?heq
  · intro 𝔓 h𝔓
    obtain ⟨h𝔓_prime, h𝔓_lies⟩ := (h_mem_F 𝔓).mp h𝔓
    refine (h_mem_Ft _).mpr ⟨Ideal.IsPrime.under (𝓞 F_tame) 𝔓, ?_⟩
    haveI := h𝔓_lies
    exact Ideal.under_liesOver_of_liesOver (B := 𝓞 F_tame) 𝔓 _
  · intro 𝔓₁ h𝔓₁ 𝔓₂ h𝔓₂ heq
    rw [Finset.mem_coe] at h𝔓₁ h𝔓₂
    obtain ⟨h𝔓₁_prime, h𝔓₁_lies⟩ := (h_mem_F 𝔓₁).mp h𝔓₁
    obtain ⟨h𝔓₂_prime, h𝔓₂_lies⟩ := (h_mem_F 𝔓₂).mp h𝔓₂
    set 𝔭 := 𝔓₁.under (𝓞 F_tame) with h𝔭_def
    haveI h𝔭_prime : 𝔭.IsPrime := Ideal.IsPrime.under (𝓞 F_tame) 𝔓₁
    haveI h𝔭_lies : 𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      haveI := h𝔓₁_lies
      exact Ideal.under_liesOver_of_liesOver (B := 𝓞 F_tame) 𝔓₁ _
    haveI h𝔓₁_over_𝔭 : 𝔓₁.LiesOver 𝔭 := ⟨rfl⟩
    haveI h𝔓₂_over_𝔭 : 𝔓₂.LiesOver 𝔭 := ⟨heq⟩
    have h_tr := hF_tame_ramified 𝔭 h𝔭_prime h𝔭_lies
    have h𝔭_ne : 𝔭 ≠ ⊥ := by
      intro hbot
      apply hp_span_ne
      have hover := h𝔭_lies.over
      rw [hbot, Ideal.under_def,
        Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 F_tame))]
        at hover
      exact hover
    haveI h𝔭_max : 𝔭.IsMaximal := h𝔭_prime.isMaximal h𝔭_ne
    obtain ⟨P, hsingle, _, _, _, _⟩ :=
      h_tr.primesOverFinset_eq_singleton F_tame F h𝔭_ne
    have h₁mem : 𝔓₁ ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F) :=
      (IsDedekindDomain.mem_primesOverFinset_iff h𝔭_ne _).mpr ⟨h𝔓₁_prime, h𝔓₁_over_𝔭⟩
    have h₂mem : 𝔓₂ ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F) :=
      (IsDedekindDomain.mem_primesOverFinset_iff h𝔭_ne _).mpr ⟨h𝔓₂_prime, h𝔓₂_over_𝔭⟩
    rw [hsingle, Finset.mem_singleton] at h₁mem h₂mem
    exact h₁mem.trans h₂mem.symm
  · intro 𝔭 h𝔭
    rw [Finset.mem_coe] at h𝔭
    obtain ⟨h𝔭_prime, h𝔭_lies⟩ := (h_mem_Ft 𝔭).mp h𝔭
    have h_tr := hF_tame_ramified 𝔭 h𝔭_prime h𝔭_lies
    obtain ⟨𝔓, h𝔓p, h𝔓o, _, _⟩ := h_tr.exists
    refine ⟨𝔓, ?_, ?_⟩
    · rw [Finset.mem_coe]
      refine (h_mem_F 𝔓).mpr ⟨h𝔓p, ?_⟩
      haveI := h𝔓o
      haveI := h𝔭_lies
      exact Ideal.LiesOver.trans 𝔓 𝔭 _
    · exact h𝔓o.over.symm
  · intro 𝔓 h𝔓
    obtain ⟨h𝔓_prime, h𝔓_lies⟩ := (h_mem_F 𝔓).mp h𝔓
    set 𝔭 := 𝔓.under (𝓞 F_tame) with h𝔭_def
    haveI h𝔭_prime : 𝔭.IsPrime := Ideal.IsPrime.under (𝓞 F_tame) 𝔓
    haveI h𝔭_lies : 𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      haveI := h𝔓_lies
      exact Ideal.under_liesOver_of_liesOver (B := 𝓞 F_tame) 𝔓 _
    haveI h𝔓_over_𝔭 : 𝔓.LiesOver 𝔭 := ⟨rfl⟩
    have h_tr := hF_tame_ramified 𝔭 h𝔭_prime h𝔭_lies
    have h𝔭_ne : 𝔭 ≠ ⊥ := by
      intro hbot
      apply hp_span_ne
      have hover := h𝔭_lies.over
      rw [hbot, Ideal.under_def,
        Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 F_tame))]
        at hover
      exact hover
    haveI h𝔭_max : 𝔭.IsMaximal := h𝔭_prime.isMaximal h𝔭_ne
    obtain ⟨P, hsingle, _, _, _, hPf⟩ :=
      h_tr.primesOverFinset_eq_singleton F_tame F h𝔭_ne
    have h𝔓_mem : 𝔓 ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F) :=
      (IsDedekindDomain.mem_primesOverFinset_iff h𝔭_ne _).mpr ⟨h𝔓_prime, h𝔓_over_𝔭⟩
    rw [hsingle, Finset.mem_singleton] at h𝔓_mem
    have h𝔓_f : Ideal.inertiaDeg 𝔭 𝔓 = 1 := h𝔓_mem ▸ hPf
    have hN := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver (S := 𝓞 F_tame) 𝔓 𝔭 h𝔭_prime h𝔭_ne
    rw [h𝔓_f, pow_one] at hN
    rw [hN]

/-- **Ramified-case scaffold (d): unramified case at the tame level `m`.** With `p.Coprime m`,
the existing unramified result `prod_chars_eq_prod_inertia` applies inside `Km/ℚ` to the
intermediate field `F_tame_in_Km : IntermediateField ℚ Km`, yielding the level-`m` identity.

Existing API to compose:
* `prod_chars_eq_prod_inertia` — the unramified case (taking `n := m`, `Kn := Km`,
  `F := F_tame_in_Km`).
* `primesAboveOf` is defined intrinsically to the field, so the RHS at level `m` over
  `F_tame_in_Km` coincides with `primesAboveOf F_tame p` once `F_tame_in_Km` is identified
  with `F_tame` as a number field (`AlgEquiv` from `IntermediateField.inclusion` /
  `IsCyclotomicExtension.relative_of_dvd`-induced isomorphism). -/
private lemma prod_chars_eq_prod_inertia_tame_m
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime)
    (Km : IntermediateField ℚ Kn) [NumberField Km] [IsGalois ℚ Km]
    [IsCyclotomicExtension {Nat.divMaxPow n p} ℚ Km] [IsAbelianGalois ℚ Km]
    (F_tame : IntermediateField ℚ Kn) (hF_tame : F_tame = F ⊓ Km)
    [NumberField (F_tame : Type _)]
    (F_tame_in_Km : IntermediateField ℚ Km)
    [NumberField (F_tame_in_Km : Type _)]
    [hm_ne' : NeZero (Nat.divMaxPow n p)]
    (Y_tame_m : Subgroup (DirichletCharacter ℂ (Nat.divMaxPow n p)))
    (hY_tame_m : Y_tame_m =
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar
        (Nat.divMaxPow n p) Km ℂ F_tame_in_Km)
    (hp_m : p.Coprime (Nat.divMaxPow n p))
    -- The canonical AlgEquiv `F_tame_in_Km ≃ₐ[ℚ] F_tame`. The two are the same set of elements
    -- viewed inside `Km` resp. `Kn`; the equiv is induced by the inclusion `Km ↪ Kn` restricted
    -- to `F_tame_in_Km`, with image precisely `F_tame = F ⊓ Km`. Caller provides this witness
    -- alongside the existence of `F_tame_in_Km`.
    (φ_F_tame : F_tame_in_Km ≃ₐ[ℚ] F_tame) :
    haveI hm_ne : NeZero (Nat.divMaxPow n p) :=
      ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (divMaxPow_dvd' n p)⟩
    ∏ χ : Y_tame_m, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ 𝔭 ∈ primesAboveOf F_tame p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  haveI hm_ne : NeZero (Nat.divMaxPow n p) :=
    ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (divMaxPow_dvd' n p)⟩
  -- Apply `prod_chars_eq_prod_inertia` at level `m = Nat.divMaxPow n p` to
  -- `F_tame_in_Km : IntermediateField ℚ Km` with character subgroup `Y_tame_m`. The output
  -- `primesAboveOf F_tame_in_Km p` is then identified with `primesAboveOf F_tame p` via the
  -- canonical AlgEquiv `F_tame_in_Km ≃ₐ[ℚ] F_tame` (induced by `IntermediateField.inclusion`
  -- and `hF_tame`).
  -- Step 1: apply unramified result at level m to F_tame_in_Km.
  have h_step1 :
      ∏ χ : Y_tame_m, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
        ∏ 𝔭 ∈ primesAboveOf F_tame_in_Km p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ :=
    prod_chars_eq_prod_inertia F_tame_in_Km Y_tame_m hY_tame_m hp hp_m
  rw [h_step1]
  -- Step 2: transport along `e : 𝓞 F_tame_in_Km ≃+* 𝓞 F_tame` induced by `φ_F_tame`.
  set e : (𝓞 (F_tame_in_Km : Type _)) ≃+* (𝓞 (F_tame : Type _)) :=
    (RingOfIntegers.mapAlgEquiv φ_F_tame).toRingEquiv with he_def
  -- `e` commutes with `algebraMap ℤ _` because the AlgEquiv is over `𝓞 ℚ = ℤ`'s image.
  have hCommAlg : ∀ (x : ℤ), e (algebraMap ℤ _ x) = algebraMap ℤ _ x := fun x => by
    have h := (RingOfIntegers.mapAlgEquiv φ_F_tame).commutes (algebraMap ℤ (𝓞 ℚ) x)
    have h1 : (algebraMap (𝓞 ℚ) (𝓞 (F_tame_in_Km : Type _))) ((algebraMap ℤ (𝓞 ℚ)) x) =
        (algebraMap ℤ (𝓞 (F_tame_in_Km : Type _))) x :=
      (IsScalarTower.algebraMap_apply ℤ (𝓞 ℚ) _ x).symm
    have h2 : (algebraMap (𝓞 ℚ) (𝓞 (F_tame : Type _))) ((algebraMap ℤ (𝓞 ℚ)) x) =
        (algebraMap ℤ (𝓞 (F_tame : Type _))) x :=
      (IsScalarTower.algebraMap_apply ℤ (𝓞 ℚ) _ x).symm
    rw [h1, h2] at h
    exact h
  have hCommAlg' : ∀ (x : ℤ), e.symm (algebraMap ℤ _ x) = algebraMap ℤ _ x := fun x => by
    apply e.injective
    rw [e.apply_symm_apply, hCommAlg]
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  set Ip : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ) with hIp_def
  have hIp_ne : Ip ≠ ⊥ := by simp [hIp_def, hp.ne_zero]
  haveI hIp_max : Ip.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  -- The bijection `Finset.image`-style: 𝔭 ↦ Ideal.map e 𝔭.
  -- Key facts about `Ideal.map e`:
  -- 1. preserves IsPrime (e is bijective)
  -- 2. preserves LiesOver Ip (e commutes with algebraMap ℤ)
  -- 3. preserves absNorm (quotient iso via Ideal.quotientEquiv)
  -- 4. inverse is `Ideal.map e.symm`, so injective and surjective onto primesAboveOf F_tame p.
  -- Generic helper applied at both directions.
  have hUnderEq : ∀ (𝔭 : Ideal (𝓞 (F_tame_in_Km : Type _))),
      (Ideal.map e 𝔭).comap (algebraMap ℤ (𝓞 (F_tame : Type _))) =
        𝔭.comap (algebraMap ℤ (𝓞 (F_tame_in_Km : Type _))) := fun 𝔭 => by
    ext x
    simp only [Ideal.mem_comap]
    rw [← hCommAlg x, Ideal.apply_mem_of_equiv_iff]
  have hUnderEq' : ∀ (𝔭 : Ideal (𝓞 (F_tame : Type _))),
      (Ideal.map e.symm 𝔭).comap (algebraMap ℤ (𝓞 (F_tame_in_Km : Type _))) =
        𝔭.comap (algebraMap ℤ (𝓞 (F_tame : Type _))) := fun 𝔭 => by
    ext x
    simp only [Ideal.mem_comap]
    rw [← hCommAlg' x, Ideal.apply_mem_of_equiv_iff]
  have hMemFwd : ∀ {𝔭 : Ideal (𝓞 (F_tame_in_Km : Type _))},
      𝔭 ∈ primesAboveOf F_tame_in_Km p →
        Ideal.map e 𝔭 ∈ primesAboveOf F_tame p := fun {𝔭} h => by
    rw [primesAboveOf, IsDedekindDomain.mem_primesOverFinset_iff hIp_ne] at h
    rw [primesAboveOf, IsDedekindDomain.mem_primesOverFinset_iff hIp_ne]
    refine ⟨?_, ?_⟩
    · rw [← Ideal.comap_symm e]
      exact h.1.comap _
    · refine ⟨?_⟩
      rw [Ideal.under_def, hUnderEq]
      have := h.2.over; rw [Ideal.under_def] at this; exact this
  have hMemBwd : ∀ {𝔓 : Ideal (𝓞 (F_tame : Type _))},
      𝔓 ∈ primesAboveOf F_tame p →
        Ideal.map e.symm 𝔓 ∈ primesAboveOf F_tame_in_Km p := fun {𝔓} h => by
    rw [primesAboveOf, IsDedekindDomain.mem_primesOverFinset_iff hIp_ne] at h
    rw [primesAboveOf, IsDedekindDomain.mem_primesOverFinset_iff hIp_ne]
    refine ⟨?_, ?_⟩
    · rw [Ideal.map_symm]
      exact h.1.comap _
    · refine ⟨?_⟩
      rw [Ideal.under_def, hUnderEq']
      have := h.2.over; rw [Ideal.under_def] at this; exact this
  have hMapMap_fwd : ∀ (𝔭 : Ideal (𝓞 (F_tame_in_Km : Type _))),
      Ideal.map e.symm (Ideal.map e 𝔭) = 𝔭 := fun 𝔭 =>
    Ideal.map_of_equiv (I := 𝔭) e
  have hMapMap_bwd : ∀ (𝔓 : Ideal (𝓞 (F_tame : Type _))),
      Ideal.map e (Ideal.map e.symm 𝔓) = 𝔓 := fun 𝔓 => by
    have := Ideal.map_of_equiv (I := 𝔓) e.symm
    simp only [RingEquiv.symm_symm] at this
    exact this
  have hAbsNorm : ∀ (𝔭 : Ideal (𝓞 (F_tame_in_Km : Type _))),
      Ideal.absNorm (Ideal.map e 𝔭) = Ideal.absNorm 𝔭 := fun 𝔭 => by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Submodule.cardQuot_apply]
    have heq : (Ideal.map e 𝔭) = 𝔭.map (e : _ →+* _) := rfl
    exact (Nat.card_congr (Ideal.quotientEquiv 𝔭 (Ideal.map e 𝔭) e heq).toEquiv).symm
  refine Finset.prod_bij' (fun 𝔭 _ => Ideal.map e 𝔭)
    (fun 𝔓 _ => Ideal.map e.symm 𝔓) ?_ ?_ ?_ ?_ ?_
  · intro 𝔭 h𝔭; exact hMemFwd h𝔭
  · intro 𝔓 h𝔓; exact hMemBwd h𝔓
  · intro 𝔭 _; exact hMapMap_fwd 𝔭
  · intro 𝔓 _; exact hMapMap_bwd 𝔓
  · intro 𝔭 _; rw [hAbsNorm]

/-- **Ramified-case Step B.** For `p ∣ n` and `F` an intermediate field of `ℚ(ζₙ)/ℚ`, the
character product `∏ χ : Y, (1 - χ.val.primitiveCharacter p * T)⁻¹` equals the prime product
`∏ 𝔭 ∈ primesAboveOf F p, (1 - absNorm 𝔭^(-s))⁻¹`.

This wires together four sub-lemmas (each independently provable):
1. `prod_chars_ramified_LHS_eq_prod_tame` — Phase 2 + tame intersection (character side).
2. `prod_chars_tame_descend_to_level_m` — level-`n` to level-`m` descent via `changeLevel`.
3. `prod_chars_eq_prod_inertia_tame_m` — unramified case at the tame level `m`.
4. `primesAboveOf_F_tame_eq_F_of_totally_ramified` — totally-ramified tower (prime side). -/
private lemma prod_chars_eq_prod_inertia_ramified
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime) (hp_n_dvd : p ∣ n) :
    ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  -- Tame level m = divMaxPow n p, and the tame cyclotomic subfield Km = ℚ(ζₘ) ⊆ Kn.
  set m := Nat.divMaxPow n p with hm_def
  have hm_dvd : m ∣ n := divMaxPow_dvd' n p
  have hp_m : p.Coprime m := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_divMaxPow hp.one_lt (NeZero.ne n)
  haveI hm_ne : NeZero m := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) hm_dvd⟩
  let ζn := IsCyclotomicExtension.zeta n ℚ Kn
  have hζn := IsCyclotomicExtension.zeta_spec n ℚ Kn
  have hn_eq : n = p ^ padicValNat p n * m := (Nat.pow_padicValNat_mul_divMaxPow p n).symm
  let ζm := ζn ^ (p ^ padicValNat p n)
  have hζm : IsPrimitiveRoot ζm m := hζn.pow (NeZero.pos n) hn_eq
  let Km : IntermediateField ℚ Kn := IntermediateField.adjoin ℚ ({ζm} : Set Kn)
  haveI hKm_cyclo : IsCyclotomicExtension {m} ℚ Km :=
    hζm.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  haveI hKm_galois : IsGalois ℚ Km := IsCyclotomicExtension.isGalois {m} ℚ Km
  haveI hKm_abelian : IsAbelianGalois ℚ Km := IsCyclotomicExtension.isAbelianGalois {m} ℚ Km
  haveI hKm_nf : NumberField Km := inferInstance
  let F_tame : IntermediateField ℚ Kn := F ⊓ Km
  haveI hF_tame_nf : NumberField (F_tame : Type _) := inferInstance
  -- Algebra plumbing: F_tame ≤ F induces an Algebra structure F_tame → F via inclusion.
  have hF_tame_le : F_tame ≤ F := inf_le_left
  letI algFtF : Algebra F_tame F := (IntermediateField.inclusion hF_tame_le).toAlgebra
  haveI : IsScalarTower ℚ F_tame F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Tame character subgroup at level n.
  let Y_tame : Subgroup (DirichletCharacter ℂ n) :=
    IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F_tame
  have hY_tame : Y_tame =
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ (F ⊓ Km) := rfl
  -- Tame intermediate field viewed inside Km, and the level-m tame character subgroup, plus the
  -- canonical AlgEquiv F_tame_in_Km ≃ₐ[ℚ] F_tame and the totally-ramified-tower fact for the
  -- F_tame ⊆ F extension at primes above p. Each of the five witnesses is now a separate `have`
  -- with its own sorry, so they can be discharged independently (P2/P3/etc).
  -- Witness 1: tame intermediate field viewed inside Km.
  let F_tame_in_Km : IntermediateField ℚ Km :=
    IntermediateField.restrict (inf_le_right : F ⊓ Km ≤ Km)
  -- Witness 2: F_tame_in_Km is a number field (auto-derived from Km being a NumberField).
  haveI hF_tame_in_Km_nf : NumberField (F_tame_in_Km : Type _) := inferInstance
  -- Witness 3: level-m tame character subgroup plus the changeLevel bridge to level-n.
  have h_Y_tame_m : ∃ Y_tame_m : Subgroup (DirichletCharacter ℂ m),
      Y_tame_m =
        IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar m Km ℂ F_tame_in_Km ∧
      (∀ χ : DirichletCharacter ℂ n, χ ∈ Y_tame ↔
        ∃ ψ : DirichletCharacter ℂ m, ψ ∈ Y_tame_m ∧
          DirichletCharacter.changeLevel (divMaxPow_dvd' n p) ψ = χ) := by
    refine ⟨IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar m Km ℂ F_tame_in_Km,
      rfl, fun χ => ?_⟩
    exact IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_changeLevel
      (n := n) (K := Kn) (R := ℂ) (m := m) (hmn := divMaxPow_dvd' n p) Km
      (F_tame := F ⊓ Km) (hF_le := inf_le_right) χ
  obtain ⟨Y_tame_m, hY_tame_m, hYlink⟩ := h_Y_tame_m
  -- Witness 4: canonical AlgEquiv F_tame_in_Km ≃ₐ[ℚ] F_tame.
  have hφ_F_tame : Nonempty (F_tame_in_Km ≃ₐ[ℚ] F_tame) :=
    ⟨(IntermediateField.restrict_algEquiv (inf_le_right : F ⊓ Km ≤ Km)).symm⟩
  obtain ⟨φ_F_tame⟩ := hφ_F_tame
  -- Witness 5: every prime of 𝓞 F_tame above (p) is totally ramified in 𝓞 F.
  have hF_tame_ramified : ∀ 𝔭 : Ideal (𝓞 F_tame), 𝔭.IsPrime →
      𝔭.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) →
        𝔭.IsTotallyRamifiedIn (𝓞 F) := by sorry
  haveI : NumberField (F_tame_in_Km : Type _) := hF_tame_in_Km_nf
  -- Compose the four sub-lemmas.
  calc ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹
      = ∏ χ : Y_tame, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ :=
        prod_chars_ramified_LHS_eq_prod_tame F Y hY hp Km Y_tame hY_tame
    _ = ∏ χ : Y_tame_m, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ :=
        prod_chars_tame_descend_to_level_m F hp Km Y_tame hY_tame F_tame_in_Km Y_tame_m hY_tame_m
          hYlink
    _ = ∏ 𝔭 ∈ primesAboveOf F_tame p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ :=
        prod_chars_eq_prod_inertia_tame_m F hp Km F_tame rfl F_tame_in_Km
          Y_tame_m hY_tame_m hp_m φ_F_tame
    _ = ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ :=
        (primesAboveOf_F_tame_eq_F_of_totally_ramified F hp hp_n_dvd Km F_tame rfl
          hF_tame_ramified).symm

/-- **Step B (unconditional).** The product of primitive Dirichlet local Euler factors over the
character group `Y` equals the product of geometric series over primes above `p`.

Extends `prod_chars_eq_prod_inertia` to all primes, including ramified ones (`p ∣ n`), by
tame-level reduction: for `p ∣ n`, factor through `m = Nat.divMaxPow n p` where `p ∤ m`. -/
theorem prod_chars_eq_prod_inertia_general
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime) :
    ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  by_cases hp_n : p.Coprime n
  · exact prod_chars_eq_prod_inertia F Y hY hp hp_n
  · rw [Nat.Prime.coprime_iff_not_dvd hp, not_not] at hp_n
    exact prod_chars_eq_prod_inertia_ramified F Y hY hp hp_n

/-- **Local-factor matching (unconditional).** For an intermediate field `F` of `ℚ(ζₙ)/ℚ` and
any rational prime `p`, the prime-power Dedekind summand at `p` factorizes as a product of
primitive Dirichlet local Euler factors. This extends the unramified-case result to all primes. -/
theorem dedekindZeta_localFactor_eq_prod_dirichletLocal_general
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ} (hs : 1 < s.re)
    {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, dedekindZetaSummand F s (p ^ e) =
      ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ := by
  rw [dedekindZetaSummand_localSum_eq_prod_inertia (F := F) hp hs,
      ← prod_chars_eq_prod_inertia_general F Y hY hp]

/-! ### The global Dedekind zeta factorization theorem

The classical theorem `dedekindZeta F s = ∏ χ : Y, L(χ.primitiveCharacter, s)` follows by
composing the per-prime local factor identity (for all primes `p`) with the prime-by-prime ↔
character-by-character product swap. -/

/-- **Global Dedekind–Dirichlet factorization.** For an abelian number field `F` contained in
the cyclotomic field `ℚ(ζₙ)`, the Dedekind zeta function of `F` factorizes as a product of
primitive Dirichlet L-functions over the character group `Y ⊆ Xₙ` associated to `F`.

This is the classical factorization underlying analytic class field theory, expressed here via
the per-prime Euler product identity at all primes. -/
theorem dedekindZeta_eq_prod_dirichletL_abelian
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (F : Type _) s =
      ∏ χ : Y, DirichletCharacter.LFunction χ.val.primitiveCharacter s := by
  -- Rewrite dedekindZeta as an Euler tprod over primes.
  rw [← dedekindZeta_eulerProduct_tprod (F : Type _) s hs]
  -- Substitute the per-prime local factor identity (all primes), then swap tprod and prod.
  -- First: rewrite each summand ∑ e, f(p,e) → ∏ χ, (1 - χ(p) * p^(-s))⁻¹ inside the tprod.
  conv_lhs =>
    congr
    ext p
    rw [dedekindZeta_localFactor_eq_prod_dirichletLocal_general F Y hY hs p.property]
  -- Now apply the prime-character product swap: ∏' p, ∏ χ, g(p,χ) = ∏ χ, ∏' p, g(p,χ).
  exact prod_dirichletLocal_eq_prod_LFunction Y hs

end NumberField
