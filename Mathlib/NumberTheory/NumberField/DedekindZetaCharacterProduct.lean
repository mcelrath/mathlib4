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
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.DedekindZetaEulerProduct
public import Mathlib.RingTheory.DedekindDomain.IdealsOnPrimes

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

* `dedekindZeta_eulerProduct_tprod` — proved (drop-in `tprod` reformulation of the existing
  prime-power Euler product `NumberField.dedekindZeta_eulerProduct`).
* `prod_dirichletLocal_eq_prod_LFunction` — proved (per-prime ↔ per-character product swap
  via `Multipliable.tprod_finsetProd`).
* `dedekindZeta_localFactor_eq_prod_dirichletLocal` — stated with sorry; the deep
  Frobenius-cycle local-factor identity at every rational prime, including ramified primes.
* `dedekindZeta_eq_prod_dirichletL_abelian` — proved modulo the local-factor sorry; assembles
  the three pieces above.

Multiplicativity of `idealNormCount` (the splitting of `idealNormCount K (m * n)` for coprime
`m, n`) is already provided upstream as
`NumberField.idealNormCount_isMultiplicative` /
`NumberField.idealNormCount_mul_of_coprime` in
`Mathlib.NumberTheory.NumberField.DedekindZetaEulerProduct`.

## TODO

Discharge `dedekindZeta_localFactor_eq_prod_dirichletLocal`. The proof at unramified primes
follows the standard Frobenius-cycle argument; ramified primes require
`changeLevel_primitiveCharacter` + the local Euler factor identity for cyclotomic L-functions.
-/

@[expose] public section

noncomputable section

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

/-- **Step B (character side, sorry).** The product of primitive Dirichlet local Euler factors
over the character group `Y` equals the product of geometric series over primes above `p` (in
absolute-norm form). Reduces to (i) Frobenius compatibility
`χ.primitiveCharacter p = χ (σ_p)` via `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer`;
(ii) the abelian cyclic-group character identity
`∏_{χ ∈ Y} (1 - χ(g) T) = (1 - T^{ord g})^{|Y|/ord g}` (each value `χ(g)` cycles through the
`(ord g)`-th roots of unity, each appearing `|Y|/ord g` times); (iii) the orbit count
`|Y|/ord(σ_p) = #(primesAbove p)` and `inertiaDeg 𝔭 = ord(σ_p)` for each `𝔭∣p` (decomposition
group is cyclic in the abelian-Galois case). -/
theorem prod_chars_eq_prod_inertia
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ} (hs : 1 < s.re)
    {p : ℕ} (hp : p.Prime) :
    ∏ χ : Y, (1 - χ.val.primitiveCharacter (p : ℕ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  sorry

/-- **Local-factor matching.** For an intermediate field `F` of `ℚ(ζₙ)/ℚ`, the prime-power
Dedekind summand at any rational prime `p` factorizes as a product of primitive Dirichlet local
Euler factors indexed by the character subgroup `Y` corresponding to `F`. Composes Step A
(`dedekindZetaSummand_localSum_eq_prod_inertia`) and Step B (`prod_chars_eq_prod_inertia`). -/
theorem dedekindZeta_localFactor_eq_prod_dirichletLocal
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
      ← prod_chars_eq_prod_inertia F Y hY hs hp]

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

/-! ### The main theorem

The Dedekind zeta function of an abelian number field equals the product of Dirichlet
L-functions (in their *primitive* form) indexed by the corresponding character group, on
the absolute-convergence half-plane.

The proof is by composition: rewrite `dedekindZeta` via `dedekindZeta_eulerProduct_tprod`,
substitute each local factor using `dedekindZeta_localFactor_eq_prod_dirichletLocal`, and
collapse the iterated product via `prod_dirichletLocal_eq_prod_LFunction`.
-/

/-- **Abelian factorization of the Dedekind zeta function.** For an intermediate field `F` of
the cyclotomic extension `ℚ(ζₙ)/ℚ` (necessarily abelian over `ℚ`), the Dedekind zeta function
of `F` equals the product of *primitive* Dirichlet L-functions over the character subgroup
`Y := intermediateFieldEquivSubgroupChar n Kn ℂ F`. -/
theorem dedekindZeta_eq_prod_dirichletL_abelian
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {s : ℂ} (hs : 1 < s.re) :
    let Y := IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F
    dedekindZeta F s =
      ∏ χ : Y, DirichletCharacter.LFunction χ.val.primitiveCharacter s := by
  intro Y
  rw [← dedekindZeta_eulerProduct_tprod F s hs,
      tprod_congr (fun p : Nat.Primes =>
        dedekindZeta_localFactor_eq_prod_dirichletLocal F Y rfl hs p.2)]
  exact prod_dirichletLocal_eq_prod_LFunction Y hs

end NumberField
