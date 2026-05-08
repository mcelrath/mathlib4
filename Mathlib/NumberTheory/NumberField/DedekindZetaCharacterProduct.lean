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
public import Mathlib.NumberTheory.RamificationInertia.Galois
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
- Identify the quotient cardinality as `|Y|/e` via second-isomorphism + Galois inertia.

Sub-sorries:
- `hYp_eq`: `subgroupOfCoprimeConductor p = dual of (ZMod.unitsMap hm_dvd).ker`
  (requires `factorsThrough_iff_ker_unitsMap` + `Nat.Coprime.conductor_dvd` chain)
- `hInter` (RHS rewriting): intersection as dual of join via `OrderIso.map_sup`
- final sorry: `|(ZMod n)ˣ ⧸ (H_map ⊔ I_p)| = |Y|/e` via 2nd isomorphism + inertia count
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
  -- Sub-step A (sorry): subgroupOfCoprimeConductor p = dual of I_p under
  -- subgroupOrderIsoSubgroupMulChar.
  -- Proof chain: p.Coprime χ.conductor
  --   ↔ χ.conductor ∣ Nat.divMaxPow n p  (since χ.conductor ∣ n, p ∤ divMaxPow n p)
  --   ↔ FactorsThrough χ (Nat.divMaxPow n p)  (conductor_dvd and factorsThrough)
  --   ↔ (ZMod.unitsMap hm_dvd).ker ≤ χ.toUnitHom.ker  (factorsThrough_iff_ker_unitsMap)
  --   ↔ ∀ u ∈ I_p, χ.toUnitHom u = 1  (definition of ker ≤ ker)
  --   ↔ ∀ u ∈ I_p, χ u = 1            (by coe_toUnitHom)
  --   ↔ χ ∈ (subgroupOrderIsoSubgroupMulChar ... I_p).ofDual
  --     (by mem_subgroupOrderIsoSubgroupMulChar_iff).
  have hYp_eq : DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := n) p =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ I_p).ofDual := by
    sorry
  -- Sub-step B: Y = dual of H_map under subgroupOrderIsoSubgroupMulChar.
  -- From mem_intermediateFieldEquivSubgroupChar_iff:
  --   χ ∈ Y ↔ ∀ σ ∈ F.fixingSubgroup, χ (galEquivZMod n Kn σ) = 1
  -- From Subgroup.mem_map (H_map = mapSubgroup(F.fixingSubgroup)):
  --   u ∈ H_map ↔ ∃ σ ∈ F.fixingSubgroup, galEquivZMod n Kn σ = u
  -- Combined with mem_subgroupOrderIsoSubgroupMulChar_iff:
  --   χ ∈ (subgroupOrderIsoSubgroupMulChar ... H_map).ofDual ↔ ∀ u ∈ H_map, χ u = 1
  --   ↔ ∀ σ ∈ F.fixingSubgroup, χ (galEquivZMod n Kn σ) = 1  ↔ χ ∈ Y.
  have hY_eq : Y = (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ H_map).ofDual := by
    rw [hY]
    ext χ
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff,
        IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff]
    constructor
    · intro h u hu
      -- hu : u ∈ H_map = mapSubgroup(F.fixingSubgroup) = Subgroup.map galEquivZMod F.fixingSubgroup
      simp only [H_map, MulEquiv.coe_mapSubgroup, Subgroup.mem_map] at hu
      obtain ⟨σ, hσ, rfl⟩ := hu
      exact h σ hσ
    · intro h σ hσ
      -- galEquivZMod σ ∈ H_map since σ ∈ F.fixingSubgroup.
      apply h
      simp only [H_map, MulEquiv.coe_mapSubgroup, Subgroup.mem_map]
      exact ⟨σ, hσ, rfl⟩
  -- Sub-step C: Y ⊓ Y_p = dual of (H_map ⊔ I_p).
  -- subgroupOrderIsoSubgroupMulChar : Subgroup Mˣ ≃o (Subgroup (MulChar M R))ᵒᵈ
  -- preserves ⊔ (order-isomorphism). Taking ofDual converts ⊔ᵒᵈ to ⊓.
  have hInter : Y ⊓ DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := n) p =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ (H_map ⊔ I_p)).ofDual := by
    rw [hY_eq, hYp_eq]
    -- Goal: (iso H_map).ofDual ⊓ (iso I_p).ofDual = (iso (H_map ⊔ I_p)).ofDual
    -- Use ← ofDual_sup: ofDual a ⊓ ofDual b = ofDual (a ⊔ b), then ← map_sup.
    rw [← ofDual_sup, ← (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ).map_sup]
  -- Sub-step D: cardinality via card_subgroupOrderIsoSubgroupMulChar.
  rw [hInter]
  simp only [MulChar.card_subgroupOrderIsoSubgroupMulChar]
  -- Goal: Nat.card ((ZMod n)ˣ ⧸ (H_map ⊔ I_p)) = Nat.card Y / ramificationIdxIn p (𝓞 F).
  -- Sub-step E (sorry): arithmetic identity.
  -- (a) |Y| = |(ZMod n)ˣ ⧸ H_map| via hY_eq + card_subgroupOrderIsoSubgroupMulChar.
  -- (b) |(ZMod n)ˣ ⧸ (H_map ⊔ I_p)| = |(ZMod n)ˣ| / |H_map ⊔ I_p|.
  -- (c) |H_map ⊔ I_p| / |H_map| = |I_p| / |H_map ∩ I_p| (2nd isomorphism theorem).
  -- (d) |I_p / (H_map ∩ I_p)| = ramificationIdxIn p (𝓞 F):
  --     under galEquivZMod, I_p corresponds to the inertia group of p in Kn/ℚ;
  --     H_map ∩ I_p corresponds to the inertia of p within the fixing group of F;
  --     the quotient = inertia group of p in F/ℚ, order = ramificationIdxIn p (𝓞 F)
  --     (by card_inertia_eq_ramificationIdxIn).
  sorry

/-- **Phase 4 (sorry).** The image of `evalAtPrime` is cyclic of order equal to the
inertia degree. This is the Frobenius identification: the eval at `p` corresponds to
evaluating the Galois character at the Frobenius element σ_p ∈ Gal(F/ℚ), whose order
in Gal(F/ℚ) modulo inertia equals the inertia degree. -/
private lemma evalAtPrime_card_range_eq_inertiaDegIn_sorry
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {p : ℕ} (hp : p.Prime) :
    Nat.card (evalAtPrime Y p).range =
      Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 F) := by
  sorry

/-- **Phase 5 (sorry).** The kernel of `evalAtPrime` has cardinality equal to the number
of primes of `𝓞 F` above `p`. By the fundamental identity `e·f·g = [F:ℚ] = |Y|` and the
orbit-stabilizer characterization, kernel size = `|Y|/(e·f)` = orbit count. -/
private lemma evalAtPrime_card_ker_eq_primesAbove_sorry
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {p : ℕ} (hp : p.Prime) :
    Nat.card (evalAtPrime Y p).ker = (primesAboveOf F p).card := by
  sorry

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

/-- **B.1+B.4 LHS reduction.** The character-side product collapses to the same
geometric form as the prime-side, namely `((1 - p^(-fs))⁻¹)^g`. Composes Phase 2
(restriction to coprime conductors), Phase 3 (eval hom + multiplicativity), the abstract
orthogonality lemma `prod_one_sub_groupHom_apply_mul`, and the Frobenius/orbit-count
identifications (Phase 4 + 5, isolated as named sub-sorries). -/
private lemma prod_chars_eq_pow_of_inertiaDegIn_sorry
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ}
    {p : ℕ} (hp : p.Prime) :
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
  rw [evalAtPrime_card_range_eq_inertiaDegIn_sorry F Y hY hp,
      evalAtPrime_card_ker_eq_primesAbove_sorry F Y hY hp]
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
* the character-side reduction (`prod_chars_eq_pow_of_inertiaDegIn_sorry`), which uses
  Frobenius identification (B.1) and the orbit count (B.4).
-/
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
  rw [prod_chars_eq_pow_of_inertiaDegIn_sorry F Y hY hp,
      ← prod_inertia_eq_pow_of_inertiaDegIn (n := n) F hp]

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
