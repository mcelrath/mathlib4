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

/-- **Step A (sorry).** The prime-power Dedekind summand factorizes as a product
of geometric series over the primes of `𝓞 F` lying above `p`. Reduces to (i) the bijection
between ideals of `𝓞 F` of norm `p^e` and tuples `(k_𝔭)_𝔭∣p ∈ (primesAbove p) → ℕ` with
`∑ k_𝔭 · inertiaDeg 𝔭 = e`, given by unique factorization; (ii) Fubini-swap
`∑'e ∑'(k:tuple,sum=e) X = ∑'(k:tuple) X = ∏_𝔭 ∑'k_𝔭 X` for absolutely-convergent geometric
series; (iii) the geometric-series step `tsum_absNorm_pow_neg_geom` above. -/
theorem dedekindZetaSummand_localSum_eq_prod_inertia
    (F : Type*) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ∑' e : ℕ, dedekindZetaSummand F s (p ^ e) =
      ∏ 𝔭 ∈ primesAboveOf F p, (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  sorry

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
