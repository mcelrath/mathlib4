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

/-!
# The Dedekind zeta function of an abelian number field as a product of Dirichlet L-functions

For an abelian Galois extension `K/ℚ`, the Kronecker–Weber theorem embeds `K` into a cyclotomic
field `ℚ(ζₙ)`, and the Galois group `Gal(K/ℚ)` becomes a quotient of `(ℤ/nℤ)ˣ`. The
Pontryagin dual `Gal(K/ℚ)^∨` is then identified with a subgroup `Y` of the Dirichlet
character group `Xₙ` via `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar`.

In this regime the Dedekind zeta function factorizes as

  `dedekindZeta K s = ∏ χ ∈ Y, DirichletCharacter.LFunction χ s`   (for `1 < re s`).

This identity is foundational for class-field-theoretic constructions over abelian extensions
of `ℚ`, including computations of L-values, density theorems, and Generalized Riemann Hypothesis
chains in applied frameworks. The current file establishes the **statement** of the abelian
factorization (`dedekindZeta_eq_prod_dirichletL_abelian`), provides a clean `tprod`-form of the
prime-power Euler product for the Dedekind zeta (`dedekindZeta_eulerProduct_tprod`), and stubs
the two non-trivial intermediate steps:

* the *local-factor matching* between `idealNormCount`-driven prime-power sums and the standard
  L-function geometric series at primes coprime to the conductor
  (`dedekindZeta_localFactor_eq_prod_dirichletLocal`), and
* the *conductor-character correspondence* tying the local factor at `p` to a product over the
  character group `Y` (`prod_dirichletLocal_eq_prod_LFunction`).

## Status

* `dedekindZeta_eulerProduct_tprod` — proved (drop-in `tprod` reformulation of the existing
  prime-power Euler product `NumberField.dedekindZeta_eulerProduct`).
* `dedekindZeta_localFactor_eq_prod_dirichletLocal` — stated, sorry.
* `prod_dirichletLocal_eq_prod_LFunction` — stated, sorry.
* `dedekindZeta_eq_prod_dirichletL_abelian` — stated, sorry; proof is to assemble the two
  intermediate steps via the existing `dedekindZetaSummand_isMultiplicative`.

Multiplicativity of `idealNormCount` (the splitting of `idealNormCount K (m * n)` for coprime
`m, n`) is already provided upstream as
`NumberField.idealNormCount_isMultiplicative` /
`NumberField.idealNormCount_mul_of_coprime` in
`Mathlib.NumberTheory.NumberField.DedekindZetaEulerProduct`.

## TODO

Assemble `dedekindZeta_eq_prod_dirichletL_abelian` once the two local-factor / conductor-matching
sorries are filled.
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

The local Euler factor of `dedekindZeta K` at the rational prime `p` is the inner sum
`∑' e, dedekindZetaSummand K s (p ^ e)`. For `p` coprime to the conductor of `K/ℚ`, this
equals the product of geometric series `∏_{𝔭∣p} (1 - N(𝔭)^(-s))^(-1)` indexed by the prime
ideals of `𝓞 K` above `p`. The next step ties each `(1 - N(𝔭)^(-s))^(-1)` to a Dirichlet
L-Euler factor via Frobenius compatibility.
-/

/-- **Local-factor matching (sorry).** For an abelian extension `K/ℚ` of conductor `n`, and a
rational prime `p` coprime to `n`, the prime-power Dedekind summand
`∑' e, dedekindZetaSummand K s (p^e)` factorizes as a product of Dirichlet local Euler factors
indexed by the character group `Y` corresponding to `K`.

This is the non-trivial local statement: it reduces to the identity
`∑_{n ≥ 0} a_{p^n} p^{-ns} = ∏_χ (1 - χ(p) p^{-s})^{-1}`,
where `a_m = idealNormCount K m`, holding because the Frobenius at `p` acts on the prime
ideals above `p` via `galEquivZMod n K (Frob_p)`, and the cycle structure determines both
the inertia degrees `f(𝔭∣p)` and the character values `χ(p)`.

The proof in a follow-on session uses
`IsCyclotomicExtension.Rat.galEquivZMod_stabilizer` to identify the Frobenius image, and
unique factorization of `p · 𝓞_K` together with `dedekindZetaSummand_isMultiplicative`. -/
theorem dedekindZeta_localFactor_eq_prod_dirichletLocal
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    (Y : Subgroup (DirichletCharacter ℂ n))
    (hY : Y = IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F)
    {s : ℂ} (hs : 1 < s.re)
    {p : ℕ} (hp : p.Prime) (hpn : p.Coprime n) :
    ∑' e : ℕ, dedekindZetaSummand F s (p ^ e) =
      ∏ χ : Y, (1 - (χ.val p : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
  sorry

/-! ### Character-group product assembly

Given the per-prime local factor, the global identity follows by taking the product over
primes and exchanging it with the product over characters (a finite group), using
absolute convergence (`summable_dedekindZetaSummand`) on the analytic side and
`DirichletCharacter.LSeries_eulerProduct_tprod` on the L-function side.

The conductor-coprime hypothesis above is harmless for primes dividing `n`, since
`χ p = 0` exactly when `p ∣ conductor χ`, and the corresponding `dedekindZeta` local
factor at a ramified prime then matches the omitted geometric term.
-/

/-- **Character-group product (sorry).** The prime-by-prime product of Dirichlet local Euler
factors over a character subgroup `Y` reassembles to a product of L-functions over `Y`. -/
theorem prod_dirichletLocal_eq_prod_LFunction
    {n : ℕ} [NeZero n] (Y : Subgroup (DirichletCharacter ℂ n)) {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, ∏ χ : Y, (1 - (χ.val p : ℂ) * (p : ℂ) ^ (-s))⁻¹ =
      ∏ χ : Y, DirichletCharacter.LFunction χ.val s := by
  sorry

/-! ### The main theorem

The Dedekind zeta function of an abelian number field equals the product of Dirichlet
L-functions indexed by the corresponding character group, on the absolute-convergence
half-plane.

The proof is by composition: rewrite `dedekindZeta` via `dedekindZeta_eulerProduct_tprod`,
substitute each local factor using `dedekindZeta_localFactor_eq_prod_dirichletLocal`, and
collapse the iterated product via `prod_dirichletLocal_eq_prod_LFunction`.
-/

/-- **Abelian factorization of the Dedekind zeta function.** For an intermediate field `F` of
the cyclotomic extension `ℚ(ζₙ)/ℚ` (necessarily abelian over `ℚ`), the Dedekind zeta function
of `F` equals the product of Dirichlet L-functions over the character subgroup
`Y := intermediateFieldEquivSubgroupChar n Kn ℂ F`. -/
theorem dedekindZeta_eq_prod_dirichletL_abelian
    {n : ℕ} [NeZero n] {Kn : Type*} [Field Kn] [NumberField Kn]
    [IsCyclotomicExtension {n} ℚ Kn] [IsAbelianGalois ℚ Kn]
    (F : IntermediateField ℚ Kn) [NumberField F]
    {s : ℂ} (hs : 1 < s.re) :
    let Y := IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n Kn ℂ F
    dedekindZeta F s = ∏ χ : Y, DirichletCharacter.LFunction χ.val s := by
  sorry

end NumberField
