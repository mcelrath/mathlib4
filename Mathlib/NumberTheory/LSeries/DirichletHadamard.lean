/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.SpecialFunctions.Gamma.VerticalBounds
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Hadamard factorization of completed Dirichlet L-functions

For a primitive Dirichlet character `χ` of conductor `N ≥ 1`, the completed L-function
`completedLFunction χ` is entire (when `χ ≠ 1`) and of order ≤ 1. By the Hadamard factorization
theorem for entire functions of order 1, it admits a product representation over its zeros.

## Main results

* `DirichletCharacter.completedLFunction_vertical_bound` (sorry): polynomial growth bound
  `‖completedLFunction χ s‖ ≤ C · (1 + |Im s|)^k` uniformly in vertical strips.

* `DirichletCharacter.completedLFunction_order_le_one` (sorry): growth bound implying analytic
  order ≤ 1. Currently stated as an exponential bound `‖Λ(χ,s)‖ ≤ C · exp(‖s‖^(1+ε))`.

* `DirichletCharacter.completedLFunction_hadamard_factorization` (sorry): for nontrivial
  primitive `χ`, there exist `a b : ℂ` and an (at most countable) multiset of zeros `ρ` such that
  ```
  completedLFunction χ s = exp (a + b * s) * ∏' ρ, ((1 - s / ρ) * exp (s / ρ))
  ```
  with the product converging absolutely and uniformly on compact subsets of `ℂ`.

* `DirichletCharacter.completedLFunction_logDeriv_eq_sum_zeros` (sorry): the logarithmic
  derivative equals
  ```
  deriv (completedLFunction χ) s / completedLFunction χ s = b + ∑' ρ, (1/(s - ρ) + 1/ρ)
  ```

## Status and blockers

`completedLFunction_vertical_bound` and `completedLFunction_order_le_one` are closable once
one missing Stirling-type lemma is added to Mathlib (see below). The Hadamard factorization
theorems have a deeper blocker.

### Blocker B1: Stirling bound for `gammaFactor` in vertical strips (closable, ~2 weeks)

The proof of `completedLFunction_vertical_bound` requires a bound of the form
  `‖Gammaℝ (s + a)‖ ≤ C · (1 + |Im s|)^k · exp (π * |Im s| / 2)`
for `s` in a vertical strip `σ_min ≤ Re s ≤ σ_max`, where `a = 0` (even character) or `a = 1`
(odd character). The Gamma function on **pure imaginary** arguments is controlled by
`Mathlib.Analysis.SpecialFunctions.Gamma.VerticalBounds.Gamma_vertical_bound`, which gives
  `‖Γ(n + it)‖ ≤ n! · (2√π) · (1 + |t|)^n · exp(−π|t|/2)`
for integers `n`. The needed extension is:

  **Missing**: `Gamma_vertical_strip_bound` — for all `σ ∈ [σ_min, σ_max]` and all `t : ℝ` with
  `|t| ≥ 1`, `‖Γ(σ + it)‖ ≤ C(σ_min, σ_max) · (1 + |t|)^k · exp(−π|t|/2)`.

  This follows from `Gamma_vertical_bound` at the integer endpoints plus the three-lines theorem
  (`Complex.HadamardThreeLines`) applied to `Γ` on the strip `[σ_min, σ_max]`, combined with
  the reflection formula `Gamma_mul_Gamma_one_sub` to handle negative real parts. The argument
  is standard (see e.g. Iwaniec–Kowalski §5.1) but has not been formalized in Mathlib.

### Blocker B2: Hadamard factorization for order-1 entire functions (deep, ~4–8 weeks)

`completedLFunction_hadamard_factorization` and `completedLFunction_logDeriv_eq_sum_zeros`
require the Hadamard product theorem for entire functions of finite order. Mathlib has:
- `Complex.HadamardThreeLines` (Hadamard three-lines / interpolation inequality) — NOT the
  product theorem.
- No `Complex.entireFunction_order` (definition of analytic order / exponent of convergence).
- No `Complex.Weierstrass.canonicalProduct` (Weierstrass primary factors).
- No `Complex.Hadamard.factorizationOfOrder1` (the product theorem itself).

Required new Mathlib declarations (to be contributed upstream):
1. `Complex.entireOrder` : `(ℂ → ℂ) → ℝ≥0∞` — order of an entire function as
   `limsup_{r→∞} log log M(r) / log r`, where `M(r) = sup_{|z|=r} ‖f z‖`.
2. `Complex.WeierstrассProduct.convergent` — the canonical product `∏ₙ E_p(z/aₙ)` converges
   locally uniformly when the exponent of convergence of `{aₙ}` is finite.
3. `Complex.Hadamard.factorizationOfOrder1` — for `f` entire of order ≤ 1, `f = e^(a+bz) · ∏ₙ`.

## References

* Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
* Iwaniec–Kowalski, *Analytic Number Theory*, §5.1–5.6.
* Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §2.1–2.12.
-/

open Complex

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-! ### Vertical strip growth bound -/

/-- **Polynomial growth of `completedLFunction χ` in vertical strips**.

For a nontrivial primitive character `χ`, the completed L-function satisfies
  `‖completedLFunction χ s‖ ≤ C · (1 + |Im s|)^k`
uniformly for `s` in any vertical strip `σ_min ≤ Re s ≤ σ_max`.

Proof outline (classical, see Davenport Ch. 12, Iwaniec–Kowalski §5.4):
- **Right edge** `Re s ≥ 2`: the Dirichlet series `∑ χ(n)/nˢ` converges absolutely, giving
  `‖LFunction χ s‖ ≤ ζ(2)`. The gamma factor `gammaFactor χ s = Gammaℝ (s + a)` where `a ∈ {0,1}`
  satisfies `‖Gammaℝ (σ + it)‖ ≤ C · (1 + |t|)^k · exp(−π|t|/2)` by
  `Gamma_vertical_bound` (n = σ, integer shifts via `Gamma_add_natCast`).
- **Left edge** `Re s ≤ −1`: the functional equation `IsPrimitive.completedLFunction_one_sub`
  reduces to the right-edge bound on `completedLFunction χ⁻¹ (1 - s)` with `Re(1-s) ≥ 2`.
- **Interior strip** `−1 ≤ Re s ≤ 2`: apply `PhragmenLindelof.vertical_strip` with the two
  edge bounds.

**Blocker B1**: requires `Gamma_vertical_strip_bound` — a generalization of
`Mathlib.Analysis.SpecialFunctions.Gamma.VerticalBounds.Gamma_vertical_bound` from integer
real parts to arbitrary real parts in a strip. This can be proved using
`Complex.HadamardThreeLines` applied to `Γ` on `[n, n+1]` for each integer `n`, but this
intermediate lemma has not yet been added to Mathlib. -/
theorem completedLFunction_vertical_bound (hχ : χ ≠ 1) (hprim : IsPrimitive χ)
    (σ_min σ_max : ℝ) (hσ : σ_min ≤ σ_max) :
    ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧ ∀ s : ℂ,
      σ_min ≤ s.re → s.re ≤ σ_max →
      ‖completedLFunction χ s‖ ≤ C * (1 + |s.im|) ^ k := by
  -- Available:
  --   differentiable_completedLFunction hχ : Differentiable ℂ (completedLFunction χ)
  --   IsPrimitive.completedLFunction_one_sub hprim : completedLFunction χ (1-s) = ...
  --   Gamma_vertical_bound : ‖Γ(↑n + ↑t * I)‖ ≤ n! * (2√π) * (1+|t|)^n * exp(-π|t|/2)
  --   PhragmenLindelof.vertical_strip : Phragmén-Lindelöf principle in vertical strips
  -- Missing: Gamma_vertical_strip_bound for non-integer Re s (Blocker B1 above).
  sorry

/-! ### Order estimate -/

/-- **Order ≤ 1 for `completedLFunction χ`** (nontrivial primitive character).

The completed L-function `completedLFunction χ` satisfies the exponential-type growth bound
  `‖completedLFunction χ s‖ ≤ C · exp(‖s‖^(1 + 1/k))`
for all `s` with `‖s‖ ≥ 1`, which in particular implies analytic order ≤ 1 in the classical sense.

This is a formal consequence of `completedLFunction_vertical_bound` (which gives polynomial × exp
growth in strips) combined with the `exp(-π|t|/2)` decay from the gamma factor.

**Blockers**: same as `completedLFunction_vertical_bound` (Blocker B1).
In addition, the notion of "analytic order" of an entire function is not yet in Mathlib
(`Complex.entireOrder` or equivalent; see Blocker B2 in the module docstring for the definition
needed to state this as a `Complex.entireOrder (completedLFunction χ) ≤ 1` theorem). -/
theorem completedLFunction_order_le_one (hχ : χ ≠ 1) (hprim : IsPrimitive χ) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ s : ℂ, ‖s‖ ≥ 1 →
      ‖completedLFunction χ s‖ ≤ C * Real.exp (‖s‖ ^ (1 + (1 : ℝ) / k)) := by
  -- Follows from completedLFunction_vertical_bound (when proved): the polynomial × exp bound
  -- in any vertical strip implies the exponential-type bound globally.
  -- The exp(-π|t|/2) factor from the Gamma vertical bound is absorbed into exp(‖s‖^(1+1/k))
  -- since exp(-π|t|/2) ≤ exp(‖s‖^(1+ε)) for all large s.
  -- Missing: completedLFunction_vertical_bound (Blocker B1) and
  --          Gamma_vertical_strip_bound (Blocker B1).
  sorry

/-! ### Hadamard factorization -/

/-- **Hadamard factorization for `completedLFunction χ`** (nontrivial primitive character).

For nontrivial primitive `χ`, the entire function `completedLFunction χ` of order ≤ 1 admits
the Hadamard product representation

    completedLFunction χ s = exp (a_χ + b_χ * s) * ∏' ρ, ((1 - s / ρ) * exp (s / ρ))

where the product runs over all zeros `ρ` of `completedLFunction χ` (with multiplicity), and
converges absolutely and uniformly on compact subsets of `ℂ`.

**Blocker B2 (deep, ~4–8 weeks)**: Mathlib does not contain the Hadamard factorization theorem
for entire functions of finite order. Required upstream Mathlib declarations (not yet present):

- `Complex.entireOrder` : `(ℂ → ℂ) → ℝ≥0∞` — order of an entire function, defined as
  `limsup_{r→∞} log log (sup_{|z|≤r} ‖f z‖) / log r`. (Mathlib has `meromorphicOrderAt` for the
  *local* order at a point, which is a *different* concept — `meromorphicOrderAt f z₀ ∈ WithTop ℤ`
  is the integer vanishing order; the classical "order of an entire function" is a global growth
  rate `ρ ∈ ℝ≥0`.)

- `Complex.WeierstrассProduct.convergent` — the Weierstrass canonical product `∏ₙ E_p(z/aₙ)`
  converges locally uniformly when the exponent of convergence `limsup_{r→∞} log n(r) / log r`
  of the zero sequence `{aₙ}` is finite. Lean infrastructure needed: primary factors `E_p`,
  `tprod` convergence under local uniform bounds.

- `Complex.Hadamard.factorizationOfOrder1` — for `f` entire with `Complex.entireOrder f ≤ 1`,
  there exist `a b : ℂ` such that `f z = exp (a + b * z) * ∏ₙ (1 - z/aₙ) * exp (z/aₙ)`,
  with the product ranging over zeros counted with multiplicity.

Conditional proof (once the above exist): apply `Complex.Hadamard.factorizationOfOrder1` to
`completedLFunction χ`, using `completedLFunction_order_le_one` (Blocker B1) to supply the
order-≤-1 hypothesis and `differentiable_completedLFunction hχ` for entireness. -/
theorem completedLFunction_hadamard_factorization (hχ : χ ≠ 1) (hprim : IsPrimitive χ) :
    ∃ (a b : ℂ) (zeros : ℕ → ℂ),
    (∀ n, completedLFunction χ (zeros n) = 0) ∧
    (∀ s : ℂ, completedLFunction χ s =
      Complex.exp (a + b * s) *
      ∏' n, ((1 - s / zeros n) * Complex.exp (s / zeros n))) := by
  -- Needs: Complex.Hadamard.factorizationOfOrder1 (Blocker B2; not in Mathlib as of 2026-05).
  -- Available: differentiable_completedLFunction hχ (entire function),
  --            completedLFunction_order_le_one (Blocker B1; also sorry).
  -- Note: `meromorphicOrderAt` in Mathlib.Analysis.Meromorphic.Order is the LOCAL vanishing
  -- order at a point (an integer), NOT the global growth rate. These are different objects.
  sorry

/-! ### Logarithmic derivative expansion -/

/-- **Logarithmic derivative of `completedLFunction χ` as a zero sum**.

A formal consequence of `completedLFunction_hadamard_factorization`: differentiating the
Hadamard product logarithmically gives

    (deriv (completedLFunction χ) s) / (completedLFunction χ s) = b_χ + ∑' ρ, (1/(s-ρ) + 1/ρ)

where the sum converges absolutely for `s` not a zero of `completedLFunction χ`.

This is the form used in the explicit formula contour integral:
the Weil explicit formula arises by integrating `M[f](s) · (log completedLFunction χ)'` along
a rectangular contour, with residues at zeros contributing `∑_ρ M[f](ρ)`.

**Blockers**:
- Primary: `completedLFunction_hadamard_factorization` (Blocker B2 above).
- Secondary (once B2 is resolved): differentiation of an infinite `tprod` requires locally
  uniform convergence of `∑' n, deriv (fun s ↦ (1 - s / zeros n) * exp (s / zeros n)) s`.
  The needed Mathlib lemma is `tprod_deriv_eq` or an analogue of `HasSum.deriv_of_summable`
  for products; this may require contributing `differentiable_tprod` to Mathlib. -/
theorem completedLFunction_logDeriv_eq_sum_zeros (hχ : χ ≠ 1) (hprim : IsPrimitive χ) :
    ∃ b : ℂ, ∃ (zeros : ℕ → ℂ),
    (∀ n, completedLFunction χ (zeros n) = 0) ∧
    ∀ s : ℂ, completedLFunction χ s ≠ 0 →
      deriv (completedLFunction χ) s / completedLFunction χ s =
        b + ∑' n, (1 / (s - zeros n) + 1 / zeros n) := by
  -- Needs: completedLFunction_hadamard_factorization (Blocker B2) +
  --        locally uniform convergence of the product derivative (secondary blocker above).
  sorry

end DirichletCharacter
