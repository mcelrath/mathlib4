/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Algebra.Polynomial.Basic

/-! # `norm_num` extension for `IsCoprime` on `Polynomial ℚ`

This module defines a `norm_num` extension for `IsCoprime` over `ℚ[X]`.

The extension parses polynomial expressions into coefficient arrays, runs the
extended Euclidean algorithm to find Bezout witnesses, then certifies the
result using `ring`.

Since `ring` treats `Polynomial.C r` as an opaque atom, we cannot directly build witness
expressions using `C`. Instead, we clear denominators: if the XGCD yields rational-coefficient
witnesses `a, b` with `a * p + b * q = 1`, we find a common denominator `d`, build
integer-coefficient expressions `a' = d*a`, `b' = d*b` (using numeric literals that `ring`
understands), prove `a' * p + b' * q = C d` via `ring`, and conclude `IsCoprime` via a helper
lemma.
-/

public section

namespace Tactic.NormNum.PolyIsCoprime

open Polynomial

theorem isCoprime_of_bezout_scaled (d : ℕ) (hd : d ≠ 0) (a' b' p q : ℚ[X])
    (h : a' * p + b' * q = (d : ℚ[X])) :
    IsCoprime p q := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  exact ⟨Polynomial.C (d : ℚ)⁻¹ * a', Polynomial.C (d : ℚ)⁻¹ * b', by
    rw [mul_assoc, mul_assoc, ← mul_add, h, ← Polynomial.C_eq_natCast,
      ← map_mul, inv_mul_cancel₀ hd', map_one]⟩

end Tactic.NormNum.PolyIsCoprime

end -- public section

public meta section

namespace Tactic

namespace NormNum

open Qq Lean Meta Elab.Tactic Mathlib.Meta.NormNum Polynomial

/-! ## Phase 1: Polynomial arithmetic on coefficient arrays -/

def polyAdd (p r : Array ℚ) : Array ℚ := Id.run do
  let n := max p.size r.size
  let mut res := Array.replicate n 0
  for i in [:p.size] do
    res := res.set! i (res[i]! + p[i]!)
  for i in [:r.size] do
    res := res.set! i (res[i]! + r[i]!)
  return res

def polyNeg (p : Array ℚ) : Array ℚ :=
  p.map (· * (-1))

def polyMul (p r : Array ℚ) : Array ℚ := Id.run do
  if p.isEmpty || r.isEmpty then return #[]
  let n := p.size + r.size - 1
  let mut res := Array.replicate n 0
  for i in [:p.size] do
    for j in [:r.size] do
      res := res.set! (i + j) (res[i + j]! + p[i]! * r[j]!)
  return res

def polyStrip (p : Array ℚ) : Array ℚ := Id.run do
  let mut n := p.size
  while n > 0 && p[n - 1]! == 0 do
    n := n - 1
  return p.shrink n

def polyScale (c : ℚ) (p : Array ℚ) : Array ℚ :=
  p.map (· * c)

def polyDivMod (f g : Array ℚ) : Array ℚ × Array ℚ := Id.run do
  let f := polyStrip f
  let g := polyStrip g
  if g.isEmpty then return (#[], f)
  if f.size < g.size then return (#[], f)
  let lc := g.back!
  let mut rem := f
  let mut quot := Array.replicate (f.size - g.size + 1) (0 : ℚ)
  for i in [:quot.size] do
    let idx := f.size - 1 - i
    if idx + 1 < g.size then break
    let c := rem[idx]! / lc
    quot := quot.set! (idx + 1 - g.size) c
    for j in [:g.size] do
      let k := idx + 1 - g.size + j
      rem := rem.set! k (rem[k]! - c * g[j]!)
  return (polyStrip quot, polyStrip rem)

/-! ## Phase 2: Extended Euclidean algorithm -/

def polyXGCD (f g : Array ℚ) : Array ℚ × Array ℚ × Array ℚ := Id.run do
  let mut r0 := polyStrip f
  let mut r1 := polyStrip g
  let mut s0 : Array ℚ := #[1]
  let mut s1 : Array ℚ := #[]
  let mut t0 : Array ℚ := #[]
  let mut t1 : Array ℚ := #[1]
  while !r1.isEmpty do
    let (quot, rem) := polyDivMod r0 r1
    r0 := r1
    r1 := rem
    let s_new := polyAdd (polyStrip s0) (polyNeg (polyMul quot s1))
    s0 := s1
    s1 := s_new
    let t_new := polyAdd (polyStrip t0) (polyNeg (polyMul quot t1))
    t0 := t1
    t1 := t_new
  let gcd := polyStrip r0
  if gcd.size == 1 && gcd[0]! != 0 then
    let c := 1 / gcd[0]!
    return (#[1], polyScale c (polyStrip s0), polyScale c (polyStrip t0))
  return (gcd, polyStrip s0, polyStrip t0)

/-! ## Phase 1 (cont.): Expression parsing -/

def exprToRat (e : Expr) : MetaM ℚ := do
  let e' ← whnfR e
  if let some n := e'.rawNatLit? then
    return ↑n
  have e : Q(ℚ) := e
  let res ← deriveRat e (α := q(ℚ)) (_inst := q(inferInstance))
  return res.1

partial def parsePolyExpr (e : Expr) : MetaM (Array ℚ) := do
  let e ← whnfR e
  if e.isAppOfArity ``Polynomial.C 3 then
    let c ← exprToRat (e.getArg! 2)
    return #[c]
  if e.isAppOfArity ``Polynomial.X 2 then
    return #[0, 1]
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let a ← parsePolyExpr (e.getArg! 4)
    let b ← parsePolyExpr (e.getArg! 5)
    return polyAdd a b
  if e.isAppOfArity ``HMul.hMul 6 then
    let a ← parsePolyExpr (e.getArg! 4)
    let b ← parsePolyExpr (e.getArg! 5)
    return polyMul a b
  if e.isAppOfArity ``HSub.hSub 6 then
    let a ← parsePolyExpr (e.getArg! 4)
    let b ← parsePolyExpr (e.getArg! 5)
    return polyAdd a (polyNeg b)
  if e.isAppOfArity ``Neg.neg 3 then
    let a ← parsePolyExpr (e.getArg! 2)
    return polyNeg a
  if e.isAppOfArity ``HPow.hPow 6 then
    let a ← parsePolyExpr (e.getArg! 4)
    let nExpr := e.getArg! 5
    let nExpr' ← whnfR nExpr
    let n ← match nExpr'.rawNatLit? with
      | some n => pure n
      | none =>
        if nExpr'.isAppOfArity ``OfNat.ofNat 3 then
          let inner ← whnfR (nExpr'.getArg! 1)
          match inner.rawNatLit? with
          | some n => pure n
          | none => throwError "PolynomialIsCoprime: non-literal exponent {nExpr}"
        else throwError "PolynomialIsCoprime: non-literal exponent {nExpr}"
    let mut result : Array ℚ := #[1]
    for _ in [:n] do
      result := polyMul result a
    return result
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let nExpr := e.getArg! 1
    let nExpr' ← whnfR nExpr
    if let some n := nExpr'.rawNatLit? then
      return #[↑n]
  if e.isAppOfArity ``Nat.cast 3 then
    let c ← exprToRat (e.getArg! 2)
    return #[c]
  if e.isAppOfArity ``Int.cast 3 then
    let c ← exprToRat (e.getArg! 2)
    return #[c]
  if e.isAppOfArity ``HSMul.hSMul 6 then
    let c ← exprToRat (e.getArg! 4)
    let p ← parsePolyExpr (e.getArg! 5)
    return polyScale c p
  try
    let c ← exprToRat e
    return #[c]
  catch _ =>
    throwError "PolynomialIsCoprime: cannot parse polynomial expression {e}"

/-! ## Phase 3: Proof construction -/

/-- Compute LCM of all denominators in the coefficient array. -/
def coeffsDenomLCM (coeffs : Array ℚ) : Nat := Id.run do
  let mut lcm : Nat := 1
  for c in coeffs do
    lcm := Nat.lcm lcm c.den
  return lcm

/-- Build a polynomial expression using integer numeric literals (not `C`).
These are understood by `ring` as coefficients. -/
def intCoeffsToPolyExpr (coeffs : Array ℤ) : MetaM Expr := do
  let xExpr : Expr := q((Polynomial.X : Polynomial ℚ))
  let mut result : Option Expr := none
  for i in [:coeffs.size] do
    let c := coeffs[i]!
    if c == 0 then continue
    -- Build integer coefficient as ℚ[X] numeric literal
    let cPoly : Expr ←
      if c ≥ 0 then
        let nLit : Q(ℕ) := mkRawNatLit c.toNat
        pure q(($nLit : Polynomial ℚ))
      else
        let nLit : Q(ℕ) := mkRawNatLit (-c).toNat
        pure q(-($nLit : Polynomial ℚ))
    let term : Expr ←
      if i == 0 then
        pure cPoly
      else if i == 1 then
        if c == 1 then
          pure xExpr
        else if c == -1 then
          mkAppM ``Neg.neg #[xExpr]
        else
          mkAppM ``HMul.hMul #[cPoly, xExpr]
      else do
        let iLit : Q(ℕ) := mkRawNatLit i
        let xPow ← mkAppM ``HPow.hPow #[xExpr, iLit]
        if c == 1 then
          pure xPow
        else if c == -1 then
          mkAppM ``Neg.neg #[xPow]
        else
          mkAppM ``HMul.hMul #[cPoly, xPow]
    match result with
    | none => result := some term
    | some r => result := some (← mkAppM ``HAdd.hAdd #[r, term])
  match result with
  | none => return q((0 : Polynomial ℚ))
  | some r => return r

/-- A `norm_num` extension that decides `IsCoprime p q` for `p q : ℚ[X]` by computing an
extended GCD and synthesizing a Bézout certificate. -/
@[norm_num IsCoprime (_ : Polynomial ℚ) (_ : Polynomial ℚ)]
def evalPolyIsCoprime : NormNumExt where eval {_ _} e := do
  let .app (.app _ (p : Q(Polynomial ℚ))) (qp : Q(Polynomial ℚ)) ← whnfR e | failure
  let pCoeffs ← parsePolyExpr p
  let qCoeffs ← parsePolyExpr qp
  let (gcd, aCoeffs, bCoeffs) := polyXGCD pCoeffs qCoeffs
  match polyStrip gcd with
  | #[c] => if c == 0 then failure
  | _ => failure
  -- Find common denominator for all witness coefficients
  let denomA := coeffsDenomLCM aCoeffs
  let denomB := coeffsDenomLCM bCoeffs
  let denom : Nat := Nat.lcm denomA denomB
  let aScaled : Array ℤ := aCoeffs.map fun c => (c * ↑denom).num
  let bScaled : Array ℤ := bCoeffs.map fun c => (c * ↑denom).num
  -- Build integer-coefficient witness expressions
  let aExpr ← intCoeffsToPolyExpr aScaled
  let bExpr ← intCoeffsToPolyExpr bScaled
  have aExpr : Q(Polynomial ℚ) := aExpr
  have bExpr : Q(Polynomial ℚ) := bExpr
  -- Build d as a natural number literal
  have dLit : Q(ℕ) := mkRawNatLit denom
  -- Build proof that d ≠ 0
  let hdGoal : Q(Prop) := q($dLit ≠ (0 : ℕ))
  let hdExpr ← mkFreshExprMVar (some hdGoal)
  let hdTac ← `(tactic| decide)
  let _ ← Lean.Elab.runTactic hdExpr.mvarId! hdTac.raw
  have hdExpr : Q($dLit ≠ (0 : ℕ)) := hdExpr
  -- Build and prove the scaled equation: aExpr * p + bExpr * qp = (d : ℚ[X])
  let dPoly : Q(Polynomial ℚ) := q(($dLit : Polynomial ℚ))
  let lhs ← mkAppM ``HAdd.hAdd #[← mkAppM ``HMul.hMul #[aExpr, p],
                                    ← mkAppM ``HMul.hMul #[bExpr, qp]]
  let goalType ← mkAppM ``Eq #[lhs, dPoly]
  let eqProof ← mkFreshExprMVar (some goalType)
  let eqTac ← `(tactic| ring)
  let _ ← Lean.Elab.runTactic eqProof.mvarId! eqTac.raw
  have eqProof : Q($aExpr * $p + $bExpr * $qp = ($dLit : Polynomial ℚ)) := eqProof
  -- Apply helper lemma
  let proof : Q(IsCoprime $p $qp) :=
    q(PolyIsCoprime.isCoprime_of_bezout_scaled $dLit $hdExpr $aExpr $bExpr $p $qp $eqProof)
  return .isTrue proof

end NormNum

end Tactic

section PolynomialIsCoprime_tests

open Polynomial in
example : IsCoprime (X : ℚ[X]) (X + 1) := by norm_num

open Polynomial in
example : IsCoprime (X ^ 2 : ℚ[X]) (X + 1) := by norm_num

open Polynomial in
example : IsCoprime (X ^ 2 + 1 : ℚ[X]) (X - 1) := by norm_num

end PolynomialIsCoprime_tests
