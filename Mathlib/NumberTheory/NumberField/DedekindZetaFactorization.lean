/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.DedekindCharacters
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind zeta factorization for `ℚ(ζ₁₂)`

This file currently contains the imports needed for the expected factorization of the Dedekind zeta
function of `CyclotomicField 12 ℚ`. The actual factorization theorem is not yet added, because the
present library does not provide the cyclotomic prime-splitting / Euler-product interface needed to
prove it upstream-cleanly from existing infrastructure.
-/

@[expose] public section
