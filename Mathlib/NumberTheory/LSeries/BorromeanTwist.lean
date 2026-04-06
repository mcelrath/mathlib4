/-
 Copyright (c) 2026 Bob McElrath. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Bob McElrath
 -/
 module
 
 public import Mathlib.NumberTheory.LSeries.DirichletContinuation
 public import Mathlib.NumberTheory.LSeries.DirichletEta
 
 /-!
 # Borromean-twisted Dirichlet L-functions
 -/
 
 @[expose] public section
 
 noncomputable section
 
 open Complex
 
 namespace DirichletCharacter
 
 variable {N : ℕ} [NeZero N]
 
 /-- The Borromean twist factor at the prime `2`. -/
 noncomputable def borromeanTwist (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
   1 - χ 2 * (2 : ℂ) ^ (1 - s)
 
 /-- The Borromean-twisted Dirichlet `L`-function. -/
 noncomputable def LFunction_twisted (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
   borromeanTwist χ s * DirichletCharacter.LFunction χ s
 
 theorem borromeanTwist_trivial (χ : DirichletCharacter ℂ N) (s : ℂ) (hχ : χ 2 = 0) :
     borromeanTwist χ s = 1 := by
   simp [borromeanTwist, hχ]
 
 theorem LFunction_twisted_eq_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hχ : χ 2 = 0) :
     LFunction_twisted χ s = LFunction χ s := by
   simp [LFunction_twisted, borromeanTwist_trivial, hχ]
 
theorem LFunction_twisted_one_eq_dirichletEta {s : ℂ} (hs : s ≠ 1) :
    LFunction_twisted (1 : DirichletCharacter ℂ 1) s = DirichletEta.dirichletEta s := by
  have h2 : (1 : DirichletCharacter ℂ 1) 2 = 1 := by
    change (1 : DirichletCharacter ℂ 1) (1 : ZMod 1) = 1
    simp
  rw [LFunction_twisted, DirichletEta.dirichletEta_ne_one s hs, LFunction_modOne_eq]
  rw [borromeanTwist, h2]
  ring
 
 end DirichletCharacter
