/-
Copyright (c) 2026 The Mathlib Community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Asymptotic decay rate of Tr(exp(-t·A)) equals the minimum positive eigenvalue

For a positive semidefinite Hermitian matrix `A` over ℝ, the heat trace
`Tr exp(-t·A) = Σᵢ exp(-t·λᵢ)` decays exponentially at rate equal to
`λ_min_pos(A)` as `t → ∞`.

## Main results

* `Matrix.IsHermitian.trace_exp_neg_smul_eq_sum_exp`: `Tr(exp(-t·A)) = Σᵢ exp(-t·λᵢ)`
* `Matrix.IsHermitian.log_traceExp_div_tendsto`: decay rate → min positive eigenvalue

## Key missing Mathlib piece

`trace_exp_neg_smul_eq_sum_exp` is sorry'd. It needs composing:
1. `spectral_theorem`: `A = U·diag(λᵢ)·Uᵀ`                      (exists)
2. `Matrix.exp_conj`: `exp(U·D·U⁻¹) = U·exp(D)·U⁻¹`             (exists)
3. `Matrix.trace_mul_cycle`: `Tr(ABC) = Tr(CAB)`                  (exists)
4. `Matrix.exp_diagonal`: `exp(diag v) = diag(exp ∘ v)`           (exists)
5. `Matrix.trace_diagonal`: `Tr(diag v) = Σᵢ vᵢ`                 (exists)

No single Mathlib lemma composes all five steps end-to-end.

## References

* scripts/19gb_15_saddle_to_lambda_asymptotic.py (commit b331bf0, iter 46)
-/

open NormedSpace Real Filter

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ} {hA : A.IsHermitian}

/-- Minimum positive eigenvalue of a PSD Hermitian matrix, given one exists. -/
noncomputable def minPosEigenvalue
    (hPSD : A.PosSemidef)
    (hPos : ∃ i : n, 0 < hA.eigenvalues i) : ℝ :=
  let i₀ := hPos.choose
  Finset.univ.inf' ⟨i₀, Finset.mem_univ _⟩
    (fun i ↦ if 0 < hA.eigenvalues i then hA.eigenvalues i else hA.eigenvalues i₀)

/-- The heat trace equals the sum of exp(-t·λᵢ) over eigenvalues.

Proof outline (sorry pending Mathlib `trace_exp_conj`):
  A = U · diag(λᵢ) · Uᵀ              [spectral_theorem]
  exp(-t·A) = U · diag(exp(-t·λᵢ)) · Uᵀ    [exp_conj + exp_diagonal]
  Tr(·) = Σᵢ exp(-t·λᵢ)              [trace_mul_cycle + trace_diagonal]
-/
theorem trace_exp_neg_smul_eq_sum_exp (t : ℝ) :
    (NormedSpace.exp (-t • A)).trace = ∑ i : n, Real.exp (-t * hA.eigenvalues i) := by
  sorry
  /-
  rw [hA.spectral_theorem, show (-t • conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))) =
      conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (-t • Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) from by simp [map_smul]]
  rw [Matrix.exp_units_conj]
  -- Tr(U · M · U⁻¹) = Tr(M):
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_inv_of_invertible]
  rw [Matrix.one_mul]
  rw [Matrix.smul_diagonal, Matrix.exp_diagonal, Matrix.trace_diagonal]
  simp [Function.comp, Real.exp_mul]
  -/

/-- For PSD A, Tr exp(-t·A) ≤ card n when t ≥ 0. -/
theorem traceExp_le_card (hA' : A.IsHermitian) (hPSD : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    (NormedSpace.exp (-t • A)).trace ≤ Fintype.card n := by
  rw [hA'.trace_exp_neg_smul_eq_sum_exp t]
  have : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp
  rw [this]
  apply Finset.sum_le_sum
  intro i _
  rw [Real.exp_le_one_iff]
  linarith [mul_nonneg ht (hPSD.eigenvalues_nonneg i)]

/-- The normalized log decay rate converges to the min positive eigenvalue as t → ∞.

  Tr exp(-t·A) = exp(-t·λ_min) · S(t),  where S(t) → #{i : λᵢ = λ_min} ≥ 1.
  So (-log Tr) / t → λ_min.
-/
theorem log_traceExp_div_tendsto
    (hPSD : A.PosSemidef)
    (hPos : ∃ i : n, 0 < hA.eigenvalues i) :
    Filter.Tendsto (fun t : ℝ ↦ -(Real.log (NormedSpace.exp (-t • A)).trace) / t)
      Filter.atTop
      (nhds (hA.minPosEigenvalue hPSD hPos)) := by
  sorry
  -- Proof: use trace_exp_neg_smul_eq_sum_exp, factor exp(-t·λ_min), squeeze log(S(t))/t → 0.

end Matrix.IsHermitian
