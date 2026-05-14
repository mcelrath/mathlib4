/-
Copyright (c) 2026 The Mathlib Community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
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

open NormedSpace Real Filter Matrix Unitary

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
  -- Step 1: A = U · diag(λᵢ) · U⋆ via spectral theorem
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply]
  -- Step 2: lift eigenvectorUnitary to a units element
  set U := Unitary.toUnits hA.eigenvectorUnitary with hU_def
  have hUcoe : (U : Matrix n n ℝ) = (hA.eigenvectorUnitary : Matrix n n ℝ) :=
    rfl
  have hUinv : (↑U⁻¹ : Matrix n n ℝ) = (star hA.eigenvectorUnitary : Matrix n n ℝ) := by
    simp [hU_def, Unitary.toUnits, ← Unitary.star_eq_inv]
  -- Step 3: rewrite the conjugation as U · (−t • diag) · U⁻¹
  rw [← hUinv, ← hUcoe]
  rw [← smul_mul_assoc, ← mul_smul_comm]
  -- Step 4: exp(U · D · U⁻¹) = U · exp(D) · U⁻¹
  rw [Matrix.exp_units_conj U]
  -- Step 5: Tr(U⁻¹ · (U · M)) = Tr(M) via inv_mul cancellation
  rw [Matrix.trace_mul_cycle]
  simp only [Units.inv_mul, one_mul]
  -- Step 6: expand exp of scaled diagonal
  rw [show -t • Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
      Matrix.diagonal (fun i => -t * hA.eigenvalues i) from by
    ext i j; simp [Matrix.diagonal, smul_apply, mul_ite]]
  rw [Matrix.exp_diagonal, Matrix.trace_diagonal]
  -- Step 7: NormedSpace.exp on ℝ equals Real.exp
  congr 1; ext i; simp [← Real.exp_eq_exp_ℝ]

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

  Proof: All eigenvalues Eᵢ > 0 (PosDef). Let E = min eigenvalue (attained in finite set).
  For t ≥ 0: exp(-tEᵢ) ≤ exp(-tE), so Σ exp(-tEᵢ) ≤ |n| exp(-tE).
  Also Σ exp(-tEᵢ) ≥ exp(-tE) (the min-achieving term).
  Hence E - log|n|/t ≤ -log(Σ)/t ≤ E. Both bounds → E, so squeeze applies.
-/
theorem log_traceExp_div_tendsto
    (hPD : A.PosDef)
    (hPos : ∃ i : n, 0 < hA.eigenvalues i) :
    Filter.Tendsto (fun t : ℝ ↦ -(Real.log (NormedSpace.exp (-t • A)).trace) / t)
      Filter.atTop
      (nhds (hA.minPosEigenvalue hPD.posSemidef hPos)) := by
  -- All eigenvalues are positive
  have hEi_pos : ∀ i, 0 < hA.eigenvalues i := fun i => hPD.eigenvalues_pos i
  -- Nonempty n from hPos
  have hNon : Nonempty n := ⟨hPos.choose⟩
  haveI : Nonempty n := hNon
  set E := hA.minPosEigenvalue hPD.posSemidef hPos with hE_def
  -- The inf' function; PosDef means the conditional always picks eigenvalues i
  have hf_eq : ∀ i : n, (fun j : n => if 0 < hA.eigenvalues j then hA.eigenvalues j
      else hA.eigenvalues hPos.choose) i = hA.eigenvalues i :=
    fun i => by simp [hEi_pos i]
  -- E is attained: exists i_min with eigenvalues i_min = E
  -- Use exists_min_image to find the minimum-achieving index
  obtain ⟨i_min, _, himin_le⟩ := Finset.exists_min_image Finset.univ hA.eigenvalues
    Finset.univ_nonempty
  have hi_min : hA.eigenvalues i_min = E := by
    apply le_antisymm
    · -- eigenvalues i_min ≤ E = inf' (cond f):
      -- i_min achieves the minimum of eigenvalues, so eigenvalues i_min ≤ eigenvalues j ∀j.
      -- E = inf' (cond f) where cond f = eigenvalues (PosDef). So eigenvalues i_min is a lb.
      -- Finset.le_inf' gives: eigenvalues i_min ≤ inf' f if ∀ j, eigenvalues i_min ≤ f j.
      simp only [E, minPosEigenvalue]
      apply Finset.le_inf'
      intro j _
      simp only [hEi_pos j, ↓reduceIte]
      exact himin_le j (Finset.mem_univ j)
    · -- E = inf' f ≤ f i_min = eigenvalues i_min
      simp only [E, minPosEigenvalue]
      rw [← hf_eq i_min]
      exact Finset.inf'_le _ (Finset.mem_univ i_min)
  -- E is positive (equals positive eigenvalue)
  have hE_pos : 0 < E := hi_min ▸ hEi_pos i_min
  -- E is a lower bound for all eigenvalues
  have hE_min : ∀ i, E ≤ hA.eigenvalues i := by
    intro i
    simp only [E, minPosEigenvalue]
    calc Finset.univ.inf' ⟨hPos.choose, Finset.mem_univ _⟩
          (fun j => if 0 < hA.eigenvalues j then hA.eigenvalues j else hA.eigenvalues hPos.choose)
        ≤ (fun j => if 0 < hA.eigenvalues j then hA.eigenvalues j else hA.eigenvalues hPos.choose) i :=
          Finset.inf'_le _ (Finset.mem_univ i)
      _ = hA.eigenvalues i := hf_eq i
  -- Rewrite goal using trace = sum of exp(-t λᵢ)
  simp_rw [hA.trace_exp_neg_smul_eq_sum_exp]
  -- Sum is always positive
  have hsum_pos : ∀ t : ℝ, 0 < ∑ i : n, Real.exp (-t * hA.eigenvalues i) :=
    fun t => Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  -- Upper bound: Σ exp(-t Eᵢ) ≤ card n * exp(-t E) for t ≥ 0
  have hub : ∀ t : ℝ, 0 ≤ t →
      ∑ i : n, Real.exp (-t * hA.eigenvalues i) ≤ Fintype.card n * Real.exp (-t * E) :=
    fun t ht => calc ∑ i : n, Real.exp (-t * hA.eigenvalues i)
        ≤ ∑ _i : n, Real.exp (-t * E) := Finset.sum_le_sum fun i _ =>
            Real.exp_le_exp_of_le (by nlinarith [hE_min i])
      _ = Fintype.card n * Real.exp (-t * E) := by simp [Finset.card_univ]
  -- Lower bound: Σ exp(-t Eᵢ) ≥ exp(-t E) (the i_min term)
  have hlb : ∀ t : ℝ, Real.exp (-t * E) ≤ ∑ i : n, Real.exp (-t * hA.eigenvalues i) :=
    fun t => hi_min ▸ Finset.single_le_sum
        (fun i _ => (Real.exp_pos (-t * hA.eigenvalues i)).le) (Finset.mem_univ i_min)
  -- Card is positive as real
  have hcard_pos : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  -- Squeeze: E - log(card)/t ≤ -log(Σ)/t ≤ E (both bounds hold eventually, both → E)
  -- Lower bound: E - log(card)/t
  have hg_tendsto : Filter.Tendsto (fun t : ℝ => E - Real.log (Fintype.card n) / t)
      Filter.atTop (nhds E) := by
    have h0 : Filter.Tendsto (fun t : ℝ => Real.log (Fintype.card n) / t) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Filter.Tendsto (fun t : ℝ => E - Real.log (Fintype.card n) / t)
        Filter.atTop (nhds (E - 0)) :=
      (tendsto_const_nhds (x := E)).sub h0
    simpa using h1
  -- Upper bound: constant E
  have hh_tendsto : Filter.Tendsto (fun _ : ℝ => E) Filter.atTop (nhds E) :=
    tendsto_const_nhds
  -- Eventually: lower ≤ target ≤ upper
  have hgf : ∀ᶠ t : ℝ in Filter.atTop,
      E - Real.log (Fintype.card n) / t ≤
      -(Real.log (∑ i : n, Real.exp (-t * hA.eigenvalues i))) / t := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    have ht' : (0 : ℝ) < t := Set.mem_Ioi.mp ht
    have hS_pos := hsum_pos t
    have hub_t := hub t (le_of_lt ht')
    have hlog_le : Real.log (∑ i : n, Real.exp (-t * hA.eigenvalues i)) ≤
        Real.log (Fintype.card n) + (-t * E) := by
      have h1 := Real.log_le_log hS_pos hub_t
      have h2 := Real.log_mul hcard_pos.ne' (Real.exp_pos (-t * E)).ne'
      have h3 := Real.log_exp (-t * E)
      linarith
    -- E - log(card)/t ≤ -(log Σ)/t
    -- Equivalent (multiply both sides by t): E*t - log(card) ≤ -log Σ
    have key : E * t - Real.log (Fintype.card n) ≤
        -Real.log (∑ i : n, Real.exp (-t * hA.eigenvalues i)) := by linarith
    -- E - log(card)/t ≤ -(log Σ)/t follows from key and t > 0
    have eq1 : (E * t - Real.log (Fintype.card n)) / t = E - Real.log (Fintype.card n) / t := by
      field_simp
    have ineq : (E * t - Real.log (Fintype.card n)) / t ≤
        (-Real.log (∑ i : n, Real.exp (-t * hA.eigenvalues i))) / t := by
      apply div_le_div_of_nonneg_right key (le_of_lt ht')
    linarith
  have hfh : ∀ᶠ t : ℝ in Filter.atTop,
      -(Real.log (∑ i : n, Real.exp (-t * hA.eigenvalues i))) / t ≤ E := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    have ht' : (0 : ℝ) < t := Set.mem_Ioi.mp ht
    have hlb_t := hlb t
    have hlog_ge : (-t * E) ≤ Real.log (∑ i : n, Real.exp (-t * hA.eigenvalues i)) := by
      have h1 := Real.log_le_log (Real.exp_pos (-t * E)) hlb_t
      rw [Real.log_exp] at h1; linarith
    -- -(log Σ)/t ≤ E  iff  -log Σ ≤ E*t  (multiply by t > 0)
    rw [div_le_iff₀ ht']
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hg_tendsto hh_tendsto hgf hfh

end Matrix.IsHermitian
