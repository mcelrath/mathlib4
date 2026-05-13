/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.Complex.RectangleResidue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Finset.Basic

/-! # Multi-pole rectangle residue theorem

Mathlib provides `Complex.rectangle_residue` for a single simple pole. This file
generalises that to a `Finset` of simple poles inside the rectangle: the boundary
integral picks up `2 * π * I` times the sum of residues.

## Main results

* `rectangleBoundaryIntegral` — packaging of the four-term rectangle boundary
  integral used by `Complex.rectangle_residue`.
* `rectangleBoundaryIntegral_eq_zero_of_holomorphic` — base case (no poles): the
  boundary integral of a function continuous on the closed rectangle and
  holomorphic on the interior vanishes. (Repackaging of
  `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`.)
* `rectangle_residue_finset` — the multi-pole rectangle residue theorem. Given a
  finite set of simple poles strictly inside the rectangle with associated
  numerators continuous on the closed rectangle and holomorphic on the interior,
  the rectangle boundary integral equals `2 * π * I * Σᵢ g i i`.

The inductive step peels one pole off via `Complex.rectangle_residue` and applies
the induction hypothesis to the function with that pole removed. The split is
performed on the boundary, where no pole lies (poles are strictly interior).
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Interval

namespace Complex

/-- The standard Mathlib rectangle boundary integral (sum of four sides). Repackages
the four-term expression in `Complex.rectangle_residue` for legibility. -/
noncomputable def rectangleBoundaryIntegral (f : ℂ → ℂ) (c₂ c₁ T : ℝ) : ℂ :=
  (∫ x in c₂..c₁, f (↑x + ↑(-T) * I))
    - (∫ x in c₂..c₁, f (↑x + ↑T * I))
    + I • (∫ y in (-T)..T, f (↑c₁ + ↑y * I))
    - I • (∫ y in (-T)..T, f (↑c₂ + ↑y * I))

/-- **Base case** (0 poles): if `f` is continuous on the closed rectangle and
holomorphic on its interior, the rectangle boundary integral is `0`.

This is `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` with the
empty exceptional set, repackaged in the `rectangleBoundaryIntegral` form. -/
theorem rectangleBoundaryIntegral_eq_zero_of_holomorphic
    {f : ℂ → ℂ} {c₂ c₁ T : ℝ}
    (hf_cont : ContinuousOn f ([[c₂, c₁]] ×ℂ [[-T, T]]))
    (hf_diff : ∀ x ∈ (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)),
        DifferentiableAt ℂ f x) :
    rectangleBoundaryIntegral f c₂ c₁ T = 0 := by
  unfold rectangleBoundaryIntegral
  have h := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f ⟨c₂, -T⟩ ⟨c₁, T⟩ (∅ : Set ℂ) countable_empty hf_cont
    (by intro x ⟨hx, _⟩; exact hf_diff x hx)
  -- `h` has the same 4-term shape (up to the empty exclusion which is `\ ∅ = id`).
  simpa using h

/-- **Multi-pole rectangle residue theorem.**

Suppose `f` decomposes on the closed rectangle (off the poles) as
`f s = (Σ_{i ∈ poles} (s - i)⁻¹ * g i s) + h s`, where each `g i` and `h` are
continuous on the closed rectangle and holomorphic on the interior, and every pole in
`poles` lies in the open rectangle. Then

`∮_{∂R} f = 2 * π * I * Σ_{i ∈ poles} g i i`.

This is the standard residue theorem for finitely many simple poles on a rectangle,
proved by induction on `poles`, peeling one pole at a time via
`Complex.rectangle_residue` and reducing to the holomorphic base case
`rectangleBoundaryIntegral_eq_zero_of_holomorphic` on the empty set. -/
theorem rectangle_residue_finset
    {c₂ c₁ T : ℝ}
    (hc : c₂ < c₁) (hT : -T < T)
    (poles : Finset ℂ)
    (g : ℂ → ℂ → ℂ) (h : ℂ → ℂ) (f : ℂ → ℂ)
    (hpoles_mem : ∀ z ∈ poles, c₂ < z.re ∧ z.re < c₁ ∧ -T < z.im ∧ z.im < T)
    (hg_cont : ∀ i ∈ poles, ContinuousOn (g i) ([[c₂, c₁]] ×ℂ [[-T, T]]))
    (hg_diff : ∀ i ∈ poles, DifferentiableOn ℂ (g i)
      (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)))
    (hh_cont : ContinuousOn h ([[c₂, c₁]] ×ℂ [[-T, T]]))
    (hh_diff : ∀ x ∈ (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)),
        DifferentiableAt ℂ h x)
    (hfeq : ∀ s, s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) → (∀ i ∈ poles, s ≠ i) →
      f s = (∑ i ∈ poles, (s - i)⁻¹ * g i s) + h s) :
    rectangleBoundaryIntegral f c₂ c₁ T =
      2 * (Real.pi : ℂ) * I * ∑ i ∈ poles, g i i := by
  -- Induction on `poles`. Define the auxiliary "expanded" function
  -- F s = (∑ i ∈ poles, (s - i)⁻¹ * g i s) + h s
  -- which agrees with f off the poles. On the rectangle BOUNDARY there are no poles
  -- (poles have strict-interior coordinates), so F = f on the boundary and hence
  -- rectangleBoundaryIntegral F = rectangleBoundaryIntegral f.
  -- Then peel one pole at a time from F, using `Complex.rectangle_residue`.
  --
  -- The rectangle is non-degenerate: hc gives c₂ < c₁, hT gives -T < T.
  have hmin_c : min c₂ c₁ = c₂ := min_eq_left hc.le
  have hmax_c : max c₂ c₁ = c₁ := max_eq_right hc.le
  have hmin_T : min (-T) T = -T := min_eq_left hT.le
  have hmax_T : max (-T) T = T := max_eq_right hT.le
  -- Generalize over `f` and `h` to make IH usable. Order: revert last → intro first.
  induction poles using Finset.induction_on
    generalizing f h hh_cont hh_diff with
  | empty =>
    -- f s = 0 + h s = h s on the rectangle; apply the holomorphic base case.
    simp only [Finset.sum_empty, zero_add] at hfeq
    have hfeq' : ∀ s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]), f s = h s := by
      intro s hs; exact hfeq s hs (by intro i hi; exact absurd hi (Finset.notMem_empty i))
    -- rectangleBoundaryIntegral f = rectangleBoundaryIntegral h via boundary equality.
    have heq : rectangleBoundaryIntegral f c₂ c₁ T
        = rectangleBoundaryIntegral h c₂ c₁ T := by
      unfold rectangleBoundaryIntegral
      have hbot : ∀ x ∈ [[c₂, c₁]], f (↑x + ↑(-T) * I) = h (↑x + ↑(-T) * I) := by
        intro x hx; apply hfeq'
        refine ⟨?_, ?_⟩ <;> simp [hx]
      have htop : ∀ x ∈ [[c₂, c₁]], f (↑x + ↑T * I) = h (↑x + ↑T * I) := by
        intro x hx; apply hfeq'
        refine ⟨?_, ?_⟩ <;> simp [hx]
      have hright : ∀ y ∈ [[-T, T]], f (↑c₁ + ↑y * I) = h (↑c₁ + ↑y * I) := by
        intro y hy; apply hfeq'
        refine ⟨?_, ?_⟩ <;> simp [hy]
      have hleft : ∀ y ∈ [[-T, T]], f (↑c₂ + ↑y * I) = h (↑c₂ + ↑y * I) := by
        intro y hy; apply hfeq'
        refine ⟨?_, ?_⟩ <;> simp [hy]
      rw [intervalIntegral.integral_congr hbot, intervalIntegral.integral_congr htop,
          intervalIntegral.integral_congr hright, intervalIntegral.integral_congr hleft]
    rw [heq, Finset.sum_empty, mul_zero]
    exact rectangleBoundaryIntegral_eq_zero_of_holomorphic hh_cont hh_diff
  | @insert z₀ poles' hz₀_not_mem IH =>
    -- z₀ data
    have hz₀ := hpoles_mem z₀ (Finset.mem_insert_self z₀ poles')
    obtain ⟨hz₀_c₂, hz₀_c₁, hz₀_Tm, hz₀_T⟩ := hz₀
    -- Define f' = (∑ i ∈ poles', (s - i)⁻¹ * g i s) + h s  (one fewer pole)
    set f' : ℂ → ℂ := fun s => (∑ i ∈ poles', (s - i)⁻¹ * g i s) + h s with hf'_def
    -- Define f_z = (s - z₀)⁻¹ * g z₀ s  (just the z₀ pole piece)
    set f_z : ℂ → ℂ := fun s => (s - z₀)⁻¹ * g z₀ s with hfz_def
    -- On the boundary, f s = f_z s + f' s (since boundary points are not poles).
    -- First lift the "no boundary contains poles" fact.
    have hbdy_not_pole : ∀ s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]),
        (s.re = c₂ ∨ s.re = c₁ ∨ s.im = -T ∨ s.im = T) → ∀ i ∈ insert z₀ poles', s ≠ i := by
      intro s _ hbdy i hi hsi
      rcases hpoles_mem i hi with ⟨h1, h2, h3, h4⟩
      rcases hbdy with hb | hb | hb | hb
      · have : i.re = c₂ := by rw [← hsi]; exact hb
        linarith
      · have : i.re = c₁ := by rw [← hsi]; exact hb
        linarith
      · have : i.im = -T := by rw [← hsi]; exact hb
        linarith
      · have : i.im = T := by rw [← hsi]; exact hb
        linarith
    -- Pointwise decomposition on the boundary.
    have hf_split : ∀ s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]),
        (s.re = c₂ ∨ s.re = c₁ ∨ s.im = -T ∨ s.im = T) → f s = f_z s + f' s := by
      intro s hs hbdy
      have hne := hbdy_not_pole s hs hbdy
      rw [hfeq s hs hne, hf'_def, hfz_def]
      rw [Finset.sum_insert hz₀_not_mem]
      ring
    -- Each pole's `g i` and `h` are continuous on the rectangle; the sum + h is too,
    -- so by the no-pole boundary, f_z and f' are continuous along each side (no
    -- singularities), and we can split the integrals via integral_add + integral_congr.
    -- Continuity of g z₀ on the rectangle:
    have hgz_cont : ContinuousOn (g z₀) ([[c₂, c₁]] ×ℂ [[-T, T]]) :=
      hg_cont z₀ (Finset.mem_insert_self z₀ poles')
    have hgz_diff : DifferentiableOn ℂ (g z₀)
        (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)) :=
      hg_diff z₀ (Finset.mem_insert_self z₀ poles')
    -- Apply single-pole rectangle_residue to f_z (with g = g z₀, z₀ = z₀).
    have hfz_res :
        (∫ x in c₂..c₁, f_z (↑x + ↑(-T) * I)) -
        (∫ x in c₂..c₁, f_z (↑x + ↑T * I)) +
        I • (∫ y in (-T)..T, f_z (↑c₁ + ↑y * I)) -
        I • (∫ y in (-T)..T, f_z (↑c₂ + ↑y * I)) = 2 * ↑Real.pi * I * g z₀ z₀ := by
      apply Complex.rectangle_residue hz₀_c₂ hz₀_c₁ hz₀_Tm hz₀_T hgz_cont hgz_diff
      intro s _ hs_ne; rfl
    -- Apply IH to f' on poles'.
    have hpoles_mem' : ∀ z ∈ poles', c₂ < z.re ∧ z.re < c₁ ∧ -T < z.im ∧ z.im < T :=
      fun z hz => hpoles_mem z (Finset.mem_insert_of_mem hz)
    have hg_cont' : ∀ i ∈ poles', ContinuousOn (g i) ([[c₂, c₁]] ×ℂ [[-T, T]]) :=
      fun i hi => hg_cont i (Finset.mem_insert_of_mem hi)
    have hg_diff' : ∀ i ∈ poles', DifferentiableOn ℂ (g i)
        (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)) :=
      fun i hi => hg_diff i (Finset.mem_insert_of_mem hi)
    have hf'_eq : ∀ s, s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) → (∀ i ∈ poles', s ≠ i) →
        f' s = (∑ i ∈ poles', (s - i)⁻¹ * g i s) + h s := by
      intro s _ _; rfl
    have IH' := IH h f' hpoles_mem' hg_cont' hg_diff' hh_cont hh_diff hf'_eq
    -- We split each of the 4 boundary integrals via integral_add (per side
    -- f_z and f' are continuous and bounded, hence interval-integrable).
    --
    -- Helpers: define the four "sides" as subsets of [[c₂,c₁]] / [[-T,T]] in ℂ.
    -- Continuity of f_z on a horizontal side (im = ±T): denominator (·) - z₀ doesn't
    -- vanish since z₀.im ∈ (-T, T) strictly, so im((↑x + ±T·I) - z₀) = ±T - z₀.im ≠ 0.
    have hgz_cont_bot : ContinuousOn (fun x : ℝ => g z₀ (↑x + ↑(-T) * I)) [[c₂, c₁]] := by
      refine (hgz_cont.comp ?_ ?_)
      · exact (continuous_ofReal.add (continuous_const)).continuousOn
      · intro x hx
        refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
    -- Rather than spell out all four sides (tedious), use a single helper for one
    -- side, parameterized; but for now produce the four integrability facts directly.
    -- Bottom side: f_z (↑x + ↑(-T) * I)
    have hfz_int_bot : IntervalIntegrable (fun x => f_z (↑x + ↑(-T) * I))
        MeasureTheory.volume c₂ c₁ := by
      apply ContinuousOn.intervalIntegrable
      simp only [hfz_def]
      refine ContinuousOn.mul ?_ hgz_cont_bot
      apply ContinuousOn.inv₀
      · exact (((continuous_ofReal.add continuous_const).continuousOn).sub continuousOn_const)
      · intro x _ hzero
        have him : ((↑x : ℂ) + ↑(-T) * I - z₀).im = -T - z₀.im := by simp
        rw [hzero, Complex.zero_im] at him
        linarith
    have hfz_int_top : IntervalIntegrable (fun x => f_z (↑x + ↑T * I))
        MeasureTheory.volume c₂ c₁ := by
      apply ContinuousOn.intervalIntegrable
      simp only [hfz_def]
      refine ContinuousOn.mul ?_ ?_
      · apply ContinuousOn.inv₀
        · exact (((continuous_ofReal.add continuous_const).continuousOn).sub continuousOn_const)
        · intro x _ hzero
          have him : ((↑x : ℂ) + ↑T * I - z₀).im = T - z₀.im := by simp
          rw [hzero, Complex.zero_im] at him
          linarith
      · refine (hgz_cont.comp ?_ ?_)
        · exact (continuous_ofReal.add continuous_const).continuousOn
        · intro x hx
          refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
    have hfz_int_right : IntervalIntegrable (fun y => f_z (↑c₁ + ↑y * I))
        MeasureTheory.volume (-T) T := by
      apply ContinuousOn.intervalIntegrable
      simp only [hfz_def]
      refine ContinuousOn.mul ?_ ?_
      · apply ContinuousOn.inv₀
        · exact (ContinuousOn.sub (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const)) continuousOn_const)
        · intro y _ hzero
          have hre : ((↑c₁ : ℂ) + ↑y * I - z₀).re = c₁ - z₀.re := by simp
          rw [hzero, Complex.zero_re] at hre
          linarith
      · refine (hgz_cont.comp ?_ ?_)
        · exact (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const))
        · intro y hy
          refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
    have hfz_int_left : IntervalIntegrable (fun y => f_z (↑c₂ + ↑y * I))
        MeasureTheory.volume (-T) T := by
      apply ContinuousOn.intervalIntegrable
      simp only [hfz_def]
      refine ContinuousOn.mul ?_ ?_
      · apply ContinuousOn.inv₀
        · exact (ContinuousOn.sub (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const)) continuousOn_const)
        · intro y _ hzero
          have hre : ((↑c₂ : ℂ) + ↑y * I - z₀).re = c₂ - z₀.re := by simp
          rw [hzero, Complex.zero_re] at hre
          linarith
      · refine (hgz_cont.comp ?_ ?_)
        · exact (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const))
        · intro y hy
          refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
    -- f' integrability on each side: each summand (s - i)⁻¹ * g i s is continuous on
    -- the side since i is strictly interior, and h is continuous on the rectangle.
    -- Build a generic helper:
    have hf'_int_bot : IntervalIntegrable (fun x => f' (↑x + ↑(-T) * I))
        MeasureTheory.volume c₂ c₁ := by
      apply ContinuousOn.intervalIntegrable
      simp only [hf'_def]
      refine ContinuousOn.add ?_ ?_
      · apply continuousOn_finsetSum
        intro i hi
        rcases hpoles_mem' i hi with ⟨_, _, hiTm, hiT⟩
        refine ContinuousOn.mul ?_ ?_
        · apply ContinuousOn.inv₀
          · exact (((continuous_ofReal.add continuous_const).continuousOn).sub continuousOn_const)
          · intro x _ hzero
            have him : ((↑x : ℂ) + ↑(-T) * I - i).im = -T - i.im := by simp
            rw [hzero, Complex.zero_im] at him; linarith
        · refine ((hg_cont' i hi).comp ?_ ?_)
          · exact (continuous_ofReal.add continuous_const).continuousOn
          · intro x hx
            refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
      · refine (hh_cont.comp ?_ ?_)
        · exact (continuous_ofReal.add continuous_const).continuousOn
        · intro x hx
          refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
    have hf'_int_top : IntervalIntegrable (fun x => f' (↑x + ↑T * I))
        MeasureTheory.volume c₂ c₁ := by
      apply ContinuousOn.intervalIntegrable
      simp only [hf'_def]
      refine ContinuousOn.add ?_ ?_
      · apply continuousOn_finsetSum
        intro i hi
        rcases hpoles_mem' i hi with ⟨_, _, hiTm, hiT⟩
        refine ContinuousOn.mul ?_ ?_
        · apply ContinuousOn.inv₀
          · exact (((continuous_ofReal.add continuous_const).continuousOn).sub continuousOn_const)
          · intro x _ hzero
            have him : ((↑x : ℂ) + ↑T * I - i).im = T - i.im := by simp
            rw [hzero, Complex.zero_im] at him; linarith
        · refine ((hg_cont' i hi).comp ?_ ?_)
          · exact (continuous_ofReal.add continuous_const).continuousOn
          · intro x hx
            refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
      · refine (hh_cont.comp ?_ ?_)
        · exact (continuous_ofReal.add continuous_const).continuousOn
        · intro x hx
          refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
    have hf'_int_right : IntervalIntegrable (fun y => f' (↑c₁ + ↑y * I))
        MeasureTheory.volume (-T) T := by
      apply ContinuousOn.intervalIntegrable
      simp only [hf'_def]
      refine ContinuousOn.add ?_ ?_
      · apply continuousOn_finsetSum
        intro i hi
        rcases hpoles_mem' i hi with ⟨hic₂, hic₁, _, _⟩
        refine ContinuousOn.mul ?_ ?_
        · apply ContinuousOn.inv₀
          · exact (ContinuousOn.sub (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const)) continuousOn_const)
          · intro y _ hzero
            have hre : ((↑c₁ : ℂ) + ↑y * I - i).re = c₁ - i.re := by simp
            rw [hzero, Complex.zero_re] at hre; linarith
        · refine ((hg_cont' i hi).comp ?_ ?_)
          · exact (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const))
          · intro y hy
            refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
      · refine (hh_cont.comp ?_ ?_)
        · exact (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const))
        · intro y hy
          refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
    have hf'_int_left : IntervalIntegrable (fun y => f' (↑c₂ + ↑y * I))
        MeasureTheory.volume (-T) T := by
      apply ContinuousOn.intervalIntegrable
      simp only [hf'_def]
      refine ContinuousOn.add ?_ ?_
      · apply continuousOn_finsetSum
        intro i hi
        rcases hpoles_mem' i hi with ⟨hic₂, hic₁, _, _⟩
        refine ContinuousOn.mul ?_ ?_
        · apply ContinuousOn.inv₀
          · exact (ContinuousOn.sub (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const)) continuousOn_const)
          · intro y _ hzero
            have hre : ((↑c₂ : ℂ) + ↑y * I - i).re = c₂ - i.re := by simp
            rw [hzero, Complex.zero_re] at hre; linarith
        · refine ((hg_cont' i hi).comp ?_ ?_)
          · exact (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const))
          · intro y hy
            refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
      · refine (hh_cont.comp ?_ ?_)
        · exact (continuousOn_const.add ((continuous_ofReal.continuousOn).mul continuousOn_const))
        · intro y hy
          refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
    -- Boundary equality lemmas: for each side, f = f_z + f' pointwise.
    have hbdy_bot : ∀ x ∈ [[c₂, c₁]],
        f (↑x + ↑(-T) * I) = f_z (↑x + ↑(-T) * I) + f' (↑x + ↑(-T) * I) := by
      intro x hx
      have hs_mem : (↑x + ↑(-T) * I) ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) := by
        refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
      apply hf_split _ hs_mem
      right; right; left; simp
    have hbdy_top : ∀ x ∈ [[c₂, c₁]],
        f (↑x + ↑T * I) = f_z (↑x + ↑T * I) + f' (↑x + ↑T * I) := by
      intro x hx
      have hs_mem : (↑x + ↑T * I) ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) := by
        refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hx, hmin_T, hmax_T]
      apply hf_split _ hs_mem
      right; right; right; simp
    have hbdy_right : ∀ y ∈ [[-T, T]],
        f (↑c₁ + ↑y * I) = f_z (↑c₁ + ↑y * I) + f' (↑c₁ + ↑y * I) := by
      intro y hy
      have hs_mem : (↑c₁ + ↑y * I) ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) := by
        refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
      apply hf_split _ hs_mem
      right; left; simp
    have hbdy_left : ∀ y ∈ [[-T, T]],
        f (↑c₂ + ↑y * I) = f_z (↑c₂ + ↑y * I) + f' (↑c₂ + ↑y * I) := by
      intro y hy
      have hs_mem : (↑c₂ + ↑y * I) ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) := by
        refine ⟨?_, ?_⟩ <;> simp [mem_reProdIm, hy, hmin_c, hmax_c]
      apply hf_split _ hs_mem
      left; simp
    -- Split each integral.
    have hI_bot : (∫ x in c₂..c₁, f (↑x + ↑(-T) * I))
        = (∫ x in c₂..c₁, f_z (↑x + ↑(-T) * I)) + (∫ x in c₂..c₁, f' (↑x + ↑(-T) * I)) := by
      rw [intervalIntegral.integral_congr hbdy_bot,
          intervalIntegral.integral_add hfz_int_bot hf'_int_bot]
    have hI_top : (∫ x in c₂..c₁, f (↑x + ↑T * I))
        = (∫ x in c₂..c₁, f_z (↑x + ↑T * I)) + (∫ x in c₂..c₁, f' (↑x + ↑T * I)) := by
      rw [intervalIntegral.integral_congr hbdy_top,
          intervalIntegral.integral_add hfz_int_top hf'_int_top]
    have hI_right : (∫ y in (-T)..T, f (↑c₁ + ↑y * I))
        = (∫ y in (-T)..T, f_z (↑c₁ + ↑y * I)) + (∫ y in (-T)..T, f' (↑c₁ + ↑y * I)) := by
      rw [intervalIntegral.integral_congr hbdy_right,
          intervalIntegral.integral_add hfz_int_right hf'_int_right]
    have hI_left : (∫ y in (-T)..T, f (↑c₂ + ↑y * I))
        = (∫ y in (-T)..T, f_z (↑c₂ + ↑y * I)) + (∫ y in (-T)..T, f' (↑c₂ + ↑y * I)) := by
      rw [intervalIntegral.integral_congr hbdy_left,
          intervalIntegral.integral_add hfz_int_left hf'_int_left]
    -- Assemble.
    unfold rectangleBoundaryIntegral at IH' ⊢
    rw [hI_bot, hI_top, hI_right, hI_left]
    -- Now LHS = (fz_bot + f'_bot) - (fz_top + f'_top) + I•(fz_right + f'_right)
    --        - I•(fz_left + f'_left)
    --        = [fz-rectangle-integral] + [f'-rectangle-integral]
    --        = 2πi·g z₀ z₀ + 2πi·∑ poles' g i i
    --        = 2πi · ∑ (insert z₀ poles') g i i
    rw [Finset.sum_insert hz₀_not_mem]
    rw [smul_add, smul_add]
    have : (∫ x in c₂..c₁, f_z (↑x + ↑(-T) * I)) + (∫ x in c₂..c₁, f' (↑x + ↑(-T) * I)) -
           ((∫ x in c₂..c₁, f_z (↑x + ↑T * I)) + (∫ x in c₂..c₁, f' (↑x + ↑T * I))) +
           (I • (∫ y in (-T)..T, f_z (↑c₁ + ↑y * I)) +
            I • (∫ y in (-T)..T, f' (↑c₁ + ↑y * I))) -
           (I • (∫ y in (-T)..T, f_z (↑c₂ + ↑y * I)) +
            I • (∫ y in (-T)..T, f' (↑c₂ + ↑y * I))) =
           ((∫ x in c₂..c₁, f_z (↑x + ↑(-T) * I)) - (∫ x in c₂..c₁, f_z (↑x + ↑T * I)) +
             I • (∫ y in (-T)..T, f_z (↑c₁ + ↑y * I)) -
             I • (∫ y in (-T)..T, f_z (↑c₂ + ↑y * I))) +
           ((∫ x in c₂..c₁, f' (↑x + ↑(-T) * I)) - (∫ x in c₂..c₁, f' (↑x + ↑T * I)) +
             I • (∫ y in (-T)..T, f' (↑c₁ + ↑y * I)) -
             I • (∫ y in (-T)..T, f' (↑c₂ + ↑y * I))) := by ring
    rw [this, hfz_res, IH']
    ring

end Complex
