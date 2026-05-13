/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.Complex.RectangleResidueFinset
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Finite-T → infinite-T tendsto for the rectangle boundary integral

`Complex.rectangle_residue_finset` gives the rectangle boundary integral for a fixed
finite height `T`. Many applications (Mellin–Barnes contour shifts, Perron-style
inversion, L-function functional equations) instead need the limit `T → ∞`: the two
horizontal sides should disappear and the two vertical sides should become
integrals over the infinite vertical lines `Re s = c₁` and `Re s = c₂`.

This file packages that limit as a `Tendsto` statement on
`rectangleBoundaryIntegral f c₂ c₁ T`. Combined with `rectangle_residue_finset`
(which is independent of `T`'s sign and merely depends on which poles lie strictly
inside), it produces the residue identity for the infinite-vertical-line difference:

`(∫ y, f (c₁ + y * I)) - (∫ y, f (c₂ + y * I)) = 2πi · Σ residues`,

once the residues are constant in `T` (the standard situation: every pole has a
finite imaginary part, so for all sufficiently large `T` the pole set inside the
rectangle is the full given finite pole set).

## Main results

* `rectangleBoundaryIntegral_tendsto` — under integrability of the two vertical
  cross-sections on the full line and decay of the two horizontal cross-sections,
  `rectangleBoundaryIntegral f c₂ c₁ T` tends to `I • V₁ - I • V₂` as `T → ∞`,
  where `Vⱼ = ∫ y : ℝ, f (cⱼ + y * I)`.

* `verticalLineIntegral_diff_eq_residues` — corollary combining the tendsto with
  `rectangle_residue_finset`: when the rectangle residue is constant in `T` (eg.
  all poles in `poles` have imaginary part in `(-T, T)` for `T` large), the
  difference of the two infinite-line integrals equals `2πi · Σ residues`.

The proof uses `intervalIntegral_tendsto_integral` from
`Mathlib.MeasureTheory.Integral.IntegralEqImproper` for the vertical sides.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval

namespace Complex

/-- The integral over an infinite vertical line `Re s = c`, parameterised by
`y : ℝ ↦ f (c + y * I)`. -/
noncomputable def verticalLineIntegral_inf (f : ℂ → ℂ) (c : ℝ) : ℂ :=
  ∫ y : ℝ, f (↑c + ↑y * I)

/-- **Finite-T → infinite-T tendsto theorem.** Under integrability of
`y ↦ f (cⱼ + y * I)` on `ℝ` for `j = 1, 2`, and atTop-decay of the two horizontal
cross-section integrals, the four-term `rectangleBoundaryIntegral f c₂ c₁ T` tends
as `T → ∞` to `I • V₁ - I • V₂`, where `Vⱼ` is the infinite vertical line integral
at `Re s = cⱼ`.

This is the bridge needed to upgrade `rectangle_residue_finset` (finite-T multi-pole
residue) to a statement about infinite vertical lines: combined with that theorem,
the limit identity gives `V₁ - V₂ = 2πi · Σ residues / I` (cf.
`verticalLineIntegral_diff_eq_residues`).

The horizontal-decay hypotheses are stated abstractly (each horizontal-line
integral tends to `0`); in applications they follow from polynomial decay of `f`
on horizontal lines combined with bounded width `c₁ - c₂`. -/
theorem rectangleBoundaryIntegral_tendsto
    (f : ℂ → ℂ) (c₂ c₁ : ℝ)
    (h_right_int : Integrable (fun y : ℝ => f (↑c₁ + ↑y * I)) volume)
    (h_left_int  : Integrable (fun y : ℝ => f (↑c₂ + ↑y * I)) volume)
    (h_bot_decay : Tendsto (fun T : ℝ => ∫ x in c₂..c₁, f (↑x + ↑(-T) * I))
        atTop (𝓝 0))
    (h_top_decay : Tendsto (fun T : ℝ => ∫ x in c₂..c₁, f (↑x + ↑T * I))
        atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => rectangleBoundaryIntegral f c₂ c₁ T) atTop
      (𝓝 (I • verticalLineIntegral_inf f c₁ - I • verticalLineIntegral_inf f c₂)) := by
  -- Vertical-side limits via the improper-integral primitive.
  have h_neg : Tendsto (fun T : ℝ => -T) atTop atBot := tendsto_neg_atTop_atBot
  have h_id  : Tendsto (fun T : ℝ => T) atTop atTop := tendsto_id
  have h_right :
      Tendsto (fun T : ℝ => ∫ y in (-T)..T, f (↑c₁ + ↑y * I)) atTop
        (𝓝 (verticalLineIntegral_inf f c₁)) :=
    intervalIntegral_tendsto_integral h_right_int h_neg h_id
  have h_left :
      Tendsto (fun T : ℝ => ∫ y in (-T)..T, f (↑c₂ + ↑y * I)) atTop
        (𝓝 (verticalLineIntegral_inf f c₂)) :=
    intervalIntegral_tendsto_integral h_left_int h_neg h_id
  -- Apply scalar action and assemble.
  have h_right_smul :
      Tendsto (fun T : ℝ => I • (∫ y in (-T)..T, f (↑c₁ + ↑y * I))) atTop
        (𝓝 (I • verticalLineIntegral_inf f c₁)) :=
    h_right.const_smul I
  have h_left_smul :
      Tendsto (fun T : ℝ => I • (∫ y in (-T)..T, f (↑c₂ + ↑y * I))) atTop
        (𝓝 (I • verticalLineIntegral_inf f c₂)) :=
    h_left.const_smul I
  -- Combine: (bot - top) + (I • right) - (I • left) → 0 - 0 + I·V₁ - I·V₂.
  have h_bot_top :
      Tendsto (fun T : ℝ =>
          (∫ x in c₂..c₁, f (↑x + ↑(-T) * I)) - (∫ x in c₂..c₁, f (↑x + ↑T * I)))
        atTop (𝓝 (0 - 0)) :=
    h_bot_decay.sub h_top_decay
  have h_sum :
      Tendsto (fun T : ℝ => rectangleBoundaryIntegral f c₂ c₁ T) atTop
        (𝓝 ((0 - 0) + I • verticalLineIntegral_inf f c₁
              - I • verticalLineIntegral_inf f c₂)) := by
    unfold rectangleBoundaryIntegral
    exact ((h_bot_top.add h_right_smul).sub h_left_smul)
  simpa using h_sum

/-- **Infinite-vertical-line residue identity.** Under the hypotheses of
`rectangleBoundaryIntegral_tendsto` combined with the multi-pole rectangle residue
theorem applied at every sufficiently large `T`, the difference of the two infinite
vertical line integrals equals `2πi · Σ residues`.

Concretely: if the rectangle residue value `R := 2πi · Σ_{i ∈ poles} g i i` agrees
with `rectangleBoundaryIntegral f c₂ c₁ T` eventually as `T → ∞` (the standard
situation when every pole of `f` in the strip `c₂ < Re s < c₁` has bounded imaginary
part, so for `T` large the rectangle captures them all), then

`I • V₁ - I • V₂ = R`.
-/
theorem verticalLineIntegral_diff_eq_residues
    (f : ℂ → ℂ) (c₂ c₁ : ℝ) (R : ℂ)
    (h_right_int : Integrable (fun y : ℝ => f (↑c₁ + ↑y * I)) volume)
    (h_left_int  : Integrable (fun y : ℝ => f (↑c₂ + ↑y * I)) volume)
    (h_bot_decay : Tendsto (fun T : ℝ => ∫ x in c₂..c₁, f (↑x + ↑(-T) * I))
        atTop (𝓝 0))
    (h_top_decay : Tendsto (fun T : ℝ => ∫ x in c₂..c₁, f (↑x + ↑T * I))
        atTop (𝓝 0))
    (h_eventually_residue :
      ∀ᶠ T : ℝ in atTop, rectangleBoundaryIntegral f c₂ c₁ T = R) :
    I • verticalLineIntegral_inf f c₁ - I • verticalLineIntegral_inf f c₂ = R := by
  have h_tendsto :=
    rectangleBoundaryIntegral_tendsto f c₂ c₁ h_right_int h_left_int
      h_bot_decay h_top_decay
  have h_const : Tendsto (fun T : ℝ => rectangleBoundaryIntegral f c₂ c₁ T) atTop
      (𝓝 R) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [h_eventually_residue] with T hT
    exact hT.symm
  exact tendsto_nhds_unique h_tendsto h_const

end Complex
