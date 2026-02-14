/-
Copyright (c) 2025 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rectangle residue theorem and vertical line shift

This file proves the rectangle residue theorem: if `f(z) = (z - z₀)⁻¹ * g(z)` where `g` is
holomorphic, then the boundary integral of `f` around a rectangle containing `z₀` equals
`2πi * g(z₀)`.

The main application is the vertical line shift formula for Mellin-Barnes integrals: shifting
a vertical line integral from `Re(s) = c₁` to `Re(s) = c₂` picks up a residue term plus
horizontal boundary contributions.

## Main definitions

* `Complex.verticalLineIntegral f c T`: the integral `∫_{c-iT}^{c+iT} f(s) ds`.
* `Complex.horizontalLineIntegral f a b T`: the integral `∫_a^b f(σ + iT) dσ`.

## Main results

* `Complex.rect_winding_number_eq_two_pi_I`: winding number of rectangle = 2πi.
* `Complex.rectangle_residue`: rectangle boundary integral equals `2πi * g(z₀)`.
* `Complex.verticalLine_shift`: shifting a vertical line integral picks up the residue.

## Proof strategy

The winding number integral `∮ (z - z₀)⁻¹ dz = 2πi` around a rectangle is proved by FTC
with `Complex.log` as antiderivative on each side. Three sides stay in `slitPlane`;
the left side uses `log(-·)` to avoid the branch cut, with `±πi` jumps summing to `2πi`.

The full rectangle residue theorem then follows from `dslope` decomposition: writing
`f(z) = g(z₀) * (z - z₀)⁻¹ + dslope(g, z₀)(z)`, the `dslope` term vanishes by
Cauchy-Goursat, and the constant factors out by linearity.

## References

* [E. M. Stein and R. Shakarchi, *Complex Analysis*][stein2003], Chapter 2
* [J. B. Conway, *Functions of One Complex Variable*][conway1978], IV.5
-/

open Complex MeasureTheory Set Filter Topology
open scoped Interval

noncomputable section

namespace Complex

/-! ### Vertical and horizontal line integrals -/

/-- A vertical line integral `∫_{c-iT}^{c+iT} f(s) ds`, parameterized by `t ∈ [-T, T]`. -/
noncomputable def verticalLineIntegral (f : ℂ → ℂ) (c : ℝ) (T : ℝ) : ℂ :=
  ∫ t in (-T)..T, f (↑c + ↑t * I)

/-- A horizontal line integral `∫_a^b f(σ + iT) dσ`. -/
noncomputable def horizontalLineIntegral (f : ℂ → ℂ) (a b : ℝ) (T : ℝ) : ℂ :=
  ∫ σ in a..b, f (↑σ + ↑T * I)

/-! ### Rectangle residue theorem -/

section RectangleResidue

private lemma log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + ↑Real.pi * I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
  push_cast; ring

private lemma log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - ↑Real.pi * I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
  push_cast; ring

private lemma horiz_ftc (z₀ : ℂ) (K a b : ℝ)
    (hslit : ∀ x ∈ [[a, b]], ((↑x + ↑K * I) - z₀ : ℂ) ∈ slitPlane) :
    (∫ x in a..b, (((↑x : ℂ) + ↑K * I) - z₀)⁻¹) =
      Complex.log ((↑b + ↑K * I) - z₀) - Complex.log ((↑a + ↑K * I) - z₀) := by
  have hderiv : ∀ x ∈ [[a, b]], HasDerivAt
      (fun (t : ℝ) => Complex.log (((↑t : ℂ) + ↑K * I) - z₀))
      (((↑x : ℂ) + ↑K * I - z₀)⁻¹) x := by
    intro x hx
    have hf : HasDerivAt (fun (t : ℝ) => ((↑t : ℂ) + ↑K * I) - z₀) 1 x := by
      have h := (RCLike.ofRealCLM (K := ℂ)).hasDerivAt (x := x)
      simpa [RCLike.ofRealCLM_apply] using (h.add_const (↑K * I)).sub_const z₀
    rw [inv_eq_one_div]
    exact hf.clog_real (hslit x hx)
  have hint : IntervalIntegrable
      (fun x => (((↑x : ℂ) + ↑K * I) - z₀)⁻¹) volume a b :=
    ((continuous_ofReal.add continuous_const).sub continuous_const).continuousOn.inv₀
      (fun x hx => slitPlane_ne_zero (hslit x hx)) |>.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private lemma vert_ftc (z₀ : ℂ) (c a b : ℝ)
    (hslit : ∀ y ∈ [[a, b]], ((↑c + ↑y * I) - z₀ : ℂ) ∈ slitPlane) :
    (∫ y in a..b, (((↑c : ℂ) + ↑y * I) - z₀)⁻¹) =
      -I * (Complex.log ((↑c + ↑b * I) - z₀) - Complex.log ((↑c + ↑a * I) - z₀)) := by
  have hderiv : ∀ y ∈ [[a, b]], HasDerivAt
      (fun (t : ℝ) => -I * Complex.log (((↑c : ℂ) + ↑t * I) - z₀))
      (((↑c : ℂ) + ↑y * I - z₀)⁻¹) y := by
    intro y hy
    have hparam : HasDerivAt (fun (t : ℝ) => ((↑c : ℂ) + ↑t * I) - z₀) I y := by
      have h := (RCLike.ofRealCLM (K := ℂ)).hasDerivAt (x := y)
      simpa [RCLike.ofRealCLM_apply] using ((h.mul_const I).const_add (↑c : ℂ)).sub_const z₀
    have hlog := hparam.clog_real (hslit y hy)
    have hderiv_val := (hlog.const_mul (-I))
    convert hderiv_val using 1
    rw [div_eq_mul_inv, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  have hint : IntervalIntegrable
      (fun y => (((↑c : ℂ) + ↑y * I) - z₀)⁻¹) volume a b :=
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const).continuousOn.inv₀
      (fun y hy => slitPlane_ne_zero (hslit y hy)) |>.intervalIntegrable
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [ftc]; ring

private lemma vert_ftc_neg (z₀ : ℂ) (c a b : ℝ)
    (hslit : ∀ y ∈ [[a, b]], (-((↑c + ↑y * I) - z₀) : ℂ) ∈ slitPlane) :
    (∫ y in a..b, (((↑c : ℂ) + ↑y * I) - z₀)⁻¹) =
      -I * (Complex.log (-((↑c + ↑b * I) - z₀)) -
            Complex.log (-((↑c + ↑a * I) - z₀))) := by
  have hderiv : ∀ y ∈ [[a, b]], HasDerivAt
      (fun (t : ℝ) => -I * Complex.log (-(((↑c : ℂ) + ↑t * I) - z₀)))
      (((↑c : ℂ) + ↑y * I - z₀)⁻¹) y := by
    intro y hy
    have hinner : HasDerivAt (fun (t : ℝ) => ((↑c : ℂ) + ↑t * I) - z₀) I y := by
      have h := (RCLike.ofRealCLM (K := ℂ)).hasDerivAt (x := y)
      simpa [RCLike.ofRealCLM_apply] using ((h.mul_const I).const_add (↑c : ℂ)).sub_const z₀
    have hparam := hinner.neg
    have hlog := hparam.clog_real (hslit y hy)
    have hderiv_val := (hlog.const_mul (-I))
    convert hderiv_val using 1
    simp only [Pi.neg_apply]
    rw [div_neg, neg_div, neg_neg, div_eq_mul_inv, ← mul_assoc, neg_mul, I_mul_I, neg_neg,
      one_mul]
  have hint : IntervalIntegrable
      (fun y => (((↑c : ℂ) + ↑y * I) - z₀)⁻¹) volume a b :=
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const).continuousOn.inv₀
      (fun y hy => neg_ne_zero.mp (slitPlane_ne_zero (hslit y hy))) |>.intervalIntegrable
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [ftc]; ring

/-- **Winding number**: the Mathlib rectangle boundary integral of `(z - z₀)⁻¹`
around a rectangle containing `z₀` in its interior equals `2πi`.

Three sides (bottom, top, right) stay in `slitPlane` — straightforward FTC with `log`.
The left side uses `log(-·)` to avoid the branch cut, picking up `±πi` jumps
that sum to `2πi`. -/
theorem rect_winding_number_eq_two_pi_I (z₀ : ℂ) (c₂ c₁ T : ℝ)
    (hc : c₂ < z₀.re) (hc' : z₀.re < c₁)
    (hT : -T < z₀.im) (hT' : z₀.im < T) :
    (∫ x in c₂..c₁, ((↑x + ↑(-T) * I) - z₀)⁻¹) -
    (∫ x in c₂..c₁, ((↑x + ↑T * I) - z₀)⁻¹) +
    I • (∫ y in (-T)..T, ((↑c₁ + ↑y * I) - z₀)⁻¹) -
    I • (∫ y in (-T)..T, ((↑c₂ + ↑y * I) - z₀)⁻¹) = 2 * ↑Real.pi * I := by
  have hbot := horiz_ftc z₀ (-T) c₂ c₁ (fun x hx => by
    simp only [slitPlane, mem_setOf]; right
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im]; linarith)
  have htop := horiz_ftc z₀ T c₂ c₁ (fun x hx => by
    simp only [slitPlane, mem_setOf]; right
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im]; linarith)
  have hright := vert_ftc z₀ c₁ (-T) T (fun y hy => by
    simp only [slitPlane, mem_setOf]; left
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re]; linarith)
  have hleft := vert_ftc_neg z₀ c₂ (-T) T (fun y hy => by
    simp only [slitPlane, mem_setOf]; left
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re]; linarith)
  have ha_im : ((↑c₂ + ↑(-T) * I) - z₀).im < 0 := by
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im]; linarith
  have hd_im : 0 < ((↑c₂ + ↑T * I) - z₀).im := by
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im]; linarith
  simp only [smul_eq_mul]
  rw [hbot, htop, hright, hleft, log_neg_of_im_pos hd_im, log_neg_of_im_neg ha_im]
  have hI2 : (I : ℂ) * I = -1 := I_mul_I
  set A := Complex.log ((↑c₁ + ↑(-T) * I) - z₀)
  set B := Complex.log ((↑c₂ + ↑(-T) * I) - z₀)
  set C := Complex.log ((↑c₁ + ↑T * I) - z₀)
  set D := Complex.log ((↑c₂ + ↑T * I) - z₀)
  linear_combination (-C + A + D - B - 2 * ↑Real.pi * I) * hI2

private lemma integral_decompose_side (g₀ z₀ : ℂ) (F f : ℂ → ℂ) (param : ℝ → ℂ) (a b : ℝ)
    (hpt : EqOn (fun t => f (param t))
      (fun t => g₀ * (param t - z₀)⁻¹ + F (param t)) [[a, b]])
    (hi1 : IntervalIntegrable (fun t => g₀ * (param t - z₀)⁻¹) volume a b)
    (hi2 : IntervalIntegrable (fun t => F (param t)) volume a b) :
    ∫ t in a..b, f (param t) =
      g₀ * (∫ t in a..b, (param t - z₀)⁻¹) + ∫ t in a..b, F (param t) := by
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul]

/-- **Boundary integral decomposition**: the boundary integral of `f` equals
`g(z₀)` times the boundary integral of `(· - z₀)⁻¹`, by the `dslope` trick.

Uses `dslope g z₀` as the removable singularity: `f(z) = g(z₀) * (z-z₀)⁻¹ + dslope(g,z₀)(z)`.
The `dslope` term vanishes by Cauchy-Goursat. -/
private theorem boundary_integral_eq_residue_times_winding
    {f g : ℂ → ℂ} {z₀ : ℂ} {c₁ c₂ T : ℝ}
    (hc : c₂ < z₀.re) (hc' : z₀.re < c₁)
    (hT : -T < z₀.im) (hT' : z₀.im < T)
    (hg_cont : ContinuousOn g ([[c₂, c₁]] ×ℂ [[-T, T]]))
    (hg_diff : DifferentiableOn ℂ g
      (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)))
    (hfg : ∀ s, s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) → s ≠ z₀ →
      f s = (s - z₀)⁻¹ * g s) :
    (∫ x in c₂..c₁, f (↑x + ↑(-T) * I)) -
    (∫ x in c₂..c₁, f (↑x + ↑T * I)) +
    I • (∫ y in (-T)..T, f (↑c₁ + ↑y * I)) -
    I • (∫ y in (-T)..T, f (↑c₂ + ↑y * I)) =
    g z₀ * ((∫ x in c₂..c₁, ((↑x + ↑(-T) * I) - z₀)⁻¹) -
      (∫ x in c₂..c₁, ((↑x + ↑T * I) - z₀)⁻¹) +
      I • (∫ y in (-T)..T, ((↑c₁ + ↑y * I) - z₀)⁻¹) -
      I • (∫ y in (-T)..T, ((↑c₂ + ↑y * I) - z₀)⁻¹)) := by
  set F := dslope g z₀ with hF_def
  have hz₀_open : z₀ ∈ Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T) :=
    ⟨⟨lt_of_le_of_lt (min_le_left _ _) hc, lt_of_lt_of_le hc' (le_max_right _ _)⟩,
     ⟨lt_of_le_of_lt (min_le_left _ _) hT, lt_of_lt_of_le hT' (le_max_right _ _)⟩⟩
  have hRect_nhd : ([[c₂, c₁]] ×ℂ [[-T, T]]) ∈ nhds z₀ :=
    Filter.mem_of_superset
      ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz₀_open)
      (fun _ hz => ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
  have hg_at : DifferentiableAt ℂ g z₀ :=
    hg_diff.differentiableAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz₀_open)
  have hF_cont : ContinuousOn F ([[c₂, c₁]] ×ℂ [[-T, T]]) :=
    (continuousOn_dslope hRect_nhd).mpr ⟨hg_cont, hg_at⟩
  have hF_diff : ∀ x ∈ (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ
      Ioo (min (-T) T) (max (-T) T)) \ {z₀}, DifferentiableAt ℂ F x := by
    intro x ⟨hx, hne⟩
    have hne' : x ≠ z₀ := fun h => hne (h ▸ mem_singleton _)
    exact (differentiableAt_dslope_of_ne hne').mpr
      (hg_diff.differentiableAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx))
  have hcg := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    F ⟨c₂, -T⟩ ⟨c₁, T⟩ {z₀} (countable_singleton z₀) hF_cont hF_diff
  have hpt : ∀ z, z ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) → z ≠ z₀ →
      f z = g z₀ * (z - z₀)⁻¹ + F z := by
    intro z hmem hne
    rw [hfg z hmem hne, hF_def, dslope_of_ne _ hne]
    simp only [slope, vsub_eq_sub, smul_eq_mul]; ring
  have hTle : -T ≤ T := le_of_lt (lt_trans hT hT')
  have hc12 : c₂ ≤ c₁ := le_of_lt (lt_trans hc hc')
  have h1 := integral_decompose_side (g z₀) z₀ F f (fun x => ↑x + ↑(-T) * I) c₂ c₁
    (fun t ht => hpt _ ⟨by simpa using ht, by simp⟩
      (by intro h; have := congr_arg im h; simp at this; linarith))
    (by
      apply ContinuousOn.intervalIntegrable
      exact continuousOn_const.mul
        (((continuous_ofReal.add continuous_const).continuousOn.sub
          continuousOn_const).inv₀
          (fun t _ h => by have := congr_arg im h; simp at this; linarith)))
    (by
      exact (hF_cont.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun t ht => ⟨by simpa using ht,
          by simp⟩)).intervalIntegrable)
  have h2 := integral_decompose_side (g z₀) z₀ F f (fun x => ↑x + ↑T * I) c₂ c₁
    (fun t ht => hpt _ ⟨by simpa using ht, by simp⟩
      (by intro h; have := congr_arg im h; simp at this; linarith))
    (by apply ContinuousOn.intervalIntegrable
        exact continuousOn_const.mul
          (((continuous_ofReal.add continuous_const).continuousOn.sub
            continuousOn_const).inv₀
            (fun t _ h => by have := congr_arg im h; simp at this; linarith)))
    (by exact (hF_cont.comp (continuous_ofReal.add continuous_const).continuousOn
          (fun t ht => ⟨by simpa using ht,
            by simp⟩)).intervalIntegrable)
  have h3 := integral_decompose_side (g z₀) z₀ F f (fun y => ↑c₁ + ↑y * I) (-T) T
    (fun t ht => hpt _ ⟨by simp, by simpa using ht⟩
      (by intro h; have := congr_arg re h; simp at this; linarith))
    (by apply ContinuousOn.intervalIntegrable
        exact continuousOn_const.mul
          (((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
            continuousOn_const).inv₀
            (fun t _ h => by have := congr_arg re h; simp at this; linarith)))
    (by exact (hF_cont.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
          (fun t ht => ⟨by simp,
            by simpa using ht⟩)).intervalIntegrable)
  have h4 := integral_decompose_side (g z₀) z₀ F f (fun y => ↑c₂ + ↑y * I) (-T) T
    (fun t ht => hpt _ ⟨by simp, by simpa using ht⟩
      (by intro h; have := congr_arg re h; simp at this; linarith))
    (by apply ContinuousOn.intervalIntegrable
        exact continuousOn_const.mul
          (((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
            continuousOn_const).inv₀
            (fun t _ h => by have := congr_arg re h; simp at this; linarith)))
    (by exact (hF_cont.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
          (fun t ht => ⟨by simp,
            by simpa using ht⟩)).intervalIntegrable)
  simp only [h1, h2, h3, h4, smul_eq_mul] at hcg ⊢
  linear_combination hcg

end RectangleResidue

/-- **Rectangle residue theorem** (Mathlib native format): If `f(z) = (z - z₀)⁻¹ * g(z)`
where `g` is continuous on the closed rectangle and holomorphic on the interior,
and `z₀` is in the interior, then the boundary integral equals `2πi * g(z₀)`.

Proved from `rect_winding_number_eq_two_pi_I` (winding number = 2πi) and
`boundary_integral_eq_residue_times_winding` (Cauchy-Goursat + linearity). -/
theorem rectangle_residue {f g : ℂ → ℂ} {z₀ : ℂ} {c₁ c₂ T : ℝ}
    (hc : c₂ < z₀.re) (hc' : z₀.re < c₁)
    (hT : -T < z₀.im) (hT' : z₀.im < T)
    (hg_cont : ContinuousOn g ([[c₂, c₁]] ×ℂ [[-T, T]]))
    (hg_diff : DifferentiableOn ℂ g
      (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)))
    (hfg : ∀ s, s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) → s ≠ z₀ →
      f s = (s - z₀)⁻¹ * g s) :
    (∫ x in c₂..c₁, f (↑x + ↑(-T) * I)) -
    (∫ x in c₂..c₁, f (↑x + ↑T * I)) +
    I • (∫ y in (-T)..T, f (↑c₁ + ↑y * I)) -
    I • (∫ y in (-T)..T, f (↑c₂ + ↑y * I)) = 2 * ↑Real.pi * I * g z₀ := by
  have hW := rect_winding_number_eq_two_pi_I z₀ c₂ c₁ T hc hc' hT hT'
  have hD := boundary_integral_eq_residue_times_winding hc hc' hT hT' hg_cont hg_diff hfg
  rw [hD, hW]; ring

/-- **Vertical line shift formula**: shifting a vertical line integral from `Re(s) = c₁`
to `Re(s) = c₂` picks up the residue `2π * g(z₀)` (real coefficient!) plus horizontal
boundary terms:

`VLI(c₁) - VLI(c₂) = 2π * g(z₀) + I * (Horiz(-T) - Horiz(T))`

**Why `2π` not `2πi`**: The Mathlib contour integral has `I •` on vertical sides, so
`I * (VLI(c₁) - VLI(c₂)) + horiz = 2πi * g(z₀)`. Solving for the VLI difference
multiplies by `(-I)`, giving `(-I) * (2πi) = 2π`. -/
theorem verticalLine_shift {f g : ℂ → ℂ} {z₀ : ℂ} {c₁ c₂ T : ℝ}
    (hc : c₂ < z₀.re) (hc' : z₀.re < c₁)
    (hT : -T < z₀.im) (hT' : z₀.im < T)
    (hg_cont : ContinuousOn g ([[c₂, c₁]] ×ℂ [[-T, T]]))
    (hg_diff : DifferentiableOn ℂ g
      (Ioo (min c₂ c₁) (max c₂ c₁) ×ℂ Ioo (min (-T) T) (max (-T) T)))
    (hfg : ∀ s, s ∈ ([[c₂, c₁]] ×ℂ [[-T, T]]) → s ≠ z₀ →
      f s = (s - z₀)⁻¹ * g s) :
    verticalLineIntegral f c₁ T - verticalLineIntegral f c₂ T =
      2 * ↑Real.pi * g z₀
      + I * (horizontalLineIntegral f c₂ c₁ (-T) - horizontalLineIntegral f c₂ c₁ T) := by
  have hrect := rectangle_residue hc hc' hT hT' hg_cont hg_diff hfg
  unfold verticalLineIntegral horizontalLineIntegral
  simp only [smul_eq_mul] at hrect ⊢
  have hI2 : (I : ℂ) * I = -1 := I_mul_I
  linear_combination (-I) * hrect +
    ((∫ t in (-T)..T, f (↑c₁ + ↑t * I)) - (∫ t in (-T)..T, f (↑c₂ + ↑t * I)) -
     2 * ↑Real.pi * g z₀) * hI2

end Complex

end
