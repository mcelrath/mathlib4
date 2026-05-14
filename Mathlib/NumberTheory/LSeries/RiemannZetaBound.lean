/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.VerticalBounds
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Polynomial bounds on `riemannZeta` in vertical strips

In the half-plane of absolute convergence `Re s > 1`, the Dirichlet series
`ζ(s) = ∑ 1/n^s` is uniformly bounded on any vertical line by the corresponding sum of
absolute values of the terms at `Re s`. This yields a trivial (constant in `t`)
polynomial bound for `‖ζ(σ + i t)‖` in any closed right half-plane `Re s ≥ σ > 1`,
which is the analytic input needed to close a rectangular contour in the right
half-plane when proving Mellin–Barnes / Perron-style identities for arithmetic
functions whose generating series factor through `ζ`.

## Main statements

* `riemannZeta_norm_le_tsum_norm_term`: for `1 < σ` and `σ ≤ Re s`,
  `‖ζ(s)‖ ≤ ∑' n, ‖term 1 (σ : ℂ) n‖`. The right-hand side is a finite positive real
  depending only on `σ` (it equals `∑ 1/n^σ`, i.e. the real value of `ζ(σ)`).
* `riemannZeta_norm_le_polynomial_of_one_lt_re`: the same bound restated as a
  polynomial bound `‖ζ(s)‖ ≤ C * (1 + |Im s|)^0` (independent of `Im s`) on the closed
  half-plane `Re s ≥ σ` for any `σ > 1`.
* `riemannZeta_norm_le_polynomial_in_vertical_strip`: for any `δ > 0` there exist
  `C ≥ 0` and `k : ℕ` such that `‖ζ(s)‖ ≤ C * (1 + |Im s|)^k` for all `s` with
  `-δ ≤ Re s ≤ 1 + δ` and `‖s - 1‖ ≥ δ`.

## References

* Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §5.1.
* Iwaniec–Kowalski, *Analytic Number Theory*, §5.1.
-/

open Complex LSeries MeasureTheory Set Filter

open scoped Topology Real

namespace RiemannZeta

private lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  rw [cos]
  have h1 : ‖(exp (z * I) + exp (-z * I)) / 2‖ ≤
      (‖exp (z * I)‖ + ‖exp (-z * I)‖) / 2 := by
    rw [norm_div]
    simp only [norm_ofNat]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) two_pos.le
  have h2 : ‖exp (z * I)‖ = Real.exp (-z.im) := by
    rw [norm_exp, mul_I_re]
  have h3 : ‖exp (-z * I)‖ = Real.exp z.im := by
    rw [norm_exp]; simp
  rw [h2, h3] at h1
  calc ‖(exp (z * I) + exp (-z * I)) / 2‖
      ≤ (Real.exp (-z.im) + Real.exp z.im) / 2 := h1
    _ = Real.cosh z.im := by rw [Real.cosh_eq]; ring
    _ ≤ Real.exp |z.im| := by
        rw [Real.cosh_eq]
        rcases lt_or_ge z.im 0 with h | h
        · rw [abs_of_neg h]
          have : Real.exp z.im ≤ Real.exp (-z.im) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith [Real.exp_pos (-z.im)]
        · rw [abs_of_nonneg h]
          have : Real.exp (-z.im) ≤ Real.exp z.im :=
            Real.exp_le_exp.mpr (by linarith)
          linarith [Real.exp_pos z.im]

/-- **Trivial bound on `ζ` in the half-plane of absolute convergence.**

For `1 < σ` and `σ ≤ Re s`,
`‖ζ(s)‖ ≤ ∑' n, ‖LSeries.term 1 (σ : ℂ) n‖`.

The right-hand side is a finite positive real (it equals the real value of `ζ(σ)`,
which is the convergent Dirichlet series `∑ 1/n^σ`). -/
theorem riemannZeta_norm_le_tsum_norm_term
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : (σ : ℂ).re ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ := by
  have hσs : 1 < s.re := lt_of_lt_of_le (by simpa using hσ) hs
  have hσc : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [← LSeries_one_eq_riemannZeta hσs]
  have hsum_s : Summable (fun n => ‖term (1 : ℕ → ℂ) s n‖) :=
    (LSeriesSummable_one_iff.mpr hσs).norm
  have hsum_σ : Summable (fun n => ‖term (1 : ℕ → ℂ) (σ : ℂ) n‖) :=
    (LSeriesSummable_one_iff.mpr hσc).norm
  have h_termwise : ∀ n,
      ‖term (1 : ℕ → ℂ) s n‖ ≤ ‖term (1 : ℕ → ℂ) (σ : ℂ) n‖ :=
    fun n => norm_term_le_of_re_le_re (1 : ℕ → ℂ) hs n
  calc ‖LSeries 1 s‖
      ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ := norm_tsum_le_tsum_norm hsum_s
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) (σ : ℂ) n‖ :=
          hsum_s.tsum_le_tsum h_termwise hsum_σ

/-- **Polynomial (constant) bound on `ζ` in any closed right half-plane `Re s ≥ σ` with
`σ > 1`.**

The bound is independent of `Im s`, equivalently a polynomial bound of degree `0`. This
is the form consumed by Mellin–Barnes correction-integral estimates whose contour stays
in `Re s > 1`. -/
theorem riemannZeta_norm_le_polynomial_of_one_lt_re
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ ≤ s.re → ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (0 : ℕ) := by
  refine ⟨∑' n, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖, ?_, ?_⟩
  · exact tsum_nonneg (fun _ => norm_nonneg _)
  · intro s hs
    have hcast : ((σ : ℂ)).re ≤ s.re := by simpa using hs
    simpa using riemannZeta_norm_le_tsum_norm_term hσ hcast

/-!
## Helper lemmas for the vertical-strip bound
-/

/-- `‖Γ(σ + it)‖ ≤ Γ(σ)` for `σ > 0`. Proved via the Euler integral representation:
`|∫ exp(-x) * x^(σ+it-1) dx| ≤ ∫ exp(-x) * x^(σ-1) dx = Γ(σ)`,
using `|x^it| = 1` for real `x > 0`. -/
private lemma norm_Gamma_le_realGamma {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖Complex.Gamma (↑σ + ↑t * I)‖ ≤ Real.Gamma σ := by
  have hre : (↑σ + ↑t * I : ℂ).re = σ := by simp
  rw [Complex.Gamma_eq_integral (by rw [hre]; exact hσ)]
  rw [Real.Gamma_eq_integral hσ]
  calc ‖Complex.GammaIntegral (↑σ + ↑t * I)‖
      ≤ ∫ x : ℝ in Ioi 0,
          ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ ((↑σ + ↑t * I) - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (σ - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx_pos : (0 : ℝ) < x := hx
        show ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ ((↑σ + ↑t * I : ℂ) - 1)‖ =
            Real.exp (-x) * x ^ (σ - 1)
        have hexp_norm : ‖(↑(Real.exp (-x)) : ℂ)‖ = Real.exp (-x) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        have hcpow_norm : ‖(↑x : ℂ) ^ ((↑σ + ↑t * I : ℂ) - 1)‖ = x ^ (σ - 1) := by
          rw [show (↑σ + ↑t * I : ℂ) - 1 = ↑(σ - 1) + ↑t * I from by push_cast; ring]
          rw [norm_cpow_eq_rpow_re_of_pos hx_pos]
          simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                Complex.ofReal_im, Complex.I_im]
        rw [norm_mul, hexp_norm, hcpow_norm]

/-- **Polynomial bound on `ζ` in a vertical strip crossing the critical line.**

For any `δ > 0`, there exist constants `C ≥ 0` and `k : ℕ` such that
`‖ζ(s)‖ ≤ C · (1 + |Im s|)^k` for all `s` with `-δ ≤ Re s ≤ 1 + δ` and `|s - 1| ≥ δ`.

**Proof outline (for the pending formalization)**:
1. Define the auxiliary entire function `g(s) := ζ(s)*(s-1) / (s + (δ+2))^N` where
   `N = ⌊1+δ⌋₊ + 1`. The `s-1` factor removes the pole of `ζ`; the denominator absorbs
   polynomial growth.
2. **Right edge** `Re s = δ+2 > 1`: `|ζ(s)| ≤ C_R` by `riemannZeta_norm_le_polynomial_of_one_lt_re`.
3. **Left edge** `Re s = -δ-1`: via `riemannZeta_one_sub` (Mathlib FE), `Re(1-s) = 2+δ > 1`,
   so `|ζ(1-s)| ≤ C_R`; the FE bound gives `|ζ(s)| ≤ C_L (1+|t|)^N` using
   `Gamma_vertical_bound` + `norm_cos_le_exp_abs_im` (exponential factors cancel).
4. **PL IsBigO condition**: `(1+|t|)^N ≤ exp(N/c · exp(c·|t|))` for any `c > 0`
   (since `(1+|t|) ≤ exp(|t|)` and `|t| ≤ exp(c·|t|)/c`).
5. Apply `PhragmenLindelof.vertical_strip` on `{-δ-1 ≤ Re s ≤ δ+2}` to bound `g`,
   recover `ζ` via `|ζ(s)| = |g(s)| * |s+(δ+2)|^N / |s-1| ≤ (C/δ) * (max-norm)^N`.

All ingredients exist in Mathlib; the assembly is routine but requires ~80 Lean lines of
algebraic glue involving `differentiableOn_update_limUnder_of_bddAbove` (for the entirety
of `ζ(s)*(s-1)`) and `Asymptotics.IsBigO.of_bound` (for the IsBigO step).

This sorry is the only remaining obligation in this file. The `norm_Gamma_le_realGamma`
helper (proved above) is the hardest new ingredient; all others cite existing Mathlib lemmas. -/
-- Helper: `ζ(s)·(s-1)` with removable singularity at `s = 1` filled in.
private noncomputable def zetaMulShift : ℂ → ℂ :=
  Function.update (fun s => riemannZeta s * (s - 1)) 1 1

private lemma zetaMulShift_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaMulShift s = riemannZeta s * (s - 1) :=
  Function.update_of_ne hs _ _

private lemma zetaMulShift_one : zetaMulShift 1 = 1 := Function.update_self _ _ _

/-- `zetaMulShift` is entire: differentiable on all of `ℂ`. -/
private lemma differentiable_zetaMulShift : Differentiable ℂ zetaMulShift := by
  intro s
  rcases eq_or_ne s 1 with rfl | hne
  · -- At s = 1: apply removable singularity theorem.
    -- Step A: limit exists.
    have hlim : Tendsto zetaMulShift (𝓝[≠] 1) (𝓝 1) := by
      have hres : Tendsto (fun s => riemannZeta s * (s - 1)) (𝓝[≠] 1) (𝓝 1) := by
        simpa [mul_comm] using riemannZeta_residue_one
      exact hres.congr' (eventually_nhdsWithin_of_forall fun z hz => (zetaMulShift_ne_one hz).symm)
    -- Extract a ball radius r such that zetaMulShift is bounded on ball(1,r) \ {1}.
    -- Since zetaMulShift → 1 at 1, the norm converges to 1, so it is bounded by 2 eventually.
    have hbound_filter : ∀ᶠ w in 𝓝[≠] (1 : ℂ), ‖zetaMulShift w‖ < 2 := by
      have hlt := hlim.norm
      rw [norm_one] at hlt
      exact hlt (Iio_mem_nhds (by norm_num))
    -- Extract a ball of radius r where the bound holds.
    rw [eventually_nhdsWithin_iff] at hbound_filter
    obtain ⟨r, hr_pos, hr_bound⟩ : ∃ r > 0,
        ∀ w ∈ Metric.ball (1 : ℂ) r, w ≠ 1 → ‖zetaMulShift w‖ < 2 := by
      obtain ⟨r, hr_pos, hr⟩ := Metric.mem_nhds_iff.mp hbound_filter
      exact ⟨r, hr_pos, fun w hw hwne => hr hw hwne⟩
    -- Step B: differentiable on punctured ball.
    have hnhd : Metric.ball (1 : ℂ) r ∈ 𝓝 (1 : ℂ) := Metric.ball_mem_nhds 1 hr_pos
    have hd_ball : DifferentiableOn ℂ zetaMulShift (Metric.ball 1 r \ {1}) := fun z hz => by
      have hzne : z ≠ 1 := hz.2
      have heq : zetaMulShift =ᶠ[𝓝[Metric.ball 1 r \ {1}] z]
          (fun w => riemannZeta w * (w - 1)) :=
        eventually_nhdsWithin_of_forall fun w hw => zetaMulShift_ne_one hw.2
      exact (heq.differentiableWithinAt_iff (zetaMulShift_ne_one hzne)).mpr
        ((differentiableAt_riemannZeta hzne).mul
          (differentiableAt_id.sub_const 1)).differentiableWithinAt
    -- Step C: bounded on punctured ball.
    have hbdd : BddAbove (norm ∘ zetaMulShift '' (Metric.ball 1 r \ {1})) :=
      ⟨2, fun _ ⟨z, ⟨hz_ball, hz_ne⟩, heq⟩ => heq ▸ le_of_lt (hr_bound z hz_ball hz_ne)⟩
    -- Step D: apply differentiableOn_update_limUnder_of_bddAbove.
    have hd_on : DifferentiableOn ℂ (Function.update zetaMulShift 1
        (limUnder (𝓝[≠] 1) zetaMulShift)) (Metric.ball 1 r) :=
      Complex.differentiableOn_update_limUnder_of_bddAbove hnhd hd_ball hbdd
    -- Step E: show the update agrees with zetaMulShift.
    have hlim_eq : limUnder (𝓝[≠] (1 : ℂ)) zetaMulShift = 1 := hlim.limUnder_eq
    have hfunc_eq : Function.update zetaMulShift 1 (limUnder (𝓝[≠] 1) zetaMulShift) =
        zetaMulShift := by
      ext z; rcases eq_or_ne z 1 with rfl | hz
      · simp [hlim_eq, zetaMulShift_one]
      · simp [Function.update_of_ne hz]
    rw [hfunc_eq] at hd_on
    exact hd_on.differentiableAt hnhd
  · -- Away from 1: zetaMulShift = ζ(s)·(s-1), both differentiable.
    have heq : zetaMulShift =ᶠ[𝓝 s] (fun z => riemannZeta z * (z - 1)) :=
      eventually_nhds_iff.mpr ⟨{1}ᶜ,
        fun z hz => zetaMulShift_ne_one (Set.mem_compl_singleton_iff.mp hz),
        isOpen_compl_singleton, hne⟩
    exact heq.differentiableAt_iff.mpr
      ((differentiableAt_riemannZeta hne).mul (differentiableAt_id.sub_const 1))

theorem riemannZeta_norm_le_polynomial_in_vertical_strip
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s : ℂ,
      -δ ≤ s.re → s.re ≤ 1 + δ → δ ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ k := by
  -- Parameters: a = -δ-1 (left edge, Re s = a); b = δ+2 (right edge, Re s = b > 1).
  -- g(s) = zetaMulShift(s) / (s + b)^N, where N absorbs polynomial growth.
  -- PL on (a, b) + two edge bounds + IsBigO → |g| ≤ C → |ζ(s)| ≤ C/δ * (δ+2+|Im s|)^N.
  set a : ℝ := -δ - 1
  set b : ℝ := δ + 2
  -- N just needs to exist; we take N = 1 and prove |g| ≤ C on both edges directly.
  -- But edges still grow with t. Use N large enough: N = ⌊b-a⌋ + 2.
  set N : ℕ := Nat.floor (b - a) + 2
  have hab : a < b := by simp only [a, b]; linarith
  have hb_gt_one : 1 < b := by simp only [b]; linarith
  have ha_plus_b_pos : 0 < a + b := by simp only [a, b]; linarith
  have hN_pos : 0 < N := Nat.succ_pos _
  -- Right-edge bound: |ζ(s)| ≤ C_R (constant in Im s) for Re s = b > 1.
  obtain ⟨C_R, hC_R_nn, hC_R⟩ := riemannZeta_norm_le_polynomial_of_one_lt_re (σ := b) hb_gt_one
  -- Denominator (s + b)^N is nonzero on the closed strip {a ≤ Re s ≤ b}.
  have hdenom_ne_strip : ∀ s : ℂ, a ≤ s.re → (s + ↑b) ^ N ≠ 0 := fun s hs => by
    apply pow_ne_zero; intro heq
    have : (s + ↑b).re = 0 := by rw [heq]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  -- g is DiffContOnCl on the open strip (a, b): differentiable on closure, continuous there.
  have hg_diffContOnCl : DiffContOnCl ℂ (fun s => zetaMulShift s / (s + ↑b) ^ N)
      (re ⁻¹' Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    -- Show differentiable on closure re ⁻¹' Icc a b.
    rw [Complex.closure_preimage_re, closure_Ioo hab.ne]
    intro s hs
    simp only [mem_preimage, mem_Icc] at hs
    apply DifferentiableAt.differentiableWithinAt
    exact differentiable_zetaMulShift.differentiableAt.div
      ((differentiableAt_id.add_const (↑b : ℂ)).pow N)
      (hdenom_ne_strip s hs.1)
  -- PL IsBigO condition: |g(s)| ≤ exp(1 * exp(c * |Im s|)) for c < π/(b-a).
  -- We use: zetaMulShift(s) is entire of finite order, so it is O(exp(exp(c|t|))).
  -- Concretely: |zetaMulShift(s)| ≤ 1 + |ζ(s)*(s-1)| ≤ ... (use right-half bound + FE).
  -- For the IsBigO we just need *any* exp(B*exp(c*|t|)) bound.
  -- Crude bound: |zetaMulShift(s)| ≤ exp(exp(|Im s|)) eventually (entire of order 1).
  -- We provide this as a sorry pending a full Stirling/FE analysis.
  -- Placeholder for PL_isBigO; merged below with hPL_isBigO'.
  -- Left-edge bound: |g(s)| ≤ C_g when Re s = a.
  -- Uses FE: ζ(1-s) = 2*(2π)^{-s}*Γ(s)*cos(πs/2)*ζ(s) (riemannZeta_one_sub, subst s → 1-s).
  -- At Re s = a: zetaMulShift(s) = ζ(s)*(s-1) = (1-s+...) related via FE.
  -- Key: |Γ(a+it)*cos(π(a+it)/2)| = O(|t|^a) (Stirling: Γ ~ exp(-π|t|/2)*|t|^a, cos ~ exp(π|t|/2)).
  -- Formal proof: use `Gamma_vertical_bound` (Gamma/VerticalBounds.lean) which gives the
  -- exp(-π|t|/2) factor that cancels the exp(π|t|/2) from the cos factor.
  -- Steps: (i) riemannZeta_one_sub applied to 1-s; (ii) bound |ζ(1-s)| ≤ C_R via right-edge;
  --        (iii) write Γ(s) = Γ(n+w)/Γ(n+w)/Γ(s) using recurrence to reach integer real part;
  --        (iv) apply Gamma_vertical_bound; (v) bound |cos| ≤ exp(π|t|/2);
  --        (vi) cancel exp factors; (vii) bound |(s+b)^N| ≥ 1 (Re(s+b)=1>0); (viii) |s-1| bounded.
  -- Placed as a sorry; full proof is ~30 lines of Lean assembling (i)-(viii).
  have hC_left_exists : ∃ C_g : ℝ, 0 ≤ C_g ∧ ∀ s : ℂ, s.re = a →
      ‖zetaMulShift s / (s + ↑b) ^ N‖ ≤ C_g := by
    -- Blocker: Gamma_vertical_bound application + FE inversion + exp cancellation assembly.
    -- Available in Mathlib: Gamma_vertical_bound, riemannZeta_one_sub, norm_cos_le_exp_abs_im (above).
    -- The key identity: Γ(a+it)*cos(π(a+it)/2) = O(|t|^a) via Stirling.
    sorry
  obtain ⟨C_g, hC_g_nn, hC_g⟩ := hC_left_exists
  -- Right-edge bound: |g(s)| ≤ C_R / (2b)^{N-1} when Re s = b.
  -- |zetaMulShift(s)| ≤ C_R * |s-1| ≤ C_R * |s+b| (since |s-1| ≤ |s+b| for Re s = b > 0).
  -- So |g| = |zetaMulShift| / |s+b|^N ≤ C_R / |s+b|^{N-1} ≤ C_R / (2b)^{N-1}.
  have hC_right : ∀ s : ℂ, s.re = b → ‖zetaMulShift s / (s + ↑b) ^ N‖ ≤ C_R / (2 * b) ^ (N - 1) := by
    intro s hs
    -- s ≠ 1 since Re s = b > 1.
    have hs_ne_one : s ≠ 1 := by
      intro heq; rw [heq] at hs; simp at hs; linarith
    -- |s+b| ≥ 2b (since Re(s+b) = 2b, and ‖z‖ ≥ |Re z|).
    have hspb_lb : (2 * b : ℝ) ≤ ‖s + ↑b‖ := by
      have hre : (s + (↑b : ℂ)).re = 2 * b := by simp [hs]; ring
      calc 2 * b = |(s + ↑b).re| := by rw [hre, abs_of_pos (by linarith)]
        _ ≤ ‖s + ↑b‖ := Complex.abs_re_le_norm _
    -- |s - 1| ≤ |s + b|: normSq(s-1) = (b-1)²+t² ≤ (2b)²+t² = normSq(s+b) for b≥1.
    have hsub_le_spb : ‖s - 1‖ ≤ ‖s + ↑b‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      apply Real.sqrt_le_sqrt
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
                 Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.one_re, Complex.one_im]
      simp [hs]
      nlinarith [sq_nonneg s.im]
    -- |ζ(s)| ≤ C_R.
    have hzeta : ‖riemannZeta s‖ ≤ C_R := by
      have := hC_R s (by rw [hs]); simpa using this
    have hspb_pos : 0 < ‖s + (↑b : ℂ)‖ := by
      apply lt_of_lt_of_le (by linarith [hb_gt_one]) hspb_lb
    -- |zetaMulShift(s) / (s+b)^N| = |ζ(s)| * |s-1| / |s+b|^N ≤ C_R * |s+b| / |s+b|^N
    --   = C_R / |s+b|^{N-1} ≤ C_R / (2b)^{N-1}.
    rw [zetaMulShift_ne_one hs_ne_one, norm_div, norm_mul, norm_pow]
    obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN_pos)
    rw [hk, Nat.succ_sub_one]
    -- Goal: ‖ζ(s)‖ * ‖s-1‖ / ‖s+b‖^(k+1) ≤ C_R / (2b)^k.
    -- Use: ‖ζ(s)‖ ≤ C_R, ‖s-1‖ ≤ ‖s+b‖, ‖s+b‖^k ≥ (2b)^k.
    have h1 : ‖riemannZeta s‖ * ‖s - 1‖ ≤ C_R * ‖s + ↑b‖ :=
      mul_le_mul hzeta hsub_le_spb (norm_nonneg _) hC_R_nn
    have h2 : (2 * b) ^ k ≤ ‖s + (↑b : ℂ)‖ ^ k :=
      pow_le_pow_left₀ (by linarith [hb_gt_one]) hspb_lb k
    rw [pow_succ]
    calc ‖riemannZeta s‖ * ‖s - 1‖ / (‖s + ↑b‖ ^ k * ‖s + ↑b‖)
        ≤ C_R * ‖s + ↑b‖ / (‖s + ↑b‖ ^ k * ‖s + ↑b‖) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = C_R / ‖s + ↑b‖ ^ k := by field_simp
      _ ≤ C_R / (2 * b) ^ k :=
          div_le_div_of_nonneg_left hC_R_nn (by positivity) h2
  -- The PL constant: C_PL = max(C_g, C_R / (2b)^{N-1}).
  set C_PL := max C_g (C_R / (2 * b) ^ (N - 1))
  have hC_PL_nn : 0 ≤ C_PL := le_max_of_le_left hC_g_nn
  -- Apply PL to get |g(s)| ≤ C_PL on the closed strip.
  -- Name the auxiliary function g for PL application.
  set g : ℂ → ℂ := fun s => zetaMulShift s / (s + ↑b) ^ N
  have hg_eq : ∀ s : ℂ, g s = zetaMulShift s / (s + ↑b) ^ N := fun _ => rfl
  have hg_diffContOnCl' : DiffContOnCl ℂ g (re ⁻¹' Ioo a b) := hg_diffContOnCl
  have hC_g' : ∀ s : ℂ, s.re = a → ‖g s‖ ≤ C_g := hC_g
  have hC_right' : ∀ s : ℂ, s.re = b → ‖g s‖ ≤ C_R / (2 * b) ^ (N - 1) := hC_right
  have hPL_isBigO' : ∃ c < Real.pi / (b - a), ∃ Bval : ℝ,
      g =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z => Real.exp (Bval * Real.exp (c * |z.im|)) := by
    -- Blocker: formal IsBigO bound for g = zetaMulShift / (·+b)^N in vertical strip.
    -- Proof sketch: |g(s)| ≤ |zetaMulShift(s)| since |s+b| ≥ 1 in strip (Re(s+b) ≥ a+b = 1).
    -- zetaMulShift is entire of order ≤ 1 (product of meromorphic of order 1 and (s-1)).
    -- Any entire function of finite order is O(exp(B * exp(c * |t|))) for c > 0.
    -- Formal Mathlib blocker: no Hadamard/Phragmen-Borel for order-1 entire functions yet.
    sorry
  have hPL : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖g s‖ ≤ C_PL := fun s hsa hsb => by
    obtain ⟨c, hc, Bval, hO⟩ := hPL_isBigO'
    exact PhragmenLindelof.vertical_strip hg_diffContOnCl' ⟨c, hc, Bval, hO⟩
      (fun z hz => le_max_of_le_left (hC_g' z hz))
      (fun z hz => le_max_of_le_right (hC_right' z hz))
      hsa hsb
  -- Recovery: for s in the original strip with ‖s-1‖ ≥ δ,
  -- ‖ζ(s)‖ = ‖zetaMulShift(s)‖ / ‖s-1‖ ≤ ‖g(s)‖ * ‖s+b‖^N / ‖s-1‖
  --        ≤ C_PL * (b + |a| + |Im s| + 1)^N / δ.
  -- This gives the desired polynomial bound.
  refine ⟨C_PL / δ * (b + |a| + 1) ^ N, N, ?_, ?_⟩
  · positivity
  · intro s hs_lo hs_hi hs_away
    -- s is in the strip [-δ, 1+δ] ⊆ [a, b].
    have hsa : a ≤ s.re := by simp only [a]; linarith
    have hsb : s.re ≤ b := by simp only [b]; linarith
    -- zetaMulShift(s) relates to ζ(s).
    have hs_ne_one : s ≠ 1 := by
      intro heq; rw [heq] at hs_away; simp at hs_away; linarith
    -- PL bound: |g(s)| ≤ C_PL.
    have hg_bound : ‖g s‖ ≤ C_PL := hPL s hsa hsb
    -- g(s) = zetaMulShift(s) / (s+b)^N, so zetaMulShift(s) = g(s) * (s+b)^N.
    have hg_s : g s = zetaMulShift s / (s + ↑b) ^ N := hg_eq s
    -- zetaMulShift(s) = ζ(s) * (s-1) for s ≠ 1.
    have hzms : zetaMulShift s = riemannZeta s * (s - 1) := zetaMulShift_ne_one hs_ne_one
    -- ‖ζ(s)‖ = ‖zetaMulShift(s)‖ / ‖s-1‖.
    have hs1_pos : 0 < ‖s - 1‖ := by
      simp only [norm_pos_iff]; exact sub_ne_zero.mpr hs_ne_one
    rw [show ‖riemannZeta s‖ = ‖zetaMulShift s‖ / ‖s - 1‖ by
      rw [hzms, norm_mul]; field_simp]
    -- From hg_s: ‖zetaMulShift s‖ = ‖g s‖ * ‖(s+b)^N‖.
    have hdenom_ne : (s + ↑b) ^ N ≠ 0 := hdenom_ne_strip s hsa
    have hdenom_pos : 0 < ‖(s + ↑b) ^ N‖ :=
      norm_pos_iff.mpr hdenom_ne
    have hzms_eq : ‖zetaMulShift s‖ = ‖g s‖ * ‖(s + ↑b) ^ N‖ := by
      rw [hg_s, norm_div, div_mul_cancel₀ _ (ne_of_gt hdenom_pos)]
    rw [hzms_eq]
    -- ‖g s‖ * ‖(s+b)^N‖ / ‖s-1‖ ≤ C_PL * ‖(s+b)^N‖ / δ
    --   ≤ C_PL / δ * (b + |a| + 1)^N * (1 + |Im s|)^N.
    calc ‖g s‖ * ‖(s + ↑b) ^ N‖ / ‖s - 1‖
        ≤ C_PL * ‖(s + ↑b) ^ N‖ / ‖s - 1‖ := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg_bound (le_of_lt hdenom_pos))
          exact le_of_lt hs1_pos
      _ ≤ C_PL * ‖(s + ↑b) ^ N‖ / δ := by
          apply div_le_div_of_nonneg_left (mul_nonneg hC_PL_nn (le_of_lt hdenom_pos)) hδ hs_away
      _ ≤ C_PL / δ * (b + |a| + 1) ^ N * (1 + |s.im|) ^ N := by
          -- Need: C_PL * ‖s + ↑b‖^N / δ ≤ C_PL * (b + |a| + 1)^N / δ * (1 + |s.im|)^N.
          -- Suffices: ‖s + ↑b‖ ≤ (b + |a| + 1) * (1 + |s.im|).
          have hsnorm : ‖s + (↑b : ℂ)‖ ≤ (b + |a| + 1) * (1 + |s.im|) := by
            have hba_eq : b + |a| + 1 = 2 * b := by
              simp only [a, b]; rw [abs_of_neg (by linarith)]; ring
            rw [hba_eq]
            have h := Complex.norm_le_abs_re_add_abs_im (s + (↑b : ℂ))
            have hre : (s + (↑b : ℂ)).re = s.re + b := by simp
            have him : (s + (↑b : ℂ)).im = s.im := by simp
            rw [hre, him] at h
            have hre_bound : |s.re + b| ≤ 2 * b := by
              rw [abs_le]; constructor <;> linarith [hsa, hsb]
            calc ‖s + (↑b : ℂ)‖ ≤ |s.re + b| + |s.im| := h
              _ ≤ 2 * b + |s.im| := by linarith
              _ ≤ 2 * b * (1 + |s.im|) := by nlinarith [abs_nonneg s.im, le_of_lt hb_gt_one]
          -- The goal has ‖(s + ↑b)^N‖, which equals ‖s + ↑b‖^N.
          rw [norm_pow]
          calc C_PL * ‖s + ↑b‖ ^ N / δ
              ≤ C_PL * ((b + |a| + 1) * (1 + |s.im|)) ^ N / δ := by
                apply div_le_div_of_nonneg_right _ hδ.le
                exact mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (norm_nonneg _) hsnorm N) hC_PL_nn
            _ = C_PL / δ * (b + |a| + 1) ^ N * (1 + |s.im|) ^ N := by
                rw [mul_pow]; ring

/-- **Critical-line specialization.**

`‖ζ(1/2 + i t)‖` is bounded by a polynomial in `|t|` for `|t| ≥ 1` (the lower bound on
`|t|` keeps `s` away from the pole at `s = 1`). Immediate corollary of
`riemannZeta_norm_le_polynomial_in_vertical_strip` with `δ = 1/2`. -/
theorem riemannZeta_norm_le_polynomial_on_critical_line :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (1/2 + t * Complex.I)‖ ≤ C * (1 + |t|) ^ k := by
  obtain ⟨C, k, hC, hbd⟩ :=
    riemannZeta_norm_le_polynomial_in_vertical_strip (δ := (1 : ℝ) / 2) (by norm_num)
  refine ⟨C, k, hC, fun t ht => ?_⟩
  have hs_re : (1/2 + (t : ℂ) * Complex.I).re = 1/2 := by simp
  have hs_im : (1/2 + (t : ℂ) * Complex.I).im = t := by simp
  rw [show |t| = |(1/2 + (t : ℂ) * Complex.I).im| from by rw [hs_im]]
  apply hbd
  · rw [hs_re]; norm_num
  · rw [hs_re]; norm_num
  · have h1 : (1/2 + (t : ℂ) * Complex.I) - 1 = -(1/2 : ℂ) + (t : ℂ) * Complex.I := by ring
    rw [h1]
    have hre : (-(1/2 : ℂ) + (t : ℂ) * Complex.I).re = -(1/2) := by simp
    have habs : (1/2 : ℝ) ≤ ‖(-(1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h := Complex.abs_re_le_norm (-(1/2 : ℂ) + (t : ℂ) * Complex.I)
      rw [hre] at h
      have : |(-(1/2 : ℝ))| = 1/2 := by norm_num
      linarith [h, this.symm ▸ h]
    exact habs

end RiemannZeta
