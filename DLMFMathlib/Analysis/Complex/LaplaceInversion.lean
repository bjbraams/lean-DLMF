/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.VerticalLineShift
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Bounds and contour shifts for inverse Laplace integrals

Rectangle Cauchy identities compare truncated vertical integrals without requiring absolute
convergence on the boundary lines. A quadratic majorant gives bounds for absolutely
convergent inverse Laplace remainders.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology Real

namespace Complex

/-- Truncated vertical integrals on two lines have difference tending to zero when their
horizontal connectors vanish. Absolute convergence on the vertical lines is not required. -/
theorem tendsto_integral_vertical_sub {f : ℂ → ℂ} {d c : ℝ} (hdc : d ≤ c)
    (hf : DifferentiableOn ℂ f (re ⁻¹' Icc d c))
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, f (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, f (x + T * I)) atBot (𝓝 0)) :
    Tendsto (fun T : ℝ => (∫ y in -T..T, f (c + y * I)) -
      ∫ y in -T..T, f (d + y * I)) atTop (𝓝 0) := by
  have he (T : ℝ) : (∫ y in -T..T, f (c + y * I)) -
      ∫ y in -T..T, f (d + y * I) =
      I * ((∫ x in d..c, f (x + (-T : ℝ) * I)) -
        ∫ x in d..c, f (x + T * I)) := by
    have hr := integral_boundary_rect_eq_zero_of_differentiableOn f
      ((d : ℂ) + (-T : ℝ) * I) ((c : ℂ) + T * I) (by
        refine hf.mono fun z hz => ?_
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero,
          ofReal_im, I_im, mul_one, sub_self, add_zero] at hz
        simpa [uIcc_of_le hdc] using hz.1)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add, smul_eq_mul] at hr
    calc (∫ y in -T..T, f (c + y * I)) - ∫ y in -T..T, f (d + y * I) =
        -I * (I * ((∫ y in -T..T, f (c + y * I)) -
          ∫ y in -T..T, f (d + y * I))) := by rw [← mul_assoc]; simp
      _ = _ := by linear_combination -I * hr
  simpa only [he, sub_zero, mul_zero, Function.comp_def] using
    ((hbot.comp tendsto_neg_atTop_atBot).sub htop).const_mul I

/-- The integral of the quadratic vertical majorant. -/
theorem integral_inv_sq_add_sq {σ : ℝ} (hσ : 0 < σ) :
    (∫ y : ℝ, (σ ^ 2 + y ^ 2)⁻¹) = Real.pi / σ := by
  have he : (fun y : ℝ => (σ ^ 2 + y ^ 2)⁻¹) =
      (fun y => (σ ^ 2)⁻¹ * (1 + (σ⁻¹ * y) ^ 2)⁻¹) := by
    funext y
    field_simp
  rw [he, integral_const_mul, integral_univ_inv_one_add_mul_sq,
    abs_inv, abs_of_pos hσ]
  field_simp

/-- A quadratic vertical bound gives absolute integrability of the inverse Laplace kernel
and a bound for its full line integral. -/
theorem integrable_exp_mul_vertical_of_norm_le {R : ℂ → ℂ} {σ C t : ℝ}
    (hσ : 0 < σ) (hR : Continuous fun y : ℝ => R (σ + y * I))
    (hb : ∀ y : ℝ, ‖R (σ + y * I)‖ ≤ C * (σ ^ 2 + y ^ 2)⁻¹) :
    Integrable (fun y : ℝ => exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)) ∧
      ‖∫ y : ℝ, exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)‖ ≤
        Real.exp (t * σ) * C * (Real.pi / σ) := by
  have hi : Integrable (fun y : ℝ =>
      Real.exp (t * σ) * C * (σ ^ 2 + y ^ 2)⁻¹) := by
    simpa using (integrable_inv_sq_add_sub_sq hσ.ne' 0).const_mul (Real.exp (t * σ) * C)
  have hb' (y : ℝ) : ‖exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)‖ ≤
      Real.exp (t * σ) * C * (σ ^ 2 + y ^ 2)⁻¹ := by
    rw [norm_mul, norm_exp]
    simp only [mul_re, ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, zero_mul, sub_zero]
    exact (mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos _).le).trans_eq (by ring)
  refine ⟨hi.mono' ((by fun_prop : Continuous fun y : ℝ =>
    exp ((t : ℂ) * (σ + y * I))).mul hR).aestronglyMeasurable
      (Eventually.of_forall hb'), ?_⟩
  have h := norm_integral_le_of_norm_le hi (Eventually.of_forall hb')
  simpa only [integral_const_mul, integral_inv_sq_add_sq hσ] using h

/-- Polynomial decay on a half-plane makes the horizontal connectors of an inverse Laplace
integral vanish at either end of the imaginary axis. -/
theorem tendsto_integral_horizontal_exp_mul_of_norm_le {R : ℂ → ℂ}
    {c d e C K a t : ℝ} (hcd : c ≤ d) (hde : d ≤ e) (hC : 0 ≤ C) (ha : 0 < a)
    (ht : 0 ≤ t) (hb : ∀ z : ℂ, c ≤ z.re → K ≤ ‖z‖ → ‖R z‖ ≤ C * ‖z‖ ^ (-a))
    {l : Filter ℝ} (hl : Tendsto (fun T : ℝ => |T|) l atTop) :
    Tendsto (fun T : ℝ => ∫ x in d..e,
      exp ((t : ℂ) * (x + T * I)) * R (x + T * I)) l (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ =>
      (e - d) * (Real.exp (t * e) * C * |T| ^ (-a))) l (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop ha).comp hl).const_mul
      (Real.exp (t * e) * C)).const_mul (e - d)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hl.eventually_ge_atTop K, hl.eventually_gt_atTop 0] with T hTK hT0
  have hb' (x : ℝ) (hx : x ∈ uIoc d e) :
      ‖exp ((t : ℂ) * (x + T * I)) * R (x + T * I)‖ ≤
        Real.exp (t * e) * C * |T| ^ (-a) := by
    rw [uIoc_of_le hde] at hx
    have hxre : ((x : ℂ) + T * I).re = x := by simp
    have hTim : |T| ≤ ‖(x : ℂ) + T * I‖ := by
      simpa using abs_im_le_norm ((x : ℂ) + T * I)
    have hnorm := hb (x + T * I) (by simpa using hcd.trans hx.1.le) (hTK.trans hTim)
    rw [norm_mul, norm_exp]
    simp only [mul_re, ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, zero_mul, sub_zero]
    calc Real.exp (t * x) * ‖R (x + T * I)‖ ≤
        Real.exp (t * e) * (C * ‖(x : ℂ) + T * I‖ ^ (-a)) :=
          mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 ht)) hnorm
            (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (t * e) * (C * |T| ^ (-a)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hT0 hTim (neg_nonpos.mpr ha.le)) hC)
            (Real.exp_pos _).le
      _ = _ := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb'
  simpa only [abs_of_nonneg (sub_nonneg.mpr hde), mul_comm] using h

/-- On a positive vertical line, a power bound of order at least two has a quadratic
integrable majorant, with the correct scaling in the line's real part. -/
theorem norm_rpow_neg_le_vertical_quadratic {σ a : ℝ} (hσ : 0 < σ) (ha : 2 ≤ a)
    (y : ℝ) :
    ‖(σ : ℂ) + y * I‖ ^ (-a) ≤ σ ^ (2 - a) * (σ ^ 2 + y ^ 2)⁻¹ := by
  have hn : σ ≤ ‖(σ : ℂ) + y * I‖ := by
    simpa only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, abs_of_pos hσ] using
      abs_re_le_norm ((σ : ℂ) + y * I)
  have hn0 : 0 < ‖(σ : ℂ) + y * I‖ := hσ.trans_le hn
  have he : ‖(σ : ℂ) + y * I‖ ^ (-a) =
      ‖(σ : ℂ) + y * I‖ ^ (2 - a) * ‖(σ : ℂ) + y * I‖ ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [he, Real.rpow_neg (norm_nonneg _), Real.rpow_two]
  have hsq := norm_add_mul_I_sub_sq σ y 0
  simp only [sub_zero, zero_re, zero_im] at hsq
  rw [hsq]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hσ hn (by linarith)) (by positivity)

/-- A vertical power of order greater than one is integrable. Its integral scales as
`σ^(1-a)` on the line with positive real part `σ`. -/
theorem integrable_norm_vertical_rpow {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ) :
    Integrable (fun y : ℝ => ‖(σ : ℂ) + y * I‖ ^ (-a)) ∧
      (∫ y : ℝ, ‖(σ : ℂ) + y * I‖ ^ (-a)) =
        σ ^ (1 - a) * ∫ y : ℝ, ‖(1 : ℂ) + y * I‖ ^ (-a) := by
  have he (y : ℝ) : ‖(1 : ℂ) + y * I‖ ^ (-a) = (1 + ‖y‖ ^ 2) ^ (-a / 2) := by
    have hn : 0 ≤ ‖(1 : ℂ) + y * I‖ := norm_nonneg _
    have hs := norm_add_mul_I_sub_sq 1 y 0
    simp only [sub_zero, zero_re, zero_im, ofReal_one, one_pow, Real.norm_eq_abs, sq_abs] at hs ⊢
    rw [← hs, ← Real.rpow_two, ← Real.rpow_mul hn]
    congr 1
    ring
  have hi : Integrable (fun y : ℝ => ‖(1 : ℂ) + y * I‖ ^ (-a)) := by
    simp_rw [he]
    exact integrable_rpow_neg_one_add_norm_sq (by simpa using ha)
  have hs (y : ℝ) : ‖(σ : ℂ) + y * I‖ ^ (-a) =
      σ ^ (-a) * ‖(1 : ℂ) + (y / σ) * I‖ ^ (-a) := by
    have hz : (σ : ℂ) + y * I = (σ : ℂ) * (1 + (y / σ : ℝ) * I) := by
      push_cast
      field_simp [hσ.ne']
      <;> ring
    rw [hz, norm_mul, norm_real, Real.norm_of_nonneg hσ.le,
      Real.mul_rpow hσ.le (norm_nonneg _)]
    simp only [ofReal_div]
  have hf : (fun y : ℝ => ‖(σ : ℂ) + y * I‖ ^ (-a)) =
      (fun y : ℝ => σ ^ (-a) * ‖(1 : ℂ) + (y / σ) * I‖ ^ (-a)) := funext hs
  rw [hf]
  constructor
  · simpa only [ofReal_div] using (hi.comp_div hσ.ne').const_mul (σ ^ (-a))
  have hscale := Measure.integral_comp_div
    (fun y : ℝ => ‖(1 : ℂ) + y * I‖ ^ (-a)) σ
  simp only [ofReal_div, abs_of_pos hσ, smul_eq_mul] at hscale
  rw [integral_const_mul, hscale]
  have hp : σ ^ (-a) * σ = σ ^ (1 - a) := by
    calc σ ^ (-a) * σ = σ ^ (-a) * σ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hσ]; congr 1; ring
  rw [← mul_assoc, hp]

/-- A power bound of order greater than one gives absolute integrability and the scaled
bound for an inverse Laplace integral on a positive vertical line. -/
theorem integrable_exp_mul_vertical_of_norm_le_rpow {R : ℂ → ℂ} {σ C t a : ℝ}
    (hσ : 0 < σ) (ha : 1 < a) (hR : Continuous fun y : ℝ => R (σ + y * I))
    (hb : ∀ y : ℝ, ‖R (σ + y * I)‖ ≤ C * ‖(σ : ℂ) + y * I‖ ^ (-a)) :
    Integrable (fun y : ℝ => exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)) ∧
      ‖∫ y : ℝ, exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)‖ ≤
        Real.exp (t * σ) * C * σ ^ (1 - a) *
          ∫ y : ℝ, ‖(1 : ℂ) + y * I‖ ^ (-a) := by
  have hi := (integrable_norm_vertical_rpow ha hσ).1.const_mul (Real.exp (t * σ) * C)
  have hb' (y : ℝ) : ‖exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)‖ ≤
      Real.exp (t * σ) * C * ‖(σ : ℂ) + y * I‖ ^ (-a) := by
    rw [norm_mul, norm_exp]
    simp only [mul_re, ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, zero_mul, sub_zero]
    exact (mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos _).le).trans_eq (by ring)
  refine ⟨hi.mono' ((by fun_prop : Continuous fun y : ℝ =>
    exp ((t : ℂ) * (σ + y * I))).mul hR).aestronglyMeasurable
      (Eventually.of_forall hb'), ?_⟩
  have h := norm_integral_le_of_norm_le hi (Eventually.of_forall hb')
  simpa only [integral_const_mul, (integrable_norm_vertical_rpow ha hσ).2,
    mul_assoc] using h

/-- A holomorphic function with uniform power decay of order greater than one on a positive
half-plane has an inverse Laplace integral, independent of the vertical line. Its inverse
is `O(t^(a-1))` at zero. Only a bound outside a fixed disc is required. -/
theorem exists_inverseLaplace_of_norm_le_rpow {R : ℂ → ℂ} {c C K a : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (ha : 1 < a)
    (hR : DifferentiableOn ℂ R {z | c ≤ z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → K ≤ ‖z‖ → ‖R z‖ ≤ C * ‖z‖ ^ (-a)) :
    ∃ q : ℝ → ℂ, (∀ σ : ℝ, c ≤ σ → ∀ t : ℝ, 0 < t →
      Tendsto (fun T : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
        ∫ y in -T..T, exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)) atTop (𝓝 (q t))) ∧
      q =O[𝓝[>] 0] (fun t : ℝ => t ^ (a - 1)) := by
  let S := max c (max K 1)
  have hcS : c ≤ S := le_max_left _ _
  have hKS : K ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hS : 0 < S := hc.trans_le hcS
  let A : ℂ := (2 * (Real.pi : ℂ))⁻¹
  let J : ℝ → ℝ → ℝ → ℂ := fun σ t T => A *
    ∫ y in -T..T, exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)
  let q : ℝ → ℂ := fun t => A *
    ∫ y : ℝ, exp ((t : ℂ) * (S + y * I)) * R (S + y * I)
  have hlarge (σ : ℝ) (hσ : S ≤ σ) (t : ℝ) :
      Integrable (fun y : ℝ => exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)) ∧
        ‖∫ y : ℝ, exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)‖ ≤
          Real.exp (t * σ) * C * σ ^ (1 - a) *
            ∫ y : ℝ, ‖(1 : ℂ) + y * I‖ ^ (-a) := by
    have hσ0 : 0 < σ := hS.trans_le hσ
    apply integrable_exp_mul_vertical_of_norm_le_rpow hσ0 ha
      (hR.continuousOn.comp_continuous (by fun_prop) fun y => by
        simpa using hcS.trans hσ)
    intro y
    have hn : σ ≤ ‖(σ : ℂ) + y * I‖ := by
      simpa [abs_of_pos hσ0] using abs_re_le_norm ((σ : ℂ) + y * I)
    exact hb _ (by simpa using hcS.trans hσ) (hKS.trans (hσ.trans hn))
  have hsame (d e : ℝ) (hd : c ≤ d) (he : c ≤ e) (t : ℝ) (ht : 0 < t) :
      Tendsto (fun T => J e t T - J d t T) atTop (𝓝 0) := by
    have hordered (d e : ℝ) (hd : c ≤ d) (hde : d ≤ e) :
        Tendsto (fun T => J e t T - J d t T) atTop (𝓝 0) := by
      have hdif : DifferentiableOn ℂ (fun z => exp ((t : ℂ) * z) * R z)
          (re ⁻¹' Icc d e) :=
        (differentiable_id.const_mul (t : ℂ)).cexp.differentiableOn.mul
          (hR.mono fun z hz => hd.trans hz.1)
      have ht' := tendsto_integral_horizontal_exp_mul_of_norm_le hd hde hC
        (by linarith : 0 < a) ht.le hb tendsto_abs_atTop_atTop
      have hb' := tendsto_integral_horizontal_exp_mul_of_norm_le hd hde hC
        (by linarith : 0 < a) ht.le hb tendsto_abs_atBot_atTop
      simpa only [J, ← mul_sub, mul_zero] using
        (tendsto_integral_vertical_sub hde hdif ht' hb').const_mul A
    rcases le_total d e with hde | hed
    · exact hordered d e hd hde
    · simpa only [neg_sub, neg_zero] using (hordered e d he hed).neg
  have hspec (σ : ℝ) (hσ : c ≤ σ) (t : ℝ) (ht : 0 < t) :
      Tendsto (J σ t) atTop (𝓝 (q t)) := by
    have hbase := (intervalIntegral_tendsto_integral (hlarge S le_rfl t).1
      tendsto_neg_atTop_atBot tendsto_id).const_mul A
    have h := hbase.add (hsame S σ hcS hσ t ht)
    simp only [add_zero] at h
    convert h using 1
    funext T
    dsimp [J]
    ring
  refine ⟨q, hspec, IsBigO.of_bound (‖A‖ * Real.exp 1 * C *
    ∫ y : ℝ, ‖(1 : ℂ) + y * I‖ ^ (-a)) ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    tendsto_inv_nhdsGT_zero.eventually_ge_atTop S] with t ht hSt
  have hqt : q t = A * ∫ y : ℝ,
      exp ((t : ℂ) * (t⁻¹ + y * I)) * R (t⁻¹ + y * I) :=
    tendsto_nhds_unique (hspec t⁻¹ (hcS.trans hSt) t ht)
      ((intervalIntegral_tendsto_integral (hlarge t⁻¹ hSt t).1
        tendsto_neg_atTop_atBot tendsto_id).const_mul A)
  rw [hqt, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  have hp : (t⁻¹) ^ (1 - a) = t ^ (a - 1) := by
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_sub]
  calc ‖A‖ * ‖∫ y : ℝ, exp ((t : ℂ) * (t⁻¹ + y * I)) * R (t⁻¹ + y * I)‖ ≤
      ‖A‖ * (Real.exp (t * t⁻¹) * C * (t⁻¹) ^ (1 - a) *
        ∫ y : ℝ, ‖(1 : ℂ) + y * I‖ ^ (-a)) :=
        mul_le_mul_of_nonneg_left (hlarge t⁻¹ hSt t).2 (norm_nonneg _)
    _ = (‖A‖ * Real.exp 1 * C * ∫ y : ℝ, ‖(1 : ℂ) + y * I‖ ^ (-a)) *
        t ^ (a - 1) := by
      rw [mul_inv_cancel₀ ht.ne', hp]
      ring

/-- A power-decaying function on a positive half-plane tends to zero on each vertical line,
even after multiplication by the inverse Laplace exponential. -/
theorem tendsto_exp_mul_vertical_of_norm_le_rpow {R : ℂ → ℂ} {c σ C K a t : ℝ}
    (hσ : c ≤ σ) (hC : 0 ≤ C) (ha : 0 < a)
    (hb : ∀ z : ℂ, c ≤ z.re → K ≤ ‖z‖ → ‖R z‖ ≤ C * ‖z‖ ^ (-a)) :
    Tendsto (fun y : ℝ => exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I))
      (cocompact ℝ) (𝓝 0) := by
  have hnorm : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    simpa only [Real.norm_eq_abs] using
      (show Tendsto (fun y : ℝ => ‖y‖) (cocompact ℝ) atTop from
        tendsto_norm_cocompact_atTop)
  have ht := ((tendsto_rpow_neg_atTop ha).comp hnorm).const_mul
    (Real.exp (t * σ) * C)
  simp only [mul_zero] at ht
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [hnorm.eventually_ge_atTop K, hnorm.eventually_gt_atTop 0] with y hy hy0
  have hn : |y| ≤ ‖(σ : ℂ) + y * I‖ := by
    simpa using abs_im_le_norm ((σ : ℂ) + y * I)
  rw [norm_mul, norm_exp]
  simp only [mul_re, ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, zero_mul, sub_zero]
  calc Real.exp (t * σ) * ‖R (σ + y * I)‖ ≤
      Real.exp (t * σ) * (C * ‖(σ : ℂ) + y * I‖ ^ (-a)) := by
        gcongr
        exact hb _ (by simpa using hσ) (hy.trans hn)
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr
      exact Real.rpow_le_rpow_of_nonpos hy0 hn (by linarith)

/-- Integration by parts transfers a convergent inverse Laplace integral of the derivative
to the original function, provided its boundary values tend to zero. -/
theorem tendsto_integral_exp_mul_vertical_of_deriv {R : ℂ → ℂ} {σ t : ℝ} {L : ℂ}
    (ht : 0 < t) (hR : ∀ y : ℝ, AnalyticAt ℂ R (σ + y * I))
    (hzero : Tendsto (fun y : ℝ => exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I))
      (cocompact ℝ) (𝓝 0))
    (hlim : Tendsto (fun T : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
      ∫ y in -T..T, exp ((t : ℂ) * (σ + y * I)) * deriv R (σ + y * I))
      atTop (𝓝 L)) :
    Tendsto (fun T : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
      ∫ y in -T..T, exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I))
      atTop (𝓝 (-L / t)) := by
  let u : ℝ → ℂ := fun y => exp ((t : ℂ) * (σ + y * I))
  let v : ℝ → ℂ := fun y => R (σ + y * I)
  have hu (y : ℝ) : HasDerivAt u ((t : ℂ) * I * u y) y := by
    simpa only [u, mul_assoc, mul_comm, mul_left_comm, one_mul, mul_one, id_eq,
      ofRealCLM_apply, ofReal_one] using!
      (((ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (σ : ℂ)).const_mul (t : ℂ) |>.cexp
  have hv (y : ℝ) : HasDerivAt v (I * deriv R (σ + y * I)) y := by
    simpa only [v, mul_comm, Function.comp_def, mul_one, one_mul, id_eq] using!
      (((hR y).differentiableAt.hasDerivAt.comp (y : ℂ)
        (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (σ : ℂ))).comp_ofReal)
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun y => (hu y).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun y => (hv y).continuousAt
  have hdc : Continuous (fun y : ℝ => deriv R (σ + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact ContinuousAt.comp (g := deriv R) (f := fun y : ℝ => (σ : ℂ) + y * I)
      ((hR y).deriv.continuousAt) (by fun_prop)
  have he (T : ℝ) : (2 * (Real.pi : ℂ))⁻¹ * ∫ y in -T..T, u y * v y =
      ((2 * (Real.pi : ℂ))⁻¹ * (u T * v T - u (-T) * v (-T)) / I -
        (2 * (Real.pi : ℂ))⁻¹ * ∫ y in -T..T, u y * deriv R (σ + y * I)) / t := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := -T) (b := T)
      huc.continuousOn hvc.continuousOn (fun y _ => hu y) (fun y _ => hv y)
      (((continuous_const.mul continuous_const).mul huc).intervalIntegrable _ _)
      ((continuous_const.mul hdc).intervalIntegrable _ _)
    have he₁ : (fun y : ℝ => u y * (I * deriv R (σ + y * I))) =
        (fun y : ℝ => I * (u y * deriv R (σ + y * I))) := by funext y; ring
    have he₂ : (fun y : ℝ => (t : ℂ) * I * u y * v y) =
        (fun y : ℝ => ((t : ℂ) * I) * (u y * v y)) := by funext y; ring
    rw [he₁, he₂, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    apply (eq_div_iff htc).mpr
    rw [div_eq_mul_inv, inv_I]
    linear_combination (norm := ring_nf) -(2 * (Real.pi : ℂ))⁻¹ * I * h
    simp [I_sq]
  have hb := (hzero.mono_left atTop_le_cocompact).sub
    ((hzero.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot)
  have h := (((hb.const_mul (2 * (Real.pi : ℂ))⁻¹).div_const I).sub hlim).div_const (t : ℂ)
  simpa only [sub_self, mul_zero, zero_div, zero_sub, he, u, v, Function.comp_def] using h

/-- Holomorphy, power decay of positive order, and a differentiated power bound imply an
inverse Laplace remainder of order `t^(a-1)`, without an unbounded exponent sequence. -/
theorem exists_inverseLaplace_of_deriv_norm_le_rpow {R : ℂ → ℂ} {c C D K a : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : 0 < a)
    (hR : AnalyticOnNhd ℂ R {z | c ≤ z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → K ≤ ‖z‖ → ‖R z‖ ≤ C * ‖z‖ ^ (-a))
    (hbd : ∀ z : ℂ, c ≤ z.re → K ≤ ‖z‖ → ‖deriv R z‖ ≤ D * ‖z‖ ^ (-(a + 1))) :
    ∃ q : ℝ → ℂ, (∀ σ : ℝ, c ≤ σ → ∀ t : ℝ, 0 < t →
      Tendsto (fun T : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
        ∫ y in -T..T, exp ((t : ℂ) * (σ + y * I)) * R (σ + y * I)) atTop (𝓝 (q t))) ∧
      q =O[𝓝[>] 0] (fun t : ℝ => t ^ (a - 1)) := by
  obtain ⟨qD, hqD, hbD⟩ := exists_inverseLaplace_of_norm_le_rpow hc hD
    (by linarith : 1 < a + 1) hR.deriv.differentiableOn hbd
  let q : ℝ → ℂ := fun t => -qD t / t
  refine ⟨q, fun σ hσ t ht => ?_, ?_⟩
  · exact tendsto_integral_exp_mul_vertical_of_deriv ht
      (fun y => hR _ (by simpa using hσ))
      (tendsto_exp_mul_vertical_of_norm_le_rpow hσ hC ha hb) (hqD σ hσ t ht)
  · obtain ⟨B, hB, hbound⟩ := hbD.exists_pos
    refine IsBigO.of_bound B ?_
    filter_upwards [self_mem_nhdsWithin, hbound.bound] with t ht hbt
    dsimp only [q]
    rw [norm_div, norm_neg, norm_real, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    simp only [add_sub_cancel_right] at hbt
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)] at hbt
    calc ‖qD t‖ / t ≤ B * t ^ a / t := div_le_div_of_nonneg_right hbt ht.le
      _ = _ := by rw [Real.rpow_sub_one ht.ne']; ring

end Complex
