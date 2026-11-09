/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import DLMFMathlib.Analysis.Integral.LaplaceConvergence

/-!
# Uniform Mellin bounds for a high tail

For a function supported in `(1,∞)`, absolute Mellin convergence on one vertical line
bounds its Mellin transform throughout the half-plane to the left.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Filter
open scoped Topology Real

/-- A high-tail Mellin transform is bounded uniformly to the left of a line of absolute
convergence by its weighted absolute integral on that line. -/
theorem norm_mellin_le_of_support_gt_one {g : ℝ → ℂ} {b : ℝ}
    (hg : ∀ t : ℝ, t ≤ 1 → g t = 0) (hi : MellinConvergent g b)
    {z : ℂ} (hz : z.re ≤ b) :
    ‖mellin g z‖ ≤ ∫ t in Ioi 0, t ^ (b - 1) * ‖g t‖ := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (b - 1) * ‖g t‖) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.norm hi) (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    simp
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hint ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
  by_cases h1 : t ≤ 1
  · simp [hg t h1]
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (not_le.mp h1).le (by simp; linarith)) (norm_nonneg _)

/-- An absolutely Mellin-convergent high tail has an absolutely convergent Laplace integral
for every positive decay parameter. -/
theorem integrableOn_exp_neg_mul_of_mellinConvergent {g : ℝ → ℂ} {p ζ : ℝ}
    (hg : ∀ t : ℝ, t ≤ 1 → g t = 0) (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hi : MellinConvergent g p) (hζ : 0 < ζ) :
    IntegrableOn (fun t : ℝ => (Real.exp (-ζ * t) : ℂ) * g t) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_rpow_mul_exp_neg_le' (1 - p) hζ
  have hi' : IntegrableOn (fun t : ℝ => t ^ (p - 1) * ‖g t‖) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.norm hi) (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    simp
  refine (hi'.const_mul C).mono'
    ((by fun_prop : Continuous fun t : ℝ => (Real.exp (-ζ * t) : ℂ)).aestronglyMeasurable.mul
      hgm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp]
  by_cases ht1 : t ≤ 1
  · simp [hg t ht1]
  · have he : t ^ (p - 1) * t ^ (1 - p) = 1 := by
      rw [← Real.rpow_add ht]
      simp
    calc Real.exp (-ζ * t) * ‖g t‖ =
        (t ^ (1 - p) * Real.exp (-ζ * t)) * (t ^ (p - 1) * ‖g t‖) := by
          linear_combination -(Real.exp (-ζ * t) * ‖g t‖) * he
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb t (not_le.mp ht1).le)
        (mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))

/-- The exponential Mellin convolution of a high tail is continuous at every positive
dilation parameter. Absolute Mellin convergence on one line suffices. -/
theorem continuousAt_integral_exp_neg_mul_dilate_of_mellinConvergent
    {g : ℝ → ℂ} {p x : ℝ} (hx : 0 < x) (hg : ∀ t : ℝ, t ≤ 1 → g t = 0)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0))) (hi : MellinConvergent g p) :
    ContinuousAt (fun x : ℝ => ∫ t in Ioi 0, (Real.exp (-t) : ℂ) * g (x * t)) x := by
  let F : ℂ → ℂ := fun z => ∫ t in Ioi (0 : ℝ), exp (-(z * t)) * g t
  have hic : IntegrableOn (fun t => Real.exp (-(x⁻¹ / 2) * t) • g t) (Ioi 0) := by
    simpa only [real_smul] using integrableOn_exp_neg_mul_of_mellinConvergent hg hgm hi
      (half_pos (inv_pos.mpr hx))
  have hd : DifferentiableAt ℂ F (x⁻¹ : ℝ) := by
    have h := (differentiableOn_integral_cexp_neg_mul_smul hic).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show x⁻¹ / 2 < ((x⁻¹ : ℝ) : ℂ).re by simp; positivity))
    simpa only [F, smul_eq_mul] using h
  have hc : ContinuousAt (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ) * F (y⁻¹ : ℝ)) x := by
    have hi' : ContinuousAt (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) x :=
      continuous_ofReal.continuousAt.comp (continuousAt_inv₀ hx.ne')
    exact hi'.mul (ContinuousAt.comp (g := F) (f := fun y : ℝ => ((y⁻¹ : ℝ) : ℂ))
      hd.continuousAt hi')
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  have he : (fun t : ℝ => (Real.exp (-t) : ℂ) * g (y * t)) =
      (fun t : ℝ => exp (-(((y⁻¹ : ℝ) : ℂ) * t)) * g t) ∘ (fun t : ℝ => y * t) := by
    funext t
    dsimp only [Function.comp_def]
    rw [ofReal_mul, ← mul_assoc, ← ofReal_mul, inv_mul_cancel₀ hy.ne']
    simp [ofReal_exp]
  rw [he]
  simp only [Function.comp_def]
  simpa only [mul_zero, real_smul, F] using integral_comp_mul_left_Ioi
    (fun t : ℝ => exp (-(((y⁻¹ : ℝ) : ℂ) * t)) * g t) 0 hy
