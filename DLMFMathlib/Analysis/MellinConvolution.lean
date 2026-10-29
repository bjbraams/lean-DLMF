/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Convolution

/-!
# Mellin convolution via logarithmic coordinates

The change of variables `t = exp(-u)` converts the Mellin integrand to
`exp(-s*u) f(exp(-u))` and multiplicative convolution to ordinary convolution on the real line.
This proves both absolute convergence and the product formula for the Mellin transform.

The convergence adapter follows the change-of-variables argument in Mathlib's
`mellinInv_mellin_eq`. Evaluation reuses `mellin_eq_fourier`, and the convolution step uses
`MeasureTheory.integral_convolution` and `MeasureTheory.Integrable.integrable_convolution`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter
open scoped Topology FourierTransform

/-- The logarithmic substitution `t = exp(-u)` identifies absolute Mellin convergence with
integrability on the real line. -/
theorem mellinConvergent_iff_integrable_exp_mul (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun u : ℝ => cexp (-s * u) * f (Real.exp (-u))) := by
  have hd : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x := fun x _ => by
    simpa only [mul_neg_one] using
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt (s := univ)
  have him : (Real.exp ∘ Neg.neg) '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]
  have hinj : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← him,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj]
  simp only [IntegrableOn, Measure.restrict_univ, Function.comp_apply, abs_neg,
    abs_of_pos (Real.exp_pos _), smul_eq_mul]
  refine integrable_congr (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Complex.real_smul]
  simp only [ofReal_exp, ofReal_neg]
  rw [← mul_assoc]
  nth_rw 1 [← cpow_one (cexp (-(u : ℂ)))]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _)]
  rw [show (1 : ℂ) + (s - 1) = s by ring,
    cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
  · congr 1; ring
  · simp [Real.pi_pos]
  · simp [Real.pi_nonneg]

/-- Express the Mellin transform as an integral on the real line in logarithmic coordinates. -/
theorem mellin_eq_integral_exp_mul (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, cexp (-s * u) * f (Real.exp (-u)) := by
  rw [mellin_eq_fourier, Real.fourier_eq']
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul, Complex.real_smul]
  rw [ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  conv_rhs => rw [← re_add_im s]
  simp only [RCLike.inner_apply]
  push_cast
  field_simp
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- Logarithmic coordinates turn the multiplicative convolution kernel into ordinary convolution. -/
private lemma convolution_mellin_log_integrands (f g : ℝ → ℂ) (s : ℂ) (u : ℝ) :
    cexp (-s * u) * (∫ y in Ioi 0, f y * g (Real.exp (-u) / y) / y) =
      convolution (fun v : ℝ => cexp (-s * v) * f (Real.exp (-v)))
        (fun v : ℝ => cexp (-s * v) * g (Real.exp (-v)))
        (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  have hmel : mellin (fun y => f y * g (Real.exp (-u) / y)) 0 =
      (∫ y in Ioi 0, f y * g (Real.exp (-u) / y) / y) := by
    unfold mellin
    dsimp only
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [zero_sub, cpow_neg_one, smul_eq_mul]
    ring
  rw [← hmel, mellin_eq_integral_exp_mul]
  simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [← integral_const_mul, convolution]
  apply integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  have harg : Real.exp (-u) / Real.exp (-v) = Real.exp (-(u - v)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [harg]
  have he : cexp (-s * v) * cexp (-s * ((u - v : ℝ) : ℂ)) = cexp (-s * u) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc cexp (-s * u) * (f (Real.exp (-v)) * g (Real.exp (-(u - v)))) =
      (cexp (-s * v) * cexp (-s * ((u - v : ℝ) : ℂ))) *
        (f (Real.exp (-v)) * g (Real.exp (-(u - v)))) := by rw [he]
    _ = _ := by push_cast; ring

/-- The Mellin transform of multiplicative convolution is the product of the Mellin transforms, with
absolute convergence. -/
theorem hasMellin_integral_mul_div {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    HasMellin (fun x : ℝ => ∫ y in Ioi 0, f y * g (x / y) / y) s
      (mellin f s * mellin g s) := by
  have hfi := (mellinConvergent_iff_integrable_exp_mul f s).mp hf
  have hgi := (mellinConvergent_iff_integrable_exp_mul g s).mp hg
  have hfun := funext (convolution_mellin_log_integrands f g s)
  refine ⟨(mellinConvergent_iff_integrable_exp_mul _ _).mpr ?_, ?_⟩
  · rw [hfun]
    exact hfi.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hgi
  · rw [mellin_eq_integral_exp_mul, hfun,
      integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfi hgi]
    simp only [ContinuousLinearMap.mul_apply', ← mellin_eq_integral_exp_mul]

/-- Absolute Mellin convergence depends only on the real part of the exponent. -/
theorem MellinConvergent.of_re_eq {f : ℝ → ℂ} {s t : ℂ}
    (hf : MellinConvergent f s) (hst : t.re = s.re) : MellinConvergent f t := by
  have hm : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (t - s))
      (volume.restrict (Ioi 0)) :=
    (continuousOn_of_forall_continuousAt fun x hx =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).aestronglyMeasurable
        measurableSet_Ioi
  have hfi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hf
  have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (t - s) *
      ((x : ℂ) ^ (s - 1) * f x)) (Ioi 0) := hfi.bdd_mul
    (c := 1) hm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [sub_re, hst])
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (t - 1) * f x) (Ioi 0)
  refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
  dsimp only
  rw [← mul_assoc, ← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
  congr 2
  ring
