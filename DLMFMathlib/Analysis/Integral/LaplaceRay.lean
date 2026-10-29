/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating exponential kernels along a horizontal ray

The identity follows from Mathlib's Fubini theorem after proving absolute
integrability using the weighted quotient `exp(-st) f(t)/t`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set

namespace Complex

/-- Along a positive horizontal ray the exponential kernel has integral
`exp(-st)/t`, including its full complex phase. -/
lemma integral_Ioi_cexp_add_mul {s : ℂ} {t : ℝ} (ht : 0 < t) (c : ℂ) :
    IntegrableOn (fun v : ℝ => cexp (-(s + v) * t) * c) (Ioi 0) ∧
      (∫ v in Ioi (0 : ℝ), cexp (-(s + v) * t) * c) = cexp (-s * t) * (c / t) := by
  have he (v : ℝ) : cexp (-(s + v) * t) * c =
      cexp (-(t : ℂ) * v) * (cexp (-s * t) * c) := by
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [he]
  have ht' : (-(t : ℂ)).re < 0 := by simp; linarith
  refine ⟨(integrableOn_exp_mul_complex_Ioi ht' 0).mul_const _, ?_⟩
  rw [integral_mul_const, integral_exp_mul_complex_Ioi ht' 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg]
  ring

/-- The integral of the norm along a horizontal ray equals the norm of the
weighted quotient, since the ray contributes a positive real exponential. -/
lemma integral_Ioi_norm_cexp_add_mul {s : ℂ} {t : ℝ} (ht : 0 < t) (c : ℂ) :
    (∫ v in Ioi (0 : ℝ), ‖cexp (-(s + v) * t) * c‖) = ‖cexp (-s * t) * (c / t)‖ := by
  have he (v : ℝ) : ‖cexp (-(s + v) * t) * c‖ =
      Real.exp (-t * v) * (Real.exp (-s.re * t) * ‖c‖) := by
    rw [norm_mul, norm_exp, ← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [neg_re, mul_re, add_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    ring
  simp_rw [he]
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos ht) 0]
  simp only [mul_zero, Real.exp_zero, div_neg, norm_mul, norm_exp,
    norm_div, norm_real, Real.norm_eq_abs, abs_of_pos ht, neg_re, mul_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

/-- Absolute convergence of the weighted quotient justifies exchanging the
positive ray and half-line exponential integrals. -/
theorem integral_Ioi_integral_cexp_add_mul {f : ℝ → ℂ} {s : ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hint : IntegrableOn (fun t : ℝ => cexp (-s * t) * (f t / t)) (Ioi 0)) :
    (∫ v in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), cexp (-(s + v) * t) * f t) =
      ∫ t in Ioi (0 : ℝ), cexp (-s * t) * (f t / t) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let Φ : ℝ × ℝ → ℂ := fun p => cexp (-(s + p.2) * p.1) * f p.1
  have hm : AEStronglyMeasurable Φ (μ.prod μ) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (-(s + p.2) * p.1)).aestronglyMeasurable.mul
      hfm.comp_fst
  have hi : Integrable Φ (μ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (integral_Ioi_cexp_add_mul ht (f t)).1
    · refine hint.norm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (integral_Ioi_norm_cexp_add_mul ht (f t)).symm
  change (∫ v, ∫ t, Φ (t, v) ∂μ ∂μ) = _
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (integral_Ioi_cexp_add_mul ht (f t)).2

end Complex
