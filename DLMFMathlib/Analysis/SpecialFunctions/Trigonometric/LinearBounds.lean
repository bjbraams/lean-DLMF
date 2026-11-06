/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A linear exponential bound for the complex sine

Integrating the cosine along the line segment from zero to `z` gives
`‖sin z‖ ≤ ‖z‖ exp(|Im z|)`. The linear factor controls a sine kernel at its zero endpoint,
while the exponential factor controls its growth away from the real axis.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Real

namespace Complex

/-- The complex sine is bounded by a linear factor times its exponential growth bound. -/
theorem norm_sin_le_norm_mul_exp_abs_im (z : ℂ) :
    ‖sin z‖ ≤ ‖z‖ * Real.exp |z.im| := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => sin ((t : ℂ) * z))
      (z * cos ((x : ℂ) * z)) x := by
    have h := ((Complex.hasDerivAt_sin ((x : ℂ) * z)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).mul_const z)).comp_ofReal (z := x)
    convert h using 1
    · rfl
    · ring
  have hi : (∫ t in (0 : ℝ)..1, z * cos ((t : ℂ) * z)) = sin z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (show IntervalIntegrable (fun t : ℝ => z * cos ((t : ℂ) * z)) volume 0 1 from
        (by fun_prop : Continuous (fun t : ℝ => z * cos ((t : ℂ) * z))).intervalIntegrable _ _)
    simpa using h
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖z * cos ((t : ℂ) * z)‖ ≤ ‖z‖ * Real.exp |z.im| := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have him : |((t : ℂ) * z).im| ≤ |z.im| := by
      rw [show ((t : ℂ) * z).im = t * z.im by simp, abs_mul, abs_of_nonneg ht.1.le]
      exact mul_le_of_le_one_left (abs_nonneg z.im) ht.2
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_cos_le_exp_abs_im _).trans
      (Real.exp_le_exp.mpr him)) (norm_nonneg z)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [hi] at h
  simpa using h

end Complex
