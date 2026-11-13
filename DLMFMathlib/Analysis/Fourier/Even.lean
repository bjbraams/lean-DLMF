/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fourier integrals of even functions on symmetric intervals

Pairing opposite points cancels the sine part of the exponential kernel.
-/

public noncomputable section

open Complex MeasureTheory

namespace Complex
/-- On a symmetric interval, the exponential integral of an even continuous function is
twice its cosine integral on the positive half. -/
theorem integral_symm_mul_exp_mul_I {f : ℝ → ℂ} (hf : Continuous f) (he : Function.Even f)
    (x R : ℝ) :
    (∫ t in -R..R, f t * exp (I * x * t)) =
      2 * ∫ t in (0 : ℝ)..R, f t * (Real.cos (x * t) : ℂ) := by
  let p : ℝ → ℂ := fun t => f t * exp (I * x * t)
  have hp : Continuous p := hf.mul (by fun_prop)
  have hneg : (∫ t in -R..(0 : ℝ), p t) = ∫ t in (0 : ℝ)..R, p (-t) := by
    simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
      (f := p) (a := 0) (b := R)).symm
  have hpoint (t : ℝ) : p (-t) + p t = 2 * (f t * (Real.cos (x * t) : ℂ)) := by
    dsimp [p]
    rw [he t, ofReal_neg, show I * (x : ℂ) * (-t) = -((x * t : ℝ) : ℂ) * I by push_cast; ring,
      show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I, exp_mul_I]
    simp only [neg_mul, cos_neg, sin_neg, ← ofReal_cos]
    ring
  calc
    (∫ t in -R..R, f t * exp (I * x * t)) =
        (∫ t in -R..(0 : ℝ), p t) + ∫ t in (0 : ℝ)..R, p t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hp.intervalIntegrable _ _) (hp.intervalIntegrable _ _)).symm
    _ = ∫ t in (0 : ℝ)..R, (p (-t) + p t) := by
      rw [hneg]
      exact (intervalIntegral.integral_add (f := fun t => p (-t))
        ((show Continuous (fun t => p (-t)) from hp.comp continuous_neg).intervalIntegrable _ _)
        (hp.intervalIntegrable _ _)).symm
    _ = 2 * ∫ t in (0 : ℝ)..R, f t * (Real.cos (x * t) : ℂ) := by
      simp_rw [hpoint]
      rw [intervalIntegral.integral_const_mul]
end Complex
