/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.BoseEinstein
public import DLMFMathlib.Analysis.Fourier.HorizontalStrip

/-!
# Exponential weights for the Bose–Einstein kernel

Polynomial multiples of `x/(exp(2πx)-1)` remain integrable on the positive half-line after
multiplication by `exp(θx)` whenever `θ < 2π`. A global exponential majorant handles both
the removable singularity at the origin and the tail at infinity.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Real

namespace Real

/-- Subcritical exponential weights preserve integrability of polynomial multiples of the
regularized Bose–Einstein kernel on the positive half-line. -/
theorem integrableOn_mul_one_add_pow_mul_exp_div_exp_two_pi_sub_one {θ : ℝ}
    (hθ : θ < 2 * π) (N : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x * (1 + x) ^ N * exp (θ * x) / (exp (2 * π * x) - 1)) (Ioi 0) := by
  let c : ℝ := 2 * π - θ
  let C : ℝ := 1 + 1 / (2 * π)
  have hc : 0 < c := sub_pos.mpr hθ
  have hI := (integrable_one_add_abs_pow_mul_exp_neg hc (N + 1)).integrableOn
    (s := Ioi (0 : ℝ))
  refine (hI.const_mul C).mono'
    (show AEStronglyMeasurable
      (fun x : ℝ => x * (1 + x) ^ N * exp (θ * x) / (exp (2 * π * x) - 1))
      (volume.restrict (Ioi 0)) from (by fun_prop : Measurable _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have hπ : 0 < 2 * π := by positivity
  have hden : 0 < exp (2 * π * x) - 1 :=
    sub_pos.mpr (one_lt_exp_iff.mpr (mul_pos hπ hx0))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ x * (1 + x) ^ N * exp (θ * x) / (exp (2 * π * x) - 1)), abs_of_pos hx0]
  have hcoef : x * (1 + 1 / (2 * π * x)) = x + 1 / (2 * π) := by
    field_simp
  have he : exp (θ * x) * exp (-(2 * π * x)) = exp (-(c * x)) := by
    rw [← exp_add]
    congr 1
    dsimp only [c]
    ring
  have hC : x + 1 / (2 * π) ≤ C * (1 + x) := by
    dsimp only [C]
    nlinarith [mul_nonneg (show 0 ≤ 1 / (2 * π) by positivity) hx0.le]
  calc
    _ = (x * (1 + x) ^ N * exp (θ * x)) * (1 / (exp (2 * π * x) - 1)) := by ring
    _ ≤ (x * (1 + x) ^ N * exp (θ * x)) *
        ((1 + 1 / (2 * π * x)) * exp (-(2 * π * x))) := by
      exact mul_le_mul_of_nonneg_left
        (one_div_exp_sub_one_le_mul_exp_neg (mul_pos hπ hx0)) (by positivity)
    _ = (x + 1 / (2 * π)) * (1 + x) ^ N * exp (-(c * x)) := by
      calc
        _ = (x * (1 + 1 / (2 * π * x))) * (1 + x) ^ N *
            (exp (θ * x) * exp (-(2 * π * x))) := by ring
        _ = _ := by rw [hcoef, he]
    _ ≤ C * ((1 + x) ^ (N + 1) * exp (-(c * x))) := by
      calc
        _ ≤ (C * (1 + x)) * ((1 + x) ^ N * exp (-(c * x))) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC
            (by positivity : 0 ≤ (1 + x) ^ N * exp (-(c * x)))
        _ = _ := by rw [pow_succ]; ring

end Real
