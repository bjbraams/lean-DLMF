/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import DLMFMathlib.Analysis.SpecialFunctions.Gamma.BetaHalfLine

/-!
# Mellin transforms of quadratic Cauchy kernels

The substitution `u = t²` reduces the Mellin transform of `1/(1+t²)` to Euler's beta
integral. Positive dilation gives the transform of `1/(a²+t²)` for `a > 0`.
Both transforms converge absolutely on the strip `0 < Re s < 2`.

## Main results

* `mellinConvergent_one_div_one_add_sq`, `mellin_one_div_one_add_sq`: the unscaled kernel.
* `mellinConvergent_one_div_sq_add_sq`, `mellin_one_div_sq_add_sq`: a positive scale.
-/

public noncomputable section

open Complex MeasureTheory Set

/-- Absolute Mellin convergence of the quadratic Cauchy kernel in the strip `0 < Re s < 2`. -/
theorem mellinConvergent_one_div_one_add_sq {s : ℂ} (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    MellinConvergent (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) s := by
  have h := integrableOn_cpow_div_one_add_cpow (a := s / 2) (b := 1 - s / 2)
    (by simp; linarith) (by simp; linarith)
  have hbase : MellinConvergent (fun t : ℝ => 1 / (1 + (t : ℂ))) (s / 2) := by
    simpa only [MellinConvergent, smul_eq_mul, add_sub_cancel, cpow_one, mul_one_div] using h
  have hsq := (MellinConvergent.comp_rpow (f := fun t : ℝ => 1 / (1 + (t : ℂ)))
    (s := s) (a := 2) (by norm_num)).mpr hbase
  simpa only [Real.rpow_two, ofReal_pow] using hsq

/-- The Mellin transform of the quadratic Cauchy kernel. -/
theorem mellin_one_div_one_add_sq {s : ℂ} (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    mellin (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) s =
      Gamma (s / 2) * Gamma (1 - s / 2) / 2 := by
  have hbase : mellin (fun t : ℝ => 1 / (1 + (t : ℂ))) (s / 2) =
      Gamma (s / 2) * Gamma (1 - s / 2) := by
    rw [mellin]
    simp only [smul_eq_mul, mul_one_div]
    have h := integral_cpow_div_one_add_cpow (s / 2) (1 - s / 2)
    simp only [add_sub_cancel, cpow_one] at h
    rw [h, betaIntegral_eq_Gamma_mul_div _ _ (by simp; linarith) (by simp; linarith),
      add_sub_cancel, Gamma_one, div_one]
  have h := mellin_comp_rpow (fun t : ℝ => 1 / (1 + (t : ℂ))) s 2
  simpa only [Real.rpow_two, ofReal_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul, ofReal_inv,
    ofReal_ofNat, hbase, inv_mul_eq_div] using h

/-- Absolute Mellin convergence of a quadratic Cauchy kernel with a positive scale. -/
theorem mellinConvergent_one_div_sq_add_sq {s : ℂ} {a : ℝ} (ha : 0 < a)
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    MellinConvergent (fun t : ℝ => 1 / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) s := by
  have h := ((MellinConvergent.comp_mul_left (f := fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2))
    (s := s) (a := a⁻¹) (inv_pos.mpr ha)).mpr
      (mellinConvergent_one_div_one_add_sq hs0 hs2)).div_const ((a : ℂ) ^ 2)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  simp only [smul_eq_mul, ofReal_mul, ofReal_inv]
  field_simp [ofReal_ne_zero.mpr ha.ne']

/-- The Mellin transform of a positively scaled quadratic Cauchy kernel. -/
theorem mellin_one_div_sq_add_sq {s : ℂ} {a : ℝ} (ha : 0 < a)
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    mellin (fun t : ℝ => 1 / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) s =
      (a : ℂ) ^ (s - 2) * Gamma (s / 2) * Gamma (1 - s / 2) / 2 := by
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hfun : (fun t : ℝ => 1 / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
      fun t : ℝ => (1 / (1 + ((a⁻¹ * t : ℝ) : ℂ) ^ 2)) / (a : ℂ) ^ 2 := by
    funext t
    simp only [ofReal_mul, ofReal_inv]
    field_simp
  rw [hfun, mellin_div_const,
    mellin_comp_mul_left (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) s (inv_pos.mpr ha),
    mellin_one_div_one_add_sq hs0 hs2, smul_eq_mul, ofReal_inv,
    inv_cpow_ofReal_nonneg ha.le, cpow_neg, inv_inv,
    cpow_sub _ _ ha0, cpow_ofNat]
  ring
