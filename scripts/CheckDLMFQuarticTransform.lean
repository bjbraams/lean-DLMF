/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.AlgebraicAnalytic.Transforms.Tables
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Domain of the quartic Fourier cosine transform

The transform formula in DLMF Table 1.14.2, row 5, holds when `|Im a| < Re a`.
The weaker condition `0 < Re a` admits the counterexample `a = 1 + I`, `x = π / 2`.
The corrected identity is checked through the library theorem
`DLMF.AlgebraicAnalytic.fourierCosTransform_quartic`.
-/

public noncomputable section
open Complex MeasureTheory Filter Set
open scoped Real Topology Nat
namespace DLMF.AlgebraicAnalytic.QuarticTransform
/-- The quartic cosine transform in the sector `|Im a| < Re a`. -/
lemma fourierCosTransform_quartic_of_abs_im_lt_re {a : ℂ} (ha : |a.im| < a.re)
    {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => 4 * a ^ 3 / (4 * a ^ 4 + t ^ 4)) x =
      (Real.sqrt Real.pi : ℂ) * cexp (-a * x) * Complex.sin (a * x + Real.pi / 4) := by
  exact DLMF.AlgebraicAnalytic.fourierCosTransform_quartic ha hx

end DLMF.AlgebraicAnalytic.QuarticTransform
#print axioms DLMF.AlgebraicAnalytic.QuarticTransform.fourierCosTransform_quartic_of_abs_im_lt_re

namespace DLMF.AlgebraicAnalytic

set_option maxHeartbeats 0

/-- The quartic transform formula fails at `a = 1 + I`, `x = π / 2`. -/
lemma fourierCosTransform_quartic_counterexample :
    fourierCosTransform (fun t => 4 * (1 + I) ^ 3 / (4 * (1 + I) ^ 4 + t ^ 4)) (π / 2) ≠
      (Real.sqrt π : ℂ) * cexp (-(1 + I) * (π / 2)) *
        Complex.sin ((1 + I) * (π / 2) + π / 4) := by
  have h3 : 4 * (1 + I) ^ 3 = (-8 + 8 * I : ℂ) := by
    norm_num [Complex.ext_iff, pow_succ, Complex.mul_re, Complex.mul_im]
  have h4 : (1 + I) ^ 4 = (-4 : ℂ) := by
    norm_num [Complex.ext_iff, pow_succ, Complex.mul_re, Complex.mul_im]
  have hpt (t : ℝ) : 4 * (1 + I) ^ 3 / (4 * (1 + I) ^ 4 + (t : ℂ) ^ 4) *
      (Real.cos (π / 2 * t) : ℂ) =
      (-8 + 8 * I) * ((Real.cos (π / 2 * t) / (t ^ 4 - 16) : ℝ) : ℂ) := by
    rw [h3, h4]
    push_cast
    ring_nf
  have hleft :
      (fourierCosTransform (fun t => 4 * (1 + I) ^ 3 / (4 * (1 + I) ^ 4 + t ^ 4))
        (π / 2)).re +
      (fourierCosTransform (fun t => 4 * (1 + I) ^ 3 / (4 * (1 + I) ^ 4 + t ^ 4))
        (π / 2)).im = 0 := by
    unfold fourierCosTransform
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t), integral_const_mul,
      integral_complex_ofReal]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, add_re, add_im, neg_re, neg_im,
      I_re, I_im]
    norm_num
  let E : ℂ := cexp (-(1 + I) * (π / 2))
  let S : ℂ := Complex.sin ((1 + I) * (π / 2) + π / 4)
  have hEre : E.re = 0 := by
    dsimp only [E]
    rw [Complex.exp_re]
    norm_num [Complex.mul_re, Complex.mul_im, Real.cos_neg]
  have hEim : E.im = -Real.exp (-π / 2) := by
    dsimp only [E]
    rw [Complex.exp_im]
    norm_num [Complex.mul_re, Complex.mul_im, Real.sin_neg]
    ring_nf
  have hS : S = ((Real.sin (3 * π / 4) * Real.cosh (π / 2) : ℝ) : ℂ) +
      ((Real.cos (3 * π / 4) * Real.sinh (π / 2) : ℝ) : ℂ) * I := by
    dsimp only [S]
    rw [show (1 + I) * (π / 2) + π / 4 =
      ((3 * π / 4 : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * I by push_cast; ring_nf]
    rw [Complex.sin_add_mul_I]
    norm_cast
  have hSre : 0 < S.re := by
    rw [hS]
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
    exact mul_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))
      (Real.cosh_pos _)
  have hSim : S.im < 0 := by
    rw [hS]
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
    exact mul_neg_of_neg_of_pos (Real.cos_neg_of_pi_div_two_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
      (Real.sinh_pos_iff.mpr (by positivity))
  have hright : ((Real.sqrt π : ℂ) * E * S).re +
      ((Real.sqrt π : ℂ) * E * S).im < 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      hEre, hEim, mul_zero, zero_mul, sub_zero, add_zero]
    nlinarith [Real.sqrt_pos.mpr Real.pi_pos, Real.exp_pos (-π / 2),
      mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos (-π / 2)),
      mul_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos (-π / 2))) hSre,
      mul_neg_of_pos_of_neg
        (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos (-π / 2))) hSim]
  intro heq
  have heq' := congrArg (fun w : ℂ => w.re + w.im) heq
  -- Fold the named exponential and sine factors before applying their sign estimates.
  change _ = ((Real.sqrt π : ℂ) * E * S).re + ((Real.sqrt π : ℂ) * E * S).im at heq'
  rw [hleft] at heq'
  exact hright.ne' heq'

/-- Positive real part alone is insufficient for the quartic transform formula. -/
lemma fourierCosTransform_quartic_statement_false :
    ¬ ∀ a : ℂ, 0 < a.re → ∀ x : ℝ, 0 < x →
      fourierCosTransform (fun t => 4 * a ^ 3 / (4 * a ^ 4 + t ^ 4)) x =
        (Real.sqrt π : ℂ) * cexp (-a * x) * Complex.sin (a * x + π / 4) := by
  intro h
  apply fourierCosTransform_quartic_counterexample
  simpa only [ofReal_div, ofReal_ofNat] using
    h (1 + I) (by norm_num) (π / 2) (by positivity)

#print axioms fourierCosTransform_quartic_counterexample
#print axioms fourierCosTransform_quartic_statement_false

end DLMF.AlgebraicAnalytic
