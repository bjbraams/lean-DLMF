/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Elementary exponential bounds for trigonometric and hyperbolic functions

* `Complex.norm_sin_le_exp_abs_im`, `Complex.norm_cos_le_exp_abs_im`:
  `‖sin z‖, ‖cos z‖ ≤ e^{|Im z|}`;
* `Real.cosh_le_exp_abs`: `cosh t ≤ e^{|t|}`;
* `Real.exp_sub_one_le_mul_exp`: `eʸ - 1 ≤ y eʸ`;
* `Real.cos_pos_of_abs_lt_pi_div_two` and its partial converse
  `Real.abs_lt_pi_div_two_of_cos_pos`.
-/

@[expose] public section
open scoped Real

namespace Complex

/-- `‖e^{-iz}‖ ≤ e^{|Im z|}`. -/
private lemma norm_exp_neg_mul_I_le (z : ℂ) : ‖exp (-z * I)‖ ≤ Real.exp |z.im| := by
  rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])

/-- `‖e^{iz}‖ ≤ e^{|Im z|}`. -/
private lemma norm_exp_mul_I_le (z : ℂ) : ‖exp (z * I)‖ ≤ Real.exp |z.im| := by
  rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])

/-- The complex sine grows at most like `e^{|Im z|}`: `‖sin z‖ ≤ e^{|Im z|}`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖sin z‖ ≤ Real.exp |z.im| := by
  rw [sin, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  linarith [norm_sub_le (exp (-z * I)) (exp (z * I)), norm_exp_neg_mul_I_le z,
    norm_exp_mul_I_le z]

/-- The complex cosine grows at most like `e^{|Im z|}`: `‖cos z‖ ≤ e^{|Im z|}`. -/
theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  rw [cos, norm_div, Complex.norm_two]
  linarith [norm_add_le (exp (z * I)) (exp (-z * I)), norm_exp_neg_mul_I_le z,
    norm_exp_mul_I_le z]

end Complex

namespace Real

/-- The hyperbolic cosine is bounded by `e^{|t|}`. -/
theorem cosh_le_exp_abs (t : ℝ) : cosh t ≤ exp |t| := by
  rw [cosh_eq]
  linarith [exp_le_exp.mpr (le_abs_self t), exp_le_exp.mpr (neg_le_abs t)]

/-- `eʸ - 1 ≤ y eʸ` for every real `y` (convexity of the exponential at `y`). -/
theorem exp_sub_one_le_mul_exp (y : ℝ) : exp y - 1 ≤ y * exp y := by
  have h := add_one_le_exp (-y)
  have h2 : exp (-y) * exp y = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos y]

/-- The cosine is positive on the open interval `|φ| < π/2`. -/
theorem cos_pos_of_abs_lt_pi_div_two {φ : ℝ} (hφ : |φ| < π / 2) : 0 < cos φ :=
  cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩

/-- On `(-3π/2, 3π/2)` the cosine is positive only on `(-π/2, π/2)`. -/
theorem abs_lt_pi_div_two_of_cos_pos {u : ℝ} (h1 : -(3 * π / 2) < u) (h2 : u < 3 * π / 2)
    (hc : 0 < cos u) : |u| < π / 2 := by
  rw [abs_lt]
  constructor
  · by_contra h
    push Not at h
    have := cos_nonpos_of_pi_div_two_le_of_le (x := -u) (by linarith) (by linarith)
    rw [cos_neg] at this; linarith
  · by_contra h
    push Not at h
    have := cos_nonpos_of_pi_div_two_le_of_le (x := u) h (by linarith)
    linarith

end Real
