/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ToMathlib.Analysis.SpecialFunctions.Pow

/-!
# Complex powers of positive reals

Small identities and bounds for complex powers `x ^ w` with a positive real base:
the exponential forms `x ^ w = exp (log x · w)`, `(x²) ^ w = x ^ (2 w)`, products with a
positive real factor, conjugation of `2 ^ w`, the bound
`‖w ^ s‖ ≤ ‖w‖ ^ Re s e^{π |Im s|}`, and the elementary bound `|log t| ≤ 4 t^{-1/4}` on
`(0, 1]`.
-/

@[expose] public section
open scoped Real ComplexConjugate

namespace Complex

/-- A complex power of a positive real is an exponential: `t ^ w = exp (w · log t)`. -/
theorem ofReal_cpow_eq_exp_mul_log {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t : ℂ) ^ w = exp (w * Real.log t) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'), ← ofReal_log ht.le, mul_comm]

/-- `(x²) ^ w = x ^ (2 w)` for real `x > 0`. -/
theorem ofReal_sq_cpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x ^ 2 : ℝ) : ℂ) ^ w = (x : ℂ) ^ (2 * w) := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [sq, ofReal_mul, mul_cpow_ofReal_nonneg hx.le hx.le, ← cpow_add _ _ hxc]; ring_nf

/-- `(x²) ^ (-1/2) = x⁻¹` for real `x > 0`. -/
theorem ofReal_sq_cpow_neg_one_div_two {x : ℝ} (hx : 0 < x) :
    ((x ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = (x : ℂ)⁻¹ := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  rw [Real.rpow_neg_one]
  push_cast
  ring

/-- `(w a) ^ s = w ^ s a ^ s` for a positive real factor `a`. -/
theorem mul_ofReal_cpow_of_ne_zero {w : ℂ} (hw : w ≠ 0) {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (w * a) ^ s = w ^ s * (a : ℂ) ^ s := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hw ha'), cpow_def_of_ne_zero hw,
    cpow_def_of_ne_zero ha', log_mul_ofReal a ha w hw, ← exp_add, ofReal_log ha.le]
  ring_nf

/-- Conjugation commutes with powers of `2`: `conj (2 ^ w) = 2 ^ conj w`. -/
theorem conj_two_cpow (w : ℂ) : conj ((2 : ℂ) ^ w) = 2 ^ conj w := by
  have h2 : (2 : ℂ).arg ≠ π := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_ne_zero.symm
  rw [cpow_conj _ _ h2, map_ofNat]

/-- `‖w ^ s‖ ≤ ‖w‖ ^ Re s · e^{π |Im s|}` for `w ≠ 0` (principal branch). -/
theorem norm_cpow_le_rpow_mul_exp {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ‖w ^ s‖ ≤ ‖w‖ ^ s.re * Real.exp (π * |s.im|) := by
  rw [norm_cpow_of_ne_zero hw, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg w * s.im) ≤ |arg w * s.im| := neg_le_abs _
    _ = |arg w| * |s.im| := abs_mul _ _
    _ ≤ π * |s.im| := by gcongr; exact abs_arg_le_pi w

end Complex

namespace Real

/-- `|log t| ≤ 4 t^{-1/4}` for `0 < t ≤ 1`. -/
theorem abs_log_le_four_mul_rpow_neg_one_fourth {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |log t| ≤ 4 * t ^ (-(1 / 4 : ℝ)) := by
  have h1 := neg_rpow_div_le_log ht.le (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 := log_nonpos ht.le ht1
  rw [abs_of_nonpos h2]
  have : -t ^ (-(1 / 4 : ℝ)) / (1 / 4) = -(4 * t ^ (-(1 / 4 : ℝ))) := by ring
  linarith

end Real
