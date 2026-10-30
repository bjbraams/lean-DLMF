/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Tactic.Ring

/-!
# Positive real scaling of the principal square root

Mathlib's real-and-imaginary-part formula `Complex.sqrt_eq_real_add_ite`
shows that nonnegative real scaling preserves the selected bank, including on the cut.
-/

@[expose] public section

open scoped Real
noncomputable section

namespace Complex
/-- A nonnegative real factor scales the principal complex square root without changing its bank. -/
lemma sqrt_ofReal_mul {a : ℝ} (ha : 0≤a) (w : ℂ) :
    sqrt ((a:ℂ)*w) = (Real.sqrt a:ℂ)*sqrt w := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp
  rw [sqrt_eq_real_add_ite, sqrt_eq_real_add_ite]
  simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero, mul_im, add_zero, mul_nonneg_iff_of_pos_left ha]
  rw [show (a*‖w‖+a*w.re)/2 = a*((‖w‖+w.re)/2) by ring,
    show (a*‖w‖-a*w.re)/2 = a*((‖w‖-w.re)/2) by ring,
    Real.sqrt_mul ha.le, Real.sqrt_mul ha.le]
  simp only [ofReal_mul]
  ring
end Complex

