/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
/-!
# Comparing complex norms after a positive real shift

A positive real-part gap eventually dominates bounded differences of squared norms. This
supplies uniform comparisons for shifted factors of hypergeometric coefficients.

* `Complex.norm_add_ofReal_le_of_re_gap`: an explicit sufficient condition for comparing
  `‖z + t‖` and `‖w + t‖` at a nonnegative real shift.
-/

public section
namespace Complex
/-- A positive real-part gap dominates a bounded squared norm after a sufficiently large
nonnegative real shift. -/
lemma norm_add_ofReal_le_of_re_gap {z w : ℂ} {M ε t : ℝ}
    (hz : ‖z‖ ≤ M) (hre : z.re + ε ≤ w.re) (ht0 : 0 ≤ t)
    (ht : M ^ 2 ≤ 2 * t * ε) : ‖z + (t : ℂ)‖ ≤ ‖w + (t : ℂ)‖ := by
  have hsq : z.re^2 + z.im^2 ≤ M^2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) hz 2
    rw [← normSq_eq_norm_sq] at hn
    simpa only [normSq_apply,pow_two] using hn
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← normSq_eq_norm_sq,← normSq_eq_norm_sq]
  simp only [normSq_apply,add_re,add_im,ofReal_re,ofReal_im,add_zero]
  have hmul := mul_le_mul_of_nonneg_left hre (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht0)
  nlinarith [sq_nonneg w.re,sq_nonneg w.im]
end Complex
