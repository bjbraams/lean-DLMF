/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF.Zeta.Polylog.LogarithmicExpansion

/-!
# The logarithm convention in the polylogarithm expansion

At `z = -1`, the principal values satisfy `log(1/z) = πi` and `-log z = -πi`.
The proved Lerch expansion therefore rules out the literal use of the former expression
in DLMF 25.12.12's singular term, already at order zero. This check uses only proved lemmas.
-/

open Complex DLMF.Zeta
open scoped Real Topology Nat

namespace DLMF.Zeta.PolylogLogarithmCheck

/-- The literal inverse-logarithm singular term has the wrong boundary value at `z = -1`. -/
theorem not_hasSum_log_inv_at_neg_one :
    ¬ HasSum (fun n : ℕ => riemannZeta ((0 : ℂ) - n) * log (-1 : ℂ) ^ n / n !)
      (polylog 0 (-1) - Gamma (1 - (0 : ℂ)) * log (1 / (-1 : ℂ)) ^ ((0 : ℂ) - 1)) := by
  have hs : ∀ n : ℕ, (0 : ℂ) ≠ (n : ℂ) + 1 := by
    intro n h
    have := congrArg re h
    simp only [zero_re, add_re, natCast_re, one_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hz : (-1 : ℂ) ∈ slitOne := Or.inr (by norm_num)
  have hz0 : (-1 : ℂ) ≠ 0 := by norm_num
  have hlog : ‖log (-1 : ℂ)‖ < 2 * π := by
    rw [log_neg_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_I, mul_one]
    nlinarith [Real.pi_pos]
  have hgood := PolylogLogarithmic.hasSum_regularized hs hz hz0 hlog
  intro hbad
  have heq := hgood.unique hbad
  have hne : log (-1 : ℂ) ≠ 0 := by
    rw [log_neg_one]
    exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  have he : (1 / (-1 : ℂ)) = -1 := by norm_num
  simp only [he, sub_zero, Gamma_one, zero_sub, one_mul, cpow_neg_one, inv_neg] at heq
  apply inv_ne_zero hne
  linear_combination (1 / 2 : ℂ) * heq

end DLMF.Zeta.PolylogLogarithmCheck

#print axioms DLMF.Zeta.PolylogLogarithmCheck.not_hasSum_log_inv_at_neg_one
