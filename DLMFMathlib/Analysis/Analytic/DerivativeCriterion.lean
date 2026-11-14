/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A real analytic derivative criterion and a flat example

Duverney, *An Introduction to Hypergeometric Functions*, Appendix B,
Theorem B.10 and Remark B.9. The criterion uses uniform factorial bounds on every
compact interval contained in an open domain. The flat example is `exp(-1/x²)`,
extended by zero at the origin.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace Real

/-- Uniform factorial derivative bounds characterize real analyticity of a smooth function.
Duverney Appendix B, Theorem B.10, equation (B.4), synopsis DU-B.04. -/
theorem analyticOnNhd_iff_iteratedDeriv_bound {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    AnalyticOnNhd ℝ f U ↔ ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U →
      ∃ C > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x ∈ Icc a b,
        |iteratedDeriv n f x| ≤ C * n.factorial * δ ^ n := by
  sorry

/-- Smoothness of the flat function `exp(-1/x²)` extended by zero.
Duverney Appendix B, Remark B.9, synopsis DU-B.03. -/
theorem contDiff_exp_neg_inv_sq :
    ContDiff ℝ ∞ (fun x : ℝ => if x = 0 then 0 else exp (-(x ^ 2)⁻¹)) := by
  convert expNegInvGlue.contDiff.comp (contDiff_id.pow 2) using 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · simp [expNegInvGlue, hx, (sq_pos_of_ne_zero hx).not_ge]

/-- Every derivative of the flat exponential is zero at the origin.
Duverney Appendix B, Remark B.9, synopsis DU-B.03. -/
theorem iteratedDeriv_exp_neg_inv_sq_zero (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => if x = 0 then 0 else exp (-(x ^ 2)⁻¹)) 0 = 0 := by
  sorry

/-- The smooth flat exponential is not analytic at the origin.
Duverney Appendix B, Remark B.9, synopsis DU-B.03. -/
theorem not_analyticAt_exp_neg_inv_sq_zero :
    ¬ AnalyticAt ℝ (fun x : ℝ => if x = 0 then 0 else exp (-(x ^ 2)⁻¹)) 0 := by
  sorry

end Real
