/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A reciprocal-exponential half-line integral

Andrews, Askey and Roy, *Special Functions*, Theorem 10.12.5, p. 535
(synopsis AAR-10.12.1–10.12.8). The endpoint parameter `b=0` is retained,
where the formula reduces to the elementary Gamma-half Laplace integral.
-/

@[expose] public section

open MeasureTheory

namespace Real

/-- The exact reciprocal-exponential integral with its full positive/zero parameter range.
Andrews–Askey–Roy, *Special Functions*, Theorem 10.12.5, p. 535
(synopsis AAR-10.12.1–10.12.8). Absolute convergence is part of the statement. -/
theorem integral_rpow_neg_half_mul_exp_neg_mul_sub_div {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * exp (-a * t - b / t)) (Set.Ioi 0) ∧
      (∫ t : ℝ in Set.Ioi 0, t ^ (-(1 / 2 : ℝ)) * exp (-a * t - b / t)) =
        sqrt (Real.pi / a) * exp (-2 * sqrt (a * b)) := by
  sorry

end Real
