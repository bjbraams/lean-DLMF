/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Complex-power growth and an exponential counterexample

Olver, *Asymptotics and Special Functions*, Chapter 1, §§2–3, pp. 4–8,
synopsis O-1.02. The complex-power comparisons are norm consequences of
Mathlib's real-power/exponential and logarithm/real-power comparisons.
-/

@[expose] public section

open Asymptotics Filter

namespace Complex

/-- Any fixed complex power grows more slowly than the real exponential on the positive
axis. Olver, Chapter 1, §§2–3, pp. 4–8, synopsis O-1.02. -/
theorem isLittleO_ofReal_cpow_exp_atTop (a : ℂ) :
    (fun x : ℝ => (x : ℂ) ^ a) =o[atTop] Real.exp := by
  apply IsLittleO.of_norm_left
  refine (_root_.isLittleO_rpow_exp_atTop a.re).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (norm_cpow_eq_rpow_re_of_pos hx a).symm

/-- The logarithm is smaller than a complex power of positive real part.
Olver, Chapter 1, §§2–3, pp. 4–8, synopsis O-1.02. -/
theorem isLittleO_log_ofReal_cpow_atTop {a : ℂ} (ha : 0 < a.re) :
    Real.log =o[atTop] (fun x : ℝ => (x : ℂ) ^ a) := by
  apply IsLittleO.of_norm_right
  refine (_root_.isLittleO_log_rpow_atTop ha).congr' .rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (norm_cpow_eq_rpow_re_of_pos hx a).symm

end Complex

namespace Real

/-- Exponentiating equivalent functions need not preserve equivalence.
Olver, Chapter 1, §§2–3, pp. 4–8, synopsis O-1.02. The explicit pair is `x+1,x`. -/
theorem isEquivalent_add_one_and_not_exp :
    ((fun x : ℝ => x + 1) ~[atTop] (fun x : ℝ => x)) ∧
      ¬ ((fun x : ℝ => exp (x + 1)) ~[atTop] exp) := by
  sorry

end Real
