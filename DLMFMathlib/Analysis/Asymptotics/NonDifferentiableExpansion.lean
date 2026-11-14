/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A null expansion whose derivative has no null expansion

Andrews, Askey and Roy, *Special Functions*, Appendix C, pp. 612–614
(synopsis AAR-C.1.1–C.2.2). The explicit smooth function
`exp(-x) sin(exp x)` is smaller than every inverse power, while its derivative
has an oscillating term of order one. A differentiable real expansion therefore
cannot in general be differentiated term by term.
-/

@[expose] public section

open Filter Asymptotics

namespace Real

/-- The exponentially damped oscillatory function has every inverse-power coefficient zero.
Andrews–Askey–Roy, *Special Functions*, Appendix C, pp. 612–614
(synopsis AAR-C.1.1–C.2.2). -/
theorem hasAsymptoticExpansion_exp_neg_mul_sin_exp :
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => x⁻¹ ^ n)
      (fun _ => (0 : ℝ)) (fun x : ℝ => exp (-x) * sin (exp x)) := by
  sorry

/-- The derivative of the explicit null-expansion example.
Andrews–Askey–Roy, *Special Functions*, Appendix C, pp. 612–614
(synopsis AAR-C.1.1–C.2.2). -/
theorem hasDerivAt_exp_neg_mul_sin_exp (x : ℝ) :
    HasDerivAt (fun t : ℝ => exp (-t) * sin (exp t))
      (cos (exp x) - exp (-x) * sin (exp x)) x := by
  convert ((hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul
    ((hasDerivAt_sin (exp x)).comp x (hasDerivAt_exp x)) using 1
  · rfl
  · dsimp only [Function.comp_def]
    rw [exp_neg]
    field_simp [exp_ne_zero]
    ring

/-- The derivative is not little-oh of one, despite all original coefficients vanishing.
Andrews–Askey–Roy, *Special Functions*, Appendix C, pp. 612–614
(synopsis AAR-C.1.1–C.2.2). -/
theorem not_deriv_exp_neg_mul_sin_exp_isLittleO_one :
    ¬ (fun x : ℝ => deriv (fun t : ℝ => exp (-t) * sin (exp t)) x)
      =o[atTop] (fun _ => (1 : ℝ)) := by
  sorry

end Real
