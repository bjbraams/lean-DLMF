/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Joint entire dependence of regularized Kummer functions

Olver, *Asymptotics and Special Functions*, Chapter 7, §9, pp. 254–258,
synopsis O-7.15. The function is Mathlib's canonical reciprocal-Gamma series;
there is no ordinary-function evaluation at a singular lower parameter.
-/

@[expose] public section

namespace DLMF.Confluent

/-- The regularized Kummer series is jointly entire in both parameters and its argument.
Olver, Chapter 7, §9, pp. 254–258, synopsis O-7.15. -/
theorem differentiable_regularizedKummer_parameters_argument :
    Differentiable ℂ (fun p : ℂ × ℂ × ℂ =>
      Complex.regularizedHGFun {p.1} {p.2.1} p.2.2) := by
  sorry

end DLMF.Confluent
