/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.Wronskian
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Wronskian criterion for two meromorphic functions

Kristensson, *Second Order Differential Equations*, Chapter 2, Lemma 2.1,
pp. 5–6. No common differential equation is assumed. At poles the statement is
about punctured germs, so arbitrary totalized values at isolated singular points
do not create a false pointwise linear-dependence assertion.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Complex

/-- Two analytic functions on a connected open domain have identically zero
Wronskian exactly when a nontrivial constant linear combination vanishes.
Kristensson, Chapter 2, Lemma 2.1, pp. 5–6. -/
theorem wronskian_eq_zero_iff_linearCombination_eq_zero {D : Set ℂ}
    (hD : IsOpen D) (hconnected : IsPreconnected D) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D) :
    (∀ z ∈ D, ODE.wronskian f g z = 0) ↔
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ z ∈ D, a * f z + b * g z = 0 := by
  sorry

/-- The same criterion for meromorphic functions is an equality of punctured germs,
including at poles and arbitrarily totalized removable points. Kristensson,
Chapter 2, Lemma 2.1, pp. 5–6. -/
theorem wronskian_eventuallyEq_zero_iff_linearCombination_eventuallyEq_zero
    {D : Set ℂ} (hD : IsOpen D) (hconnected : IsPreconnected D) {f g : ℂ → ℂ}
    (hf : MeromorphicOn f D) (hg : MeromorphicOn g D) :
    (∀ z ∈ D, ODE.wronskian f g =ᶠ[𝓝[≠] z] 0) ↔
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
        ∀ z ∈ D, (fun w => a * f w + b * g w) =ᶠ[𝓝[≠] z] 0 := by
  sorry

end Complex
