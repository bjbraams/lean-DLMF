/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import DLMFMathlib.Analysis.ODE.Wronskian

/-!
# Fundamental pairs for real-variable second-order linear equations

A nonzero Wronskian at one point makes two solutions a basis of all twice continuously
differentiable solutions on an open interval. This is the general real-variable principle
behind the solution-basis theorems in Duverney, *An Introduction to Hypergeometric
Functions*, Theorems 6.3, 7.1 and 7.11, and Exercises 3.15 and 6.9.
-/

@[expose] public noncomputable section

open Set

namespace ODE

/-- A pair of solutions with nonzero Wronskian gives unique constant coordinates for
every `C²` solution on an open interval. Duverney Theorems 6.3, 7.1, 7.11;
synopsis DU-6.07, DU-7.02, DU-7.13. -/
theorem existsUnique_linearCombination_of_wronskian_ne_zero
    {𝕜 : Type*} [RCLike 𝕜] {U : Set ℝ} (hU : IsOpen U) (hconnected : U.OrdConnected)
    {p q f g y : ℝ → 𝕜} (hp : ContinuousOn p U) (hq : ContinuousOn q U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) (hy : ContDiffOn ℝ 2 y U)
    (hfeq : ∀ x ∈ U, iteratedDeriv 2 f x = p x * deriv f x + q x * f x)
    (hgeq : ∀ x ∈ U, iteratedDeriv 2 g x = p x * deriv g x + q x * g x)
    (hyeq : ∀ x ∈ U, iteratedDeriv 2 y x = p x * deriv y x + q x * y x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ U) (hW : wronskian f g x₀ ≠ 0) :
    ∃! c : 𝕜 × 𝕜, ∀ x ∈ U, y x = c.1 * f x + c.2 * g x := by
  sorry

end ODE
