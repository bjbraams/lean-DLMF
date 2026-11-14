/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.Wronskian
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The symmetric-square equation with a first-derivative coefficient

Olver, *Asymptotics and Special Functions*, Chapter 5, Exercise 11.1,
p. 169, synopsis O-5.17. A product of two solutions of
`y''+p*y'+q*y=0` satisfies the displayed third-order equation.
The elementary cyclic Wronskian identity is the algebraic basis for Chapter 13,
§11, (11.13), synopsis O-13.09.
-/

@[expose] public noncomputable section

namespace ODE

/-- The product equation for a general second-order scalar differential equation,
including its first-derivative term. Olver, Chapter 5, Exercise 11.1,
p. 169, synopsis O-5.17. -/
theorem product_symmetricSquare_equation {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {U : Set 𝕜} (hU : IsOpen U) {p q f g : 𝕜 → 𝕜}
    (hp : DifferentiableOn 𝕜 p U) (hq : DifferentiableOn 𝕜 q U)
    (hf : ContDiffOn 𝕜 3 f U) (hg : ContDiffOn 𝕜 3 g U)
    (hfeq : ∀ z ∈ U, iteratedDeriv 2 f z + p z * deriv f z + q z * f z = 0)
    (hgeq : ∀ z ∈ U, iteratedDeriv 2 g z + p z * deriv g z + q z * g z = 0)
    {z : 𝕜} (hz : z ∈ U) :
    iteratedDeriv 3 (fun w => f w * g w) z +
      3 * p z * iteratedDeriv 2 (fun w => f w * g w) z +
      (2 * p z ^ 2 + deriv p z + 4 * q z) * deriv (fun w => f w * g w) z +
      (4 * p z * q z + 2 * deriv q z) * (f z * g z) = 0 := by
  sorry

/-- The three Wronskian cofactors give an exact pointwise linear relation for any three
functions. For solutions of one second-order ODE, Abel normalization makes these
cofactors constant connection coefficients. Olver, Chapter 13, (11.13), synopsis O-13.09. -/
theorem wronskian_cyclic_sum {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedCommRing E] [NormedSpace 𝕜 E] (f g h : 𝕜 → E) (z : 𝕜) :
    wronskian g h z * f z + wronskian h f z * g z + wronskian f g z * h z = 0 := by
  simp only [wronskian]
  ring

end ODE
