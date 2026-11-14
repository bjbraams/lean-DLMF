/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The hypergeometric basis for Airy's equation

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 3, Exercise 3.15,
gives a basis of real solutions of Airy's equation using the entire `₀F₁` functions
with lower parameters `2/3` and `4/3`. Their initial data are `(1, 0)` and `(0, 1)`.
-/

@[expose] public noncomputable section

namespace DLMF.Airy.Real

/-- A twice continuously differentiable real function solves Airy's equation precisely
when it has unique coordinates in Duverney's `₀F₁` basis.
Duverney Chapter 3, Exercise 3.15, page 89, synopsis DU-3.18. -/
theorem airy_equation_iff_existsUnique_hypergeometric_coordinates {y : ℝ → ℝ}
    (hy : ContDiff ℝ 2 y) :
    (∀ x : ℝ, iteratedDeriv 2 y x - x * y x = 0) ↔
      ∃! c : ℝ × ℝ, ∀ x : ℝ,
        y x = c.1 *
          (DLMF.Hypergeometric.generalizedHypergeometric 0 {(2 / 3 : ℂ)}
            ((x : ℂ) ^ 3 / 9)).re + c.2 * x *
          (DLMF.Hypergeometric.generalizedHypergeometric 0 {(4 / 3 : ℂ)}
            ((x : ℂ) ^ 3 / 9)).re := by
  sorry

end DLMF.Airy.Real
