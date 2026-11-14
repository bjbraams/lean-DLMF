/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerM
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# A Kummer basis for Hermite's differential equation

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 6, Exercise 6.9,
equation (6.27), gives the even and odd confluent hypergeometric solutions for every
real order. Integer Hermite polynomials alone do not cover this parameter range.
-/

@[expose] public noncomputable section

namespace DLMF.Confluent.Real

/-- Unique coordinates in the even and odd Kummer basis characterize all real `C²`
solutions of Hermite's equation. Duverney Exercise 6.9, equation (6.27), synopsis DU-6.10. -/
theorem hermite_equation_iff_existsUnique_kummer_coordinates (ν : ℝ) {y : ℝ → ℝ}
    (hy : ContDiff ℝ 2 y) :
    (∀ x : ℝ, iteratedDeriv 2 y x - 2 * x * deriv y x + 2 * ν * y x = 0) ↔
      ∃! c : ℝ × ℝ, ∀ x : ℝ,
        y x = c.1 * (DLMF.Confluent.kummerM (-(ν : ℂ) / 2) (1 / 2)
          ((x : ℂ) ^ 2)).re + c.2 * x *
          (DLMF.Confluent.kummerM ((1 - (ν : ℂ)) / 2) (3 / 2)
            ((x : ℂ) ^ 2)).re := by
  sorry

end DLMF.Confluent.Real
