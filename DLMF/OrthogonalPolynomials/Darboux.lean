/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.PolynomialContinuation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Uniform Darboux asymptotics of Jacobi polynomials

The full `O(n^(-3/2))` interior-angle remainder of Andrews, Askey and Roy,
*Special Functions*, §6.6. The polynomial continuation allows every real pair
of Jacobi parameters, including exceptional negative integers.
-/

@[expose] public section

open scoped Real

namespace DLMF.OrthogonalPolynomials

/-- Darboux's Jacobi expansion uniformly away from both endpoints.
Andrews–Askey–Roy, *Special Functions*, §6.6, pp. 310–312
(synopsis AAR-6.5.1–6.6.2). -/
theorem jacobiExtended_darboux_uniform (α β : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ ≤ Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ θ ∈ Set.Icc δ (Real.pi - δ),
        ‖jacobiExtended α β n (Real.cos θ) -
          ((Real.cos (((n : ℝ) + (α + β + 1) / 2) * θ -
              (α + 1 / 2) * Real.pi / 2) /
            (Real.sqrt (Real.pi * n) * Real.sin (θ / 2) ^ (α + 1 / 2) *
              Real.cos (θ / 2) ^ (β + 1 / 2)) : ℝ) : ℂ)‖ ≤
          C * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  sorry

end DLMF.OrthogonalPolynomials
