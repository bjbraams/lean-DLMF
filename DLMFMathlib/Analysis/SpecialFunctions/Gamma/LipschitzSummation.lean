/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Lipschitz summation on a vertical arithmetic progression

Andrews, Askey and Roy, *Special Functions*, Appendix D, Exercise 6. Both
series converge absolutely; the powers use the right-half-plane logarithm.
-/

@[expose] public section

open scoped Real

namespace Complex

/-- Lipschitz's bilateral-to-unilateral summation formula.
Andrews–Askey–Roy, *Special Functions*, Appendix D, Exercise 6, p. 627
(synopsis AAR-D-exercise-6). -/
theorem lipschitz_summation {x s : ℂ} (hx : 0 < x.re) (hs : 1 < s.re)
    {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    Summable (fun n : ℤ => exp (2 * Real.pi * I * n * a) / (x + I * n) ^ s) ∧
      Summable (fun k : ℕ => ((k + a : ℝ) : ℂ) ^ (s - 1) *
        exp (-2 * Real.pi * (k + a) * x)) ∧
      (∑' n : ℤ, exp (2 * Real.pi * I * n * a) / (x + I * n) ^ s) =
        (2 * Real.pi : ℂ) ^ s / Gamma s *
          ∑' k : ℕ, ((k + a : ℝ) : ℂ) ^ (s - 1) *
            exp (-2 * Real.pi * (k + a) * x) := by
  sorry

end Complex
