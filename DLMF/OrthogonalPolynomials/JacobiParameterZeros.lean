/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Parameter monotonicity of shifted Jacobi zeros

Andrews, Askey and Roy, *Special Functions*, §8.5, pp. 415–419.
Increasing arrays enumerate the zeros of `P_n(1 - 2x)`, so the direction
of parameter monotonicity differs from that for the unshifted polynomial.
-/

@[expose] public section

namespace DLMF.OrthogonalPolynomials

/-- Increasing the first Jacobi parameter moves each shifted zero to the right.
Andrews–Askey–Roy, *Special Functions*, §8.5, p. 416
(synopsis AAR-8.5.1–8.5.5). -/
theorem jacobiExtended_shifted_zero_lt_of_first_parameter_lt
    {n : ℕ} {α₁ α₂ β : ℝ} (hα₁ : -1 < α₁) (hα : α₁ < α₂) (hβ : -1 < β)
    {x y : Fin n → ℝ} (hx : StrictMono x) (hy : StrictMono y)
    (hxroot : ∀ i, jacobiExtended α₁ β n (1 - 2 * (x i : ℂ)) = 0)
    (hyroot : ∀ i, jacobiExtended α₂ β n (1 - 2 * (y i : ℂ)) = 0) (i : Fin n) :
    x i < y i := by
  sorry

/-- Increasing the second Jacobi parameter moves each shifted zero to the left.
Andrews–Askey–Roy, *Special Functions*, §8.5, p. 416
(synopsis AAR-8.5.1–8.5.5). -/
theorem jacobiExtended_shifted_zero_lt_of_second_parameter_lt
    {n : ℕ} {α β₁ β₂ : ℝ} (hα : -1 < α) (hβ₁ : -1 < β₁) (hβ : β₁ < β₂)
    {x y : Fin n → ℝ} (hx : StrictMono x) (hy : StrictMono y)
    (hxroot : ∀ i, jacobiExtended α β₁ n (1 - 2 * (x i : ℂ)) = 0)
    (hyroot : ∀ i, jacobiExtended α β₂ n (1 - 2 * (y i : ℂ)) = 0) (i : Fin n) :
    y i < x i := by
  sorry

end DLMF.OrthogonalPolynomials
