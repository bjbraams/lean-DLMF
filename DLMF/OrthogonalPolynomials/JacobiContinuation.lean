/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.Differential.ClassicalEquations
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Jacobi identities with polynomial continuation in the parameters

Andrews, Askey and Roy, *Special Functions*, §6.3, and Kristensson, *Second Order
Differential Equations*, §5.8, pp. 93–104. The canonical `jacobiExtended` finite
binomial sum is used at exceptional lower parameters; the hypergeometric quotient
`jacobiPolynomialP` agrees only when its lower parameter is admissible.
-/

@[expose] public section

open Complex
open scoped Topology BigOperators

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- Kristensson, §5.8.1, pp. 93–95, and AAR, §6.3: polynomially continued Jacobi
polynomials agree with their terminating Gauss realization for every admissible
lower parameter, without a real-part restriction. -/
theorem jacobiExtended_eq_jacobiPolynomialP_of_not_neg_nat {α : ℂ}
    (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)) (β : ℂ) (n : ℕ) (x : ℂ) :
    jacobiExtended α β n x = jacobiPolynomialP α β n x := by
  sorry

/-- Kristensson, §5.8.1, p. 95, and AAR, §6.3: the Jacobi differential equation
continues polynomially in both parameters, including exceptional Gauss denominators. -/
theorem jacobiExtended_differential_equation (α β : ℂ) (n : ℕ) (x : ℂ) :
    (1 - x ^ 2) * deriv (deriv (jacobiExtended α β n)) x +
      (β - α - (α + β + 2) * x) * deriv (jacobiExtended α β n) x +
        n * ((n : ℂ) + α + β + 1) * jacobiExtended α β n x = 0 := by
  sorry

/-- Kristensson, §5.8.2, pp. 96–98, and AAR, §6.3: the Jacobi generating
function near zero for arbitrary complex parameters and argument. The principal
radical and powers are the analytic branches normalized by their values at zero. -/
theorem exists_hasSum_jacobiExtended_generating (α β x : ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℂ, ‖t‖ < R →
      HasSum (fun n => jacobiExtended α β n x * t ^ n)
        ((2 : ℂ) ^ (α + β) /
          ((1 - 2 * x * t + t ^ 2) ^ (1 / 2 : ℂ) *
            (1 - t + (1 - 2 * x * t + t ^ 2) ^ (1 / 2 : ℂ)) ^ α *
            (1 + t + (1 - 2 * x * t + t ^ 2) ^ (1 / 2 : ℂ)) ^ β)) := by
  sorry

/-- Kristensson, §5.8.2: for a real argument in the orthogonality interval the
continued Jacobi generating function converges throughout the unit parameter disc. -/
theorem hasSum_jacobiExtended_generating (α β : ℂ) {x : ℝ} (hx : |x| ≤ 1)
    {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n => jacobiExtended α β n x * t ^ n)
      ((2 : ℂ) ^ (α + β) /
        ((1 - 2 * x * t + t ^ 2) ^ (1 / 2 : ℂ) *
          (1 - t + (1 - 2 * x * t + t ^ 2) ^ (1 / 2 : ℂ)) ^ α *
          (1 + t + (1 - 2 * x * t + t ^ 2) ^ (1 / 2 : ℂ)) ^ β)) := by
  sorry

/-- Kristensson, (5.25), p. 98, and AAR, §6.3: Rodrigues's identity for all
complex Jacobi parameters on the interior real interval. Positive real bases fix
the power branches; the derivative is a real-variable derivative with complex values. -/
theorem jacobiExtended_rodrigues (α β : ℂ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 1) :
    jacobiExtended α β n x = (-1 : ℂ) ^ n / (2 ^ n * n.factorial) *
      (1 - (x : ℂ)) ^ (-α) * (1 + (x : ℂ)) ^ (-β) *
        iteratedDeriv n (fun t : ℝ =>
          (1 - (t : ℂ)) ^ (α + n) * (1 + (t : ℂ)) ^ (β + n)) x := by
  sorry

/-- Kristensson, Lemma 5.9, p. 101: Schläfli's Jacobi integral on a positive
circle around `x` avoiding `±1`. The ratio powers stay on their principal branches,
equal to one at the center. -/
theorem jacobiExtended_schlafli_circle (α β : ℂ) (n : ℕ) {x : ℂ} {r : ℝ}
    (hr : 0 < r) (hr₁ : r < ‖x - 1‖) (hr₂ : r < ‖x + 1‖) :
    jacobiExtended α β n x = (2 : ℂ)⁻¹ ^ n / (2 * Real.pi * I) *
      circleIntegral (fun t : ℂ => (t ^ 2 - 1) ^ n *
        ((1 - t) / (1 - x)) ^ α * ((1 + t) / (1 + x)) ^ β /
          (t - x) ^ (n + 1)) x r := by
  sorry

end DLMF.OrthogonalPolynomials
