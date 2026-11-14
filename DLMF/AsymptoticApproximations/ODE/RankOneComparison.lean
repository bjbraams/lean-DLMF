/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Singularities
public import DLMFMathlib.Analysis.ODE.ComplexGreenDerivativeCoupling

/-!
# The computable rank-one residual comparison pair

Olver, *Asymptotics and Special Functions*, Chapter 7, Theorem 12.1,
pp. 265–270, synopsis O-7.18. All comparison functions, their normalized
Wronskian, and the finite formal truncation are actual expressions. Substitution
in `Complex.complexGreen_derivative_coupling_error` gives finite initial-error
bounds; its endpoint counterpart gives absolutely convergent infinite-tail bounds.
The full weighted progressive alternative is `ODE.WeightedVolterra.Data`.
-/

@[expose] public noncomputable section

open Set Complex
open scoped BigOperators

namespace DLMF.AsymptoticApproximations.RankOneComparison

/-- The rational parameter of the source's comparison pair. -/
def shift (pc qc : ℕ → ℂ) : ℂ :=
  (pc 0 * pc 1 - 2 * qc 1) / (pc 0 ^ 2 - 4 * qc 0)

/-- The defining comparison shift. -/
theorem shift_def (pc qc : ℕ → ℂ) :
    shift pc qc = (pc 0 * pc 1 - 2 * qc 1) / (pc 0 ^ 2 - 4 * qc 0) := rfl

/-- A comparison solution on a specified analytic logarithm branch. The other factor
uses its principal logarithm outside the circle containing the shift. -/
def comparisonFunction (pc qc : ℕ → ℂ) (lam : ℂ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  exp (-log (1 + shift pc qc / z) / 2 + lam * z + rankOneExponent pc qc lam * L z)

/-- The defining comparison function, with both power branches explicit. -/
theorem comparisonFunction_def (pc qc : ℕ → ℂ) (lam : ℂ) (L : ℂ → ℂ) (z : ℂ) :
    comparisonFunction pc qc lam L z =
      exp (-log (1 + shift pc qc / z) / 2 + lam * z + rankOneExponent pc qc lam * L z) := rfl

/-- The exact first-derivative comparison coefficient. -/
def coefficientP (pc : ℕ → ℂ) (z : ℂ) : ℂ := pc 0 + pc 1 / z

/-- The defining comparison coefficient. -/
theorem coefficientP_def (pc : ℕ → ℂ) (z : ℂ) :
    coefficientP pc z = pc 0 + pc 1 / z := rfl

/-- The second comparison coefficient, obtained from the first nowhere-zero member. -/
def coefficientQ (pc qc : ℕ → ℂ) (lam : ℂ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(deriv (deriv (comparisonFunction pc qc lam L)) z +
    coefficientP pc z * deriv (comparisonFunction pc qc lam L) z) /
      comparisonFunction pc qc lam L z

/-- The defining actual second comparison coefficient. -/
theorem coefficientQ_def (pc qc : ℕ → ℂ) (lam : ℂ) (L : ℂ → ℂ) (z : ℂ) :
    coefficientQ pc qc lam L z =
      -(deriv (deriv (comparisonFunction pc qc lam L)) z +
        coefficientP pc z * deriv (comparisonFunction pc qc lam L) z) /
          comparisonFunction pc qc lam L z := rfl

/-- The source's finite formal truncation in its literal logarithmic normalization. -/
def truncation (pc qc : ℕ → ℂ) (lam : ℂ) (L : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  exp (lam * z + rankOneExponent pc qc lam * L z) *
    ∑ n ∈ Finset.range N, rankOneCoeff pc qc lam n / z ^ n

/-- The defining finite truncation. -/
theorem truncation_def (pc qc : ℕ → ℂ) (lam : ℂ) (L : ℂ → ℂ) (N : ℕ) (z : ℂ) :
    truncation pc qc lam L N z = exp (lam * z + rankOneExponent pc qc lam * L z) *
      ∑ n ∈ Finset.range N, rankOneCoeff pc qc lam n / z ^ n := rfl

/-- The actual differential residual of an approximant. -/
def residual (p q F : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (deriv F) z + p z * deriv F z + q z * F z

/-- The defining computable residual. -/
theorem residual_def (p q F : ℂ → ℂ) (z : ℂ) :
    residual p q F z = deriv (deriv F) z + p z * deriv F z + q z * F z := rfl

/-- The comparison pair has an explicit nowhere-zero Wronskian and solves the same
comparison equation. Consequently its computed coefficient is exactly `-W'/W`.
No zero of either comparison exponential is silently excluded.
Olver, Chapter 7, Theorem 12.1 construction, synopsis O-7.18. -/
theorem comparison_pair_equations {D : Set ℂ} (hD : IsOpen D)
    {pc qc : ℕ → ℂ} {lam₁ lam₂ : ℂ} (hne : lam₁ ≠ lam₂)
    (hsum : lam₁ + lam₂ = -pc 0) (hprod : lam₁ * lam₂ = qc 0)
    {L : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L D) (hexp : ∀ z ∈ D, exp (L z) = z)
    (hshift : ∀ z ∈ D, ‖shift pc qc‖ < ‖z‖) :
    let V₁ := comparisonFunction pc qc lam₁ L
    let V₂ := comparisonFunction pc qc lam₂ L
    let W := fun z => V₁ z * deriv V₂ z - deriv V₁ z * V₂ z
    AnalyticOnNhd ℂ V₁ D ∧ AnalyticOnNhd ℂ V₂ D ∧
      AnalyticOnNhd ℂ (coefficientQ pc qc lam₁ L) D ∧
      (∀ z ∈ D, V₁ z ≠ 0 ∧ V₂ z ≠ 0 ∧ W z ≠ 0 ∧
        W z = (lam₂ - lam₁) * exp (-pc 0 * z - pc 1 * L z) ∧
        coefficientP pc z = -deriv W z / W z ∧
        deriv (deriv V₁) z + coefficientP pc z * deriv V₁ z +
          coefficientQ pc qc lam₁ L z * V₁ z = 0 ∧
        deriv (deriv V₂) z + coefficientP pc z * deriv V₂ z +
          coefficientQ pc qc lam₁ L z * V₂ z = 0) := by
  sorry

end DLMF.AsymptoticApproximations.RankOneComparison
