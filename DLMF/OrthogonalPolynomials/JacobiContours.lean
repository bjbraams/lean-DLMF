/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.JacobiContinuation
public import DLMF.AlgebraicAnalytic.Complex.Basic

/-!
# Schläfli's Jacobi integral on a general contour

Analytic logarithms of the two ratios specify the correlated powers and their
normalization at the evaluation point. The contour may be any positively oriented
simple closed piecewise-smooth contour whose filled interior lies in that branch
domain. Source: Kristensson, *Second Order Differential Equations*,
Chapter 5, Lemma 5.9, p. 101.
-/

@[expose] public noncomputable section

open Complex Set DLMF.AlgebraicAnalytic
open scoped Real

namespace DLMF.OrthogonalPolynomials

/-- Schläfli's formula for the polynomial continuation of Jacobi polynomials on
an arbitrary positive simple contour. The normalized analytic logarithms remove
any ambiguity of the powers for complex parameters. Kristensson, Chapter 5,
Lemma 5.9, p. 101. -/
theorem jacobiExtended_schlafli_contour (α β : ℂ) (n : ℕ) {x : ℂ}
    (hx₁ : x ≠ 1) (hx₂ : x ≠ -1)
    {γ : ℝ → ℂ} (hγ : IsSimpleClosedContour γ 0 1)
    (hpositive : IsPositivelyOriented γ 0 1) (hx : x ∈ contourInterior γ 0 1)
    {U : Set ℂ} (hU : IsOpen U)
    (hregion : γ '' Icc 0 1 ∪ contourInterior γ 0 1 ⊆ U)
    {L₁ L₂ : ℂ → ℂ} (hL₁ : AnalyticOnNhd ℂ L₁ U) (hL₂ : AnalyticOnNhd ℂ L₂ U)
    (hL₁exp : ∀ t ∈ U, exp (L₁ t) = (1 - t) / (1 - x))
    (hL₂exp : ∀ t ∈ U, exp (L₂ t) = (1 + t) / (1 + x))
    (hL₁zero : L₁ x = 0) (hL₂zero : L₂ x = 0) :
    jacobiExtended α β n x = (2 : ℂ)⁻¹ ^ n / (2 * Real.pi * I) *
      ∫ t : ℝ in 0..1, (γ t ^ 2 - 1) ^ n * exp (α * L₁ (γ t) + β * L₂ (γ t)) /
        (γ t - x) ^ (n + 1) * deriv γ t := by
  sorry

end DLMF.OrthogonalPolynomials
