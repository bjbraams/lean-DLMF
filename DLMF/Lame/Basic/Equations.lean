/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import DLMF.JacobiElliptic.Basic
public import DLMF.Weierstrass.Basic
public import DLMF.Elliptic.Basic.Amplitude

/-!
# Lamé equations and their alternative normalizations
-/

@[expose] public noncomputable section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Set Filter
open scoped Real Topology

namespace DLMF.Lame

/-! ### Lamé's equation and its other forms (§29.2) -/

/-- Lamé's equation (DLMF 29.2.1) over `ℂ` on a set `U`:
`w'' + (h - ν(ν+1) k² sn²(z, k)) w = 0`, with `w` and `w'` complex differentiable at every
point of `U`. DLMF takes `0 < k < 1`, `ν ≥ -1/2` and `h` real; the predicate is stated for all
complex parameters. -/
@[dlmf 29.2.E1]
structure IsLameSolutionOn (h ν k : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- `w` is complex differentiable at every point of `U`. -/
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  /-- `w'` has the derivative prescribed by the differential equation at every point. -/
  hasDerivAt_deriv : ∀ z ∈ U,
    HasDerivAt (deriv w) (-(h - ν * (ν + 1) * k ^ 2 * jacobiSnk z k ^ 2) * w z) z

/-- The algebraic form of Lamé's equation (DLMF 29.2.2) in `ξ = sn²(z, k)` (29.2.3):
`w'' + ½(1/ξ + 1/(ξ-1) + 1/(ξ-k⁻²)) w' + (h k⁻² - ν(ν+1)ξ)/(4ξ(ξ-1)(ξ-k⁻²)) w = 0` on `U`. -/
@[dlmf 29.2.E2]
structure IsLameAlgebraicSolutionOn (h ν k : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- `w` is complex differentiable at every point of `U`. -/
  differentiableAt : ∀ ξ ∈ U, DifferentiableAt ℂ w ξ
  /-- `w'` has the derivative prescribed by the differential equation at every point. -/
  hasDerivAt_deriv : ∀ ξ ∈ U, HasDerivAt (deriv w)
    (-(1 / 2 * (1 / ξ + 1 / (ξ - 1) + 1 / (ξ - (k ^ 2)⁻¹)) * deriv w ξ) -
      (h * (k ^ 2)⁻¹ - ν * (ν + 1) * ξ) / (4 * ξ * (ξ - 1) * (ξ - (k ^ 2)⁻¹)) * w ξ) ξ

/-- The Weierstrass form of Lamé's equation (DLMF 29.2.9) in `η`:
`w'' + (g - ν(ν+1) ℘(η; g₂, g₃)) w = 0` on `U`, with the project's `℘(η; g₂, g₃)`
(`DLMF.Weierstrass.weierstrassPInvariants`). -/
@[dlmf 29.2.E9]
structure IsLameWeierstrassSolutionOn (g ν g₂ g₃ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- `w` is complex differentiable at every point of `U`. -/
  differentiableAt : ∀ η ∈ U, DifferentiableAt ℂ w η
  /-- `w'` has the derivative prescribed by the differential equation at every point. -/
  hasDerivAt_deriv : ∀ η ∈ U, HasDerivAt (deriv w)
    (-(g - ν * (ν + 1) * DLMF.Weierstrass.weierstrassPInvariants g₂ g₃ η) * w η) η

/-- The algebraic Weierstrass form of Lamé's equation (DLMF 29.2.10) in `ζ = ℘(η)`:
`w'' + ½ ∑ⱼ 1/(ζ - eⱼ) w' + (g - ν(ν+1)ζ)/(4 ∏ⱼ (ζ - eⱼ)) w = 0` on `U`. -/
@[dlmf 29.2.E10]
structure IsLameWeierstrassAlgebraicSolutionOn (g ν e₁ e₂ e₃ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) :
    Prop where
  /-- `w` is complex differentiable at every point of `U`. -/
  differentiableAt : ∀ ζ ∈ U, DifferentiableAt ℂ w ζ
  /-- `w'` has the derivative prescribed by the differential equation at every point. -/
  hasDerivAt_deriv : ∀ ζ ∈ U, HasDerivAt (deriv w)
    (-(1 / 2 * (1 / (ζ - e₁) + 1 / (ζ - e₂) + 1 / (ζ - e₃)) * deriv w ζ) -
      (g - ν * (ν + 1) * ζ) / (4 * (ζ - e₁) * (ζ - e₂) * (ζ - e₃)) * w ζ) ζ

/-- The Lamé (ellipsoidal) wave equation (DLMF 29.11.1) on `U`:
`w'' + (h - ν(ν+1) k² sn²(z, k) + k² ω² sn⁴(z, k)) w = 0`. -/
@[dlmf 29.11.E1]
structure IsLameWaveSolutionOn (h ν k ω : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- `w` is complex differentiable at every point of `U`. -/
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  /-- `w'` has the derivative prescribed by the differential equation at every point. -/
  hasDerivAt_deriv : ∀ z ∈ U, HasDerivAt (deriv w)
    (-(h - ν * (ν + 1) * k ^ 2 * jacobiSnk z k ^ 2 + k ^ 2 * ω ^ 2 * jacobiSnk z k ^ 4) * w z) z

/-- Lamé's equation (DLMF 29.2.1) for real `x ∈ ℝ` and real parameters, with the real
`sn(x, k) = Real.jacobiSnm x (k²)`: `w` is differentiable on `ℝ` and
`w'' = -(h - ν(ν+1) k² sn²(x, k)) w` everywhere. -/
@[dlmf 29.2.E1 "real form: real x, real h, ν, k"]
structure Real.IsLameSolution (h ν k : ℝ) (w : ℝ → ℝ) : Prop where
  /-- `w` is differentiable on `ℝ`. -/
  differentiable : Differentiable ℝ w
  /-- `w'` has the derivative prescribed by the differential equation at every point. -/
  hasDerivAt_deriv : ∀ x : ℝ,
    HasDerivAt (deriv w) (-(h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * w x) x

/-- The trigonometric form of Lamé's equation (DLMF 29.2.4) for real `φ`:
`(1 - k² cos²φ) w'' + k² cos φ sin φ w' + (h - ν(ν+1) k² cos²φ) w = 0`. -/
@[dlmf 29.2.E4]
structure Real.IsLameTrigSolution (h ν k : ℝ) (w : ℝ → ℝ) : Prop where
  /-- `w` is differentiable on `ℝ`. -/
  differentiable : Differentiable ℝ w
  /-- `w'` is differentiable on `ℝ`. -/
  differentiable_deriv : Differentiable ℝ (deriv w)
  /-- The trigonometric Lamé equation holds at every real `φ`. -/
  ode : ∀ φ : ℝ, (1 - k ^ 2 * Real.cos φ ^ 2) * deriv (deriv w) φ +
    k ^ 2 * Real.cos φ * Real.sin φ * deriv w φ +
      (h - ν * (ν + 1) * k ^ 2 * Real.cos φ ^ 2) * w φ = 0

/-- The variable `φ = π/2 - am(x, k)` of DLMF 29.2.5 for real `x` (`am` is the real amplitude
`Real.jacobiAmm x (k²)` of §22.16(i)); then `cos φ = sn(x, k)` and `sin φ = cn(x, k)`. -/
@[dlmf 29.2.E5]
def Real.lamePhi (x k : ℝ) : ℝ := π / 2 - Real.jacobiAmm x (k ^ 2)

end DLMF.Lame
