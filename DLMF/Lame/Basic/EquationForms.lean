/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Lame.Basic.Equations

/-!
# Lamé's equation: the Heun form and the wave equation (DLMF §§29.2(ii), 29.11)

The algebraic form of Lamé's equation is a Heun equation, and the Lamé wave equation with
`ω = 0` is Lamé's equation.

## Main results

* `isLameAlgebraicSolutionOn_iff_isHeunSolOn`: 29.2.2 is Heun's equation 31.2.1 (DLMF §29.2(ii)
  states this for the equivalent 29.2.10).
* `isLameWaveSolutionOn_zero_iff`: for `ω = 0` the Lamé wave equation reduces to 29.2.1
  (DLMF §29.11).

## Implementation notes

The singularities and the algebraic, trigonometric and Weierstrass forms of §29.2 need the
analytic theory of the Jacobi functions and are in `DLMF.Lame.DifferentialEquations`.
-/

@[expose] public section

namespace DLMF.Lame

/-- §29.2(ii): the algebraic form 29.2.2 is Heun's equation 31.2.1 with `a = k⁻²`,
`q = -hk⁻²/4`, `α = -ν/2`, `β = (ν+1)/2`, `γ = δ = ε = 1/2`. DLMF states this for 29.2.10,
which is 29.2.2 after the affine change `ζ = e₃ + (e₁ - e₃)ξ`. -/
@[dlmf 29.2.ii "29.2.2 as Heun's equation (DLMF states it for the equivalent 29.2.10)"]
theorem isLameAlgebraicSolutionOn_iff_isHeunSolOn {h ν k : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsLameAlgebraicSolutionOn h ν k w U ↔
      DLMF.Heun.IsHeunSolOn (k ^ 2)⁻¹ (-(h * (k ^ 2)⁻¹) / 4) (-ν / 2) ((ν + 1) / 2) (1 / 2)
        (1 / 2) (1 / 2) w U := by
  constructor
  · intro hw
    refine ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv ?_⟩
    simp only [DLMF.Heun.heunCoeffP, DLMF.Heun.heunCoeffR]
    rw [show ∀ x : ℂ, x / (4 * z * (z - 1) * (z - (k ^ 2)⁻¹)) =
      x / 4 / (z * (z - 1) * (z - (k ^ 2)⁻¹)) from fun x => by rw [div_div]; congr 1; ring]
    ring
  · intro hw
    refine ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv ?_⟩
    simp only [DLMF.Heun.heunCoeffP, DLMF.Heun.heunCoeffR]
    rw [show ∀ x : ℂ, x / (4 * z * (z - 1) * (z - (k ^ 2)⁻¹)) =
      x / 4 / (z * (z - 1) * (z - (k ^ 2)⁻¹)) from fun x => by rw [div_div]; congr 1; ring]
    ring

/-! ### The Lamé wave equation (§29.11) -/

/-- §29.11: for `ω = 0` the Lamé wave equation 29.11.1 reduces to Lamé's equation 29.2.1. -/
@[dlmf 29.11]
theorem isLameWaveSolutionOn_zero_iff {h ν k : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsLameWaveSolutionOn h ν k 0 w U ↔ IsLameSolutionOn h ν k w U := by
  constructor
  · intro hw
    exact ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv (by ring)⟩
  · intro hw
    exact ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv (by ring)⟩

end DLMF.Lame
