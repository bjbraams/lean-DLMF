/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TurningPointCoordinates
public import Mathlib.Analysis.RCLike.Sqrt

/-!
# Parameter scaling and the intrinsic cut at a simple pole

Olver, *Asymptotics and Special Functions*, Chapter 13, §§5–6,
pp. 487–491, synopsis O-13.03. The normalized coordinate is the square
of the action, so its derivative at the pole is four times the residue.
The scaled perturbation retains the double-pole exponent coefficient.
-/

@[expose] public noncomputable section
open Complex Set Filter
open scoped Topology
namespace ODE.SimplePoleScaling

/-- The perturbation after the dilation zeta=u²*x, for nonzero u. -/
def perturbation (ψ : ℂ → ℂ) (u z : ℂ) : ℂ := ψ (z / u ^ 2) / u ^ 2

/-- The defining parameter-dilated perturbation. -/
theorem perturbation_def (ψ : ℂ → ℂ) (u z : ℂ) :
    perturbation ψ u z = ψ (z / u ^ 2) / u ^ 2 := rfl

/-- Dilation converts the large-parameter simple-pole equation to unit
parameter without changing the double-pole coefficient. Olver, Chapter 13, §5.
The identity is a residual identity, so it applies before assuming the ODE. -/
theorem dilated_residual {W : ℂ → ℂ} {u z ν : ℂ} (hu : u ≠ 0) (hz : z ≠ 0)
    (hW : ContDiffAt ℂ 2 W (z / u ^ 2)) (ψ : ℂ → ℂ) :
    let V := fun t => W (t / u ^ 2)
    deriv (deriv V) z -
      (1 / (4 * z) + (ν ^ 2 - 1) / (4 * z ^ 2) + perturbation ψ u z / z) * V z =
      u⁻¹ ^ 4 * (deriv (deriv W) (z / u ^ 2) -
        (u ^ 2 / (4 * (z / u ^ 2)) +
          (ν ^ 2 - 1) / (4 * (z / u ^ 2) ^ 2) + ψ (z / u ^ 2) / (z / u ^ 2)) *
            W (z / u ^ 2)) := by
  sorry

/-- The principal cut is the inverse image of the negative action-square ray.
Its initial tangent is -1/(4*u²*F(z0)), not a cut imposed independently of the
pole residue. Olver, Chapter 13, §5, pp. 487–488. -/
theorem exists_local_principalCut_parameterization {F : ℂ → ℂ} {z₀ u : ℂ}
    (hF : AnalyticAt ℂ F z₀) (hFzero : F z₀ ≠ 0) (hu : u ≠ 0) :
    ∃ ζ X : ℂ → ℂ, ∃ ε : ℝ, 0 < ε ∧ AnalyticAt ℂ ζ z₀ ∧ AnalyticAt ℂ X 0 ∧
      ζ z₀ = 0 ∧ deriv ζ z₀ = 4 * u ^ 2 * F z₀ ∧ X 0 = z₀ ∧
      (fun z => (z - z₀) * deriv ζ z ^ 2) =ᶠ[𝓝 z₀]
        (fun z => 4 * u ^ 2 * F z * ζ z) ∧
      (fun z => X (ζ z)) =ᶠ[𝓝 z₀] id ∧
      (∀ t : ℝ, 0 < t → t < ε → ζ (X (-t)) = -t ∧ (sqrt (ζ (X (-t)))).re = 0) ∧
      Tendsto (fun t : ℝ => (X (-t) - z₀) / t) (𝓝[>] 0)
        (𝓝 (-(4 * u ^ 2 * F z₀)⁻¹)) := by
  sorry

end ODE.SimplePoleScaling
