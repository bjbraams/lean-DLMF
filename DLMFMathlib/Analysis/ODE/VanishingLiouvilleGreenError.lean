/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Exact vanishing of adjacent complex Liouville–Green endpoint errors

Olver, *Asymptotics and Special Functions*, Chapter 13, Theorem 13.1,
pp. 508–510, synopsis O-13.10. Analytic complex-power asymptotics yield
error-density decay on interior sectors. The joining progressive paths are actual
curves which escape every compact set, with variations tending to zero. The result
is exact vanishing, not only a small nonzero endpoint constant.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology Real

namespace Complex.PowerSectorLiouvilleGreen

/-- The actual annular sector with its angles continued on an interval of width less
than a full turn. -/
def sector (R A B : ℝ) : Set ℂ :=
  exp '' {w : ℂ | R < Real.exp w.re ∧ A < w.im ∧ w.im < B}

/-- Membership in the annular sector is membership of an actual logarithmic lift. -/
theorem mem_sector_iff (R A B : ℝ) (z : ℂ) :
    z ∈ sector R A B ↔ ∃ w : ℂ,
      (R < Real.exp w.re ∧ A < w.im ∧ w.im < B) ∧ exp w = z := Iff.rfl

/-- Adjacent asymptotic principal domains, excluding their limiting boundary rays.
The principal directions themselves are `alpha*theta+arg(k)/2=pi/2+n*pi`. -/
def AdjacentRayDirections (α : ℝ) (k : ℂ) (θ₁ θ₂ : ℝ) : Prop :=
  ∃ n : ℤ,
    (α * θ₁ + arg k / 2 ∈ Ioo ((n : ℝ) * π - π / 2) ((n : ℝ) * π + π / 2) ∧
      α * θ₂ + arg k / 2 ∈ Ioo (((n : ℝ) + 1) * π - π / 2)
        (((n : ℝ) + 1) * π + π / 2)) ∨
    (α * θ₂ + arg k / 2 ∈ Ioo ((n : ℝ) * π - π / 2) ((n : ℝ) * π + π / 2) ∧
      α * θ₁ + arg k / 2 ∈ Ioo (((n : ℝ) + 1) * π - π / 2)
        (((n : ℝ) + 1) * π + π / 2))

/-- The defining adjacent-domain inequalities in unwrapped phase angle. -/
theorem adjacentRayDirections_iff (α : ℝ) (k : ℂ) (θ₁ θ₂ : ℝ) :
    AdjacentRayDirections α k θ₁ θ₂ ↔ ∃ n : ℤ,
      (α * θ₁ + arg k / 2 ∈ Ioo ((n : ℝ) * π - π / 2) ((n : ℝ) * π + π / 2) ∧
        α * θ₂ + arg k / 2 ∈ Ioo (((n : ℝ) + 1) * π - π / 2)
          (((n : ℝ) + 1) * π + π / 2)) ∨
      (α * θ₂ + arg k / 2 ∈ Ioo ((n : ℝ) * π - π / 2) ((n : ℝ) * π + π / 2) ∧
        α * θ₁ + arg k / 2 ∈ Ioo (((n : ℝ) + 1) * π - π / 2)
          (((n : ℝ) + 1) * π + π / 2)) := Iff.rfl

/-- Analytic annular-sector coefficients with the actual source complex-power limits.
A canonical branch amplitude, phase and control are explicit; no derivative decay is
assumed in place of deriving it from analyticity. -/
structure Data where
  radius : ℝ
  radius_pos : 0 < radius
  lowerAngle : ℝ
  upperAngle : ℝ
  angles_ordered : lowerAngle < upperAngle
  width_lt : upperAngle - lowerAngle < 2 * π
  exponent : ℝ
  perturbationExponent : ℝ
  exponent_pos : 0 < exponent
  perturbationExponent_pos : 0 < perturbationExponent
  leadingCoefficient : ℂ
  leadingCoefficient_ne_zero : leadingCoefficient ≠ 0
  coefficient : ℂ → ℂ
  perturbation : ℂ → ℂ
  amplitude : ℂ → ℂ
  phase : ℂ → ℂ
  control : ℂ → ℂ
  branchData : IsComplexLiouvilleGreenData coefficient perturbation amplitude phase control
    (sector radius lowerAngle upperAngle)
  coefficient_equiv : IsEquivalent
    (comap (fun w : ℂ => Real.exp w.re) atTop ⊓
      𝓟 {w : ℂ | lowerAngle < w.im ∧ w.im < upperAngle})
    (fun w => coefficient (exp w))
    (fun w => leadingCoefficient * exp (((2 * exponent - 2 : ℝ) : ℂ) * w))
  perturbation_bound : IsBigO
    (comap (fun w : ℂ => Real.exp w.re) atTop ⊓
      𝓟 {w : ℂ | lowerAngle < w.im ∧ w.im < upperAngle})
    (fun w => perturbation (exp w))
    (fun w => exp (((exponent - 2 - perturbationExponent : ℝ) : ℂ) * w))

namespace Data

/-- Cauchy differentiation of the analytic power equivalent gives the actual source
control-density decay on every closed interior subsector.
Olver, Theorem 13.1 proof, (13.02), synopsis O-13.10. -/
theorem control_deriv_isBigO (D : Data) {A B : ℝ}
    (hA : D.lowerAngle < A) (hAB : A < B) (hB : B < D.upperAngle) :
    (fun w : ℂ => deriv D.control (exp w))
      =O[comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | A ≤ w.im ∧ w.im ≤ B}]
        (fun w : ℂ => exp (((-1 - min D.exponent D.perturbationExponent : ℝ) : ℂ) * w)) := by
  sorry

/-- Adjacent rays are eventually progressive with opposite orientations and admit
actual progressive two-tail joins escaping every fixed circle with variation tending
to zero. The original straight tails are retained exactly.
Olver, Theorem 13.1, construction (13.06), synopsis O-13.10. -/
theorem exists_escaping_progressive_joins (D : Data) {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ Ioo D.lowerAngle D.upperAngle)
    (hθ₂ : θ₂ ∈ Ioo D.lowerAngle D.upperAngle)
    (hadj : AdjacentRayDirections D.exponent D.leadingCoefficient θ₁ θ₂) :
    ∃ (σ R : ℝ) (r : ℕ → ℝ) (γ : ℕ → ℝ → ℂ), (σ = 1 ∨ σ = -1) ∧ D.radius < R ∧
      AntitoneOn (fun t : ℝ => σ * (D.phase (t * exp (I * θ₁))).re) (Ici R) ∧
      MonotoneOn (fun t : ℝ => σ * (D.phase (t * exp (I * θ₂))).re) (Ici R) ∧
      (∀ n, R < r n ∧ (n : ℝ) < r n ∧ Continuous (γ n) ∧
        (∀ T > 0, TauCeti.IsPiecewiseC1On (γ n) (-T) T) ∧
        (∀ t, γ n t ∈ sector D.radius D.lowerAngle D.upperAngle ∧
          (n : ℝ) < ‖γ n t‖) ∧
        (∀ t ≤ -1, γ n t = (-t * r n : ℝ) * exp (I * θ₁)) ∧
        (∀ t ≥ 1, γ n t = (t * r n : ℝ) * exp (I * θ₂)) ∧
        Monotone (fun t => σ * (D.phase (γ n t)).re) ∧
        BoundedVariationOn (D.control ∘ γ n) univ) ∧
      Tendsto (fun n => (eVariationOn (D.control ∘ γ n) univ).toReal) atTop (𝓝 0) := by
  sorry

/-- The canonical relative error, not only its bound, vanishes at the adjacent reference
infinity. Both endpoint normalizations and the actual differential equation are retained.
Olver, Chapter 13, Theorem 13.1, synopsis O-13.10. -/
theorem tendsto_error_adjacent_zero (D : Data) {θ₁ θ₂ σ : ℝ}
    (hθ₁ : θ₁ ∈ Ioo D.lowerAngle D.upperAngle)
    (hθ₂ : θ₂ ∈ Ioo D.lowerAngle D.upperAngle)
    (hadj : AdjacentRayDirections D.exponent D.leadingCoefficient θ₁ θ₂)
    (hσ : σ = 1 ∨ σ = -1)
    (hdecay : Tendsto (fun t : ℝ => σ * (D.phase (t * exp (I * θ₁))).re) atTop atBot)
    {W ε : ℂ → ℂ}
    (hW : AnalyticOnNhd ℂ W (sector D.radius D.lowerAngle D.upperAngle))
    (hε : AnalyticOnNhd ℂ ε (sector D.radius D.lowerAngle D.upperAngle))
    (hode : ∀ z ∈ sector D.radius D.lowerAngle D.upperAngle,
      deriv (deriv W) z = (D.coefficient z + D.perturbation z) * W z)
    (hnorm : ∀ z ∈ sector D.radius D.lowerAngle D.upperAngle,
      W z = D.amplitude z * exp (σ * D.phase z) * (1 + ε z))
    (hzero : Tendsto (fun t : ℝ => ε (t * exp (I * θ₁))) atTop (𝓝 0))
    (hdzero : Tendsto (fun t : ℝ => D.amplitude (t * exp (I * θ₁)) ^ 2 *
      deriv ε (t * exp (I * θ₁))) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => ε (t * exp (I * θ₂))) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => D.amplitude (t * exp (I * θ₂)) ^ 2 *
        deriv ε (t * exp (I * θ₂))) atTop (𝓝 0) := by
  sorry

end Data
end Complex.PowerSectorLiouvilleGreen
