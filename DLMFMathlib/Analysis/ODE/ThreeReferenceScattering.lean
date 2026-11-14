/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ThreeReferenceLiouvilleGreen
public import DLMFMathlib.Analysis.ODE.TwoTurningPoints
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact scattering probabilities from three-reference endpoint errors

Olver, *Asymptotics and Special Functions*, Chapter 13, §15.1–15.2,
pp. 513–515, synopsis O-13.12. The inputs are the actual canonical
solutions, coefficient branches, unit-phase comparison waves and the explicitly
required vanishing endpoint errors. Connection coefficients and probabilities
are conclusions, and the scattering state uses its actual value and derivative
limits from `ODE.TwoTurningPoints.IsScatteringState`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology Real

namespace Complex.ThreeReferenceScattering

/-- The actual right-side relative error against the transmitted comparison wave,
with the common amplitude scale and its unit phase retained. -/
def rightRelativeError (F : ℝ → ℝ) (a b u scale : ℝ) (phase : ℂ)
    (W : ℂ → ℂ) (x : ℝ) : ℂ :=
  W x / ((scale * Real.exp (-u * ODE.TwoTurningPoints.barrierAction F a b) *
    ODE.TwoTurningPoints.potential F a b x ^ (-(1 : ℝ) / 4) : ℝ) * phase *
      exp (I * u * ODE.TwoTurningPoints.rightAction F a b x)) - 1

/-- The defining actual boundary-wave relative error. -/
theorem rightRelativeError_def (F : ℝ → ℝ) (a b u scale : ℝ) (phase : ℂ)
    (W : ℂ → ℂ) (x : ℝ) :
    rightRelativeError F a b u scale phase W x =
      W x / ((scale * Real.exp (-u * ODE.TwoTurningPoints.barrierAction F a b) *
        ODE.TwoTurningPoints.potential F a b x ^ (-(1 : ℝ) / 4) : ℝ) * phase *
          exp (I * u * ODE.TwoTurningPoints.rightAction F a b x)) - 1 := rfl

/-- Canonical solutions with the source's actual vanishing endpoint errors give both
exact probability quotients. Flux makes the incoming denominator nonzero and gives the
exponentially informative reflection identity. All comparison phases are unit-modulus;
the common positive amplitude scale cancels.
Olver, Chapter 13, (15.02)–(15.10), synopsis O-13.12. -/
theorem scattering_probabilities_of_canonical_family
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFpos : ∀ x, 0 < F x)
    {g : ℝ → ℂ} (hg : Continuous g) (hgreal : ∀ x, (g x).im = 0)
    {a b u scale : ℝ} (hab : a < b) (hu : 0 < u) (hscale : 0 < scale)
    {D : ThreeReferenceLiouvilleGreen.Data 1} {W : Fin 3 → ℂ → ℂ}
    (hW : D.IsCanonicalFamily W)
    (hglobal : ∀ j, ContDiff ℝ 2 (fun x : ℝ => W j x) ∧
      ∀ x : ℝ, deriv (deriv (fun t : ℝ => W j t)) x =
        (-(u : ℂ) ^ 2 * ODE.TwoTurningPoints.potential F a b x + g x) * W j x)
    (hcoefficient : ∀ x : ℝ, x < a →
      D.coefficient x = -(u : ℂ) ^ 2 * ODE.TwoTurningPoints.potential F a b x)
    {incidentPhase reflectedPhase transmittedPhase : ℂ}
    (hphases : ‖incidentPhase‖ = 1 ∧ ‖reflectedPhase‖ = 1 ∧ ‖transmittedPhase‖ = 1)
    (hleft : ∀ x : ℝ, x < a → (x : ℂ) ∈ D.branchDomain 1 ∩ D.branchDomain 2 ∧
      D.sourceAmplitude 1 x * exp (-D.phase 1 x) =
        (scale * ODE.TwoTurningPoints.potential F a b x ^ (-(1 : ℝ) / 4) : ℝ) *
          incidentPhase * exp (-I * u * ODE.TwoTurningPoints.leftAction F a b x) ∧
      D.sourceAmplitude 2 x * exp (-D.phase 2 x) =
        (scale * ODE.TwoTurningPoints.potential F a b x ^ (-(1 : ℝ) / 4) : ℝ) *
          reflectedPhase * exp (I * u * ODE.TwoTurningPoints.leftAction F a b x))
    (hcross : Tendsto (D.relativeError W 1 ∘ D.reference 2) atTop (𝓝 0))
    (hleftzero : ∀ j ∈ ({1, 2} : Set (Fin 3)),
      Tendsto (fun x : ℝ => D.relativeError W j x) atBot (𝓝 0) ∧
      Tendsto (fun x : ℝ => D.amplitude j x ^ 2 * deriv (D.relativeError W j) x)
        atBot (𝓝 0))
    (hrightzero : Tendsto (rightRelativeError F a b u scale transmittedPhase (W 0))
      atTop (𝓝 0))
    (hrightderiv : Tendsto (fun x : ℝ =>
      deriv (rightRelativeError F a b u scale transmittedPhase (W 0)) x /
        Real.sqrt (ODE.TwoTurningPoints.potential F a b x)) atTop (𝓝 0)) :
    ∃ δ₂ δ₃ : ℂ,
      Tendsto (D.relativeError W 0 ∘ D.reference 1) atTop (𝓝 δ₂) ∧
      Tendsto (D.relativeError W 0 ∘ D.reference 2) atTop (𝓝 δ₃) ∧
      ‖δ₂‖ ≤ (Real.exp (D.joinVariation 0 1) - 1) / 2 ∧
      ‖δ₃‖ ≤ (Real.exp (D.joinVariation 0 2) - 1) / 2 ∧ 1 + δ₃ ≠ 0 ∧
      let L := ODE.TwoTurningPoints.barrierAction F a b
      let y := fun x : ℝ => (Real.exp (u * L) : ℂ) / (scale * transmittedPhase) * W 0 x
      let A := (Real.exp (u * L) : ℂ) * exp (π * I / 3) *
        (1 + δ₃) * incidentPhase / transmittedPhase
      let B := (Real.exp (u * L) : ℂ) * exp (-π * I / 3) *
        (1 + δ₂) * reflectedPhase / transmittedPhase
      ODE.TwoTurningPoints.IsScatteringState F g a b u y A B ∧ A ≠ 0 ∧
        ‖A‖⁻¹ ^ 2 = Real.exp (-2 * u * L) / ‖1 + δ₃‖ ^ 2 ∧
        ‖B‖ ^ 2 / ‖A‖ ^ 2 = ‖1 + δ₂‖ ^ 2 / ‖1 + δ₃‖ ^ 2 ∧
        ‖A‖⁻¹ ^ 2 + ‖B‖ ^ 2 / ‖A‖ ^ 2 = 1 ∧
        ‖B‖ ^ 2 / ‖A‖ ^ 2 = 1 - Real.exp (-2 * u * L) / ‖1 + δ₃‖ ^ 2 := by
  sorry

end Complex.ThreeReferenceScattering
