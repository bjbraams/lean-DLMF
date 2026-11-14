/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.RealAiryPerturbation
public import DLMFMathlib.Analysis.Complex.AmplitudePhaseError

/-!
# The real one-turning-point connection with explicit control

Olver, *Asymptotics and Special Functions*, Chapter 13, §7,
pp. 491–494, synopsis O-13.04. This is the canonical Airy-coordinate equation;
the original f,g form follows by the exact real turning-point substitution.
The cosine boundary condition fixes its solution, while a growing equivalent
at the other end does not determine an added recessive component.
-/

@[expose] public noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace DLMF.AsymptoticApproximations.Real.GansJeffreys

/-- A conservative explicit connection constant in terms of the canonical Airy
M/N envelope values and its Volterra constant. Olver, Chapter 13, §7. -/
def errorConstant : ℝ :=
  16 * (1 + Real.pi * AiryEnvelope.modulus 0 * AiryEnvelope.derivativeModulus 0) *
    (1 + AiryEnvelope.errorConstant + AiryEnvelope.errorConstant⁻¹)

/-- The defining explicit Airy connection constant. -/
theorem errorConstant_def : errorConstant =
    16 * (1 + Real.pi * AiryEnvelope.modulus 0 * AiryEnvelope.derivativeModulus 0) *
      (1 + AiryEnvelope.errorConstant + AiryEnvelope.errorConstant⁻¹) := rfl

/-- The same right-recessive solution has the amplitude-two oscillatory
connection, and the specified left cosine solution has the corresponding growing
coefficient. All errors share the actual weighted L1 control and are O(1/u).
Olver, Chapter 13, §7, pp. 491–494. -/
theorem exists_recessive_cosine_connection {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hi : Integrable (fun x : ℝ => |ψ x| / Real.sqrt |x|)) :
    let V := ∫ x : ℝ, |ψ x| / Real.sqrt |x|
    ∃ R C : ℝ → ℝ → ℝ, ∃ A B : ℝ → ℝ,
      (∀ u : ℝ, 0 < u →
        ContDiff ℝ 2 (R u) ∧ ContDiff ℝ 2 (C u) ∧
        (∀ x : ℝ, iteratedDeriv 2 (R u) x = (u ^ 2 * x + ψ x) * R u x ∧
          iteratedDeriv 2 (C u) x = (u ^ 2 * x + ψ x) * C u x) ∧
        Tendsto (fun x : ℝ => R u x * x ^ (1 / 4 : ℝ) *
          Real.exp (2 * u / 3 * x ^ (3 / 2 : ℝ))) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => |x| ^ (1 / 4 : ℝ) * R u x -
          2 * (A u * Real.sin (2 * u / 3 * (-x) ^ (3 / 2 : ℝ) + Real.pi / 4) +
            B u * Real.cos (2 * u / 3 * (-x) ^ (3 / 2 : ℝ) + Real.pi / 4)))
          atBot (𝓝 0) ∧
        Tendsto (fun x : ℝ => |x| ^ (1 / 4 : ℝ) * C u x -
          Real.cos (2 * u / 3 * (-x) ^ (3 / 2 : ℝ) + Real.pi / 4)) atBot (𝓝 0) ∧
        Tendsto (fun x : ℝ => C u x * x ^ (1 / 4 : ℝ) *
          Real.exp (-2 * u / 3 * x ^ (3 / 2 : ℝ))) atTop (𝓝 (A u)) ∧
        ‖((A u - 1 : ℝ) : ℂ) + Complex.I * B u‖ ≤
          errorConstant * (Real.exp (errorConstant * V / u) - 1)) ∧
      (fun u : ℝ => A u - 1) =O[atTop] (fun u : ℝ => u⁻¹) ∧
      B =O[atTop] (fun u : ℝ => u⁻¹) := by
  sorry

end DLMF.AsymptoticApproximations.Real.GansJeffreys
