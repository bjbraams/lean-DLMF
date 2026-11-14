/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.AiryEnvelopes
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Real turning-point Airy approximations with explicit errors

The control function is an actual weighted integral. Extended-real interval
endpoints cover finite, boundary and infinite reference points, while weighted
integrability states precisely the finite-variation requirement. The solutions
retain both the Airy and derivative moduli and the exact supremum error constant.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
Theorem 3.1, pp. 399–400.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Real Topology

namespace DLMF.AsymptoticApproximations.Real

/-- The Airy perturbation control primitive, with an arbitrary finite base point.
Changing that base adds a constant and leaves every error variation unchanged.
Olver, Chapter 11, Theorem 3.1, pp. 399–400. -/
def airyPerturbationControl (ψ : ℝ → ℂ) (c x : ℝ) : ℂ :=
  -∫ t in c..x, ψ t / (Real.sqrt |t| : ℂ)

/-- The defining weighted interval integral. -/
theorem airyPerturbationControl_def (ψ : ℝ → ℂ) (c x : ℝ) :
    airyPerturbationControl ψ c x = -∫ t in c..x, ψ t / (Real.sqrt |t| : ℂ) := rfl

/-- The control primitive vanishes at its chosen base. -/
@[simp] theorem airyPerturbationControl_self (ψ : ℝ → ℂ) (c : ℝ) :
    airyPerturbationControl ψ c c = 0 := by
  simp [airyPerturbationControl]

/-- The real Airy approximation theorem on an interval with arbitrary finite or
infinite endpoints. Both normalized endpoint errors vanish at their prescribed
reference ends. The four quantitative inequalities use the actual E/M/N envelopes
and Lambda supremum, with no numerical substitutions. Olver, Chapter 11,
Theorem 3.1, pp. 399–400. -/
theorem exists_airy_perturbation_interval (a b : EReal) (c : ℝ)
    (hac : a < (c : EReal)) (hcb : (c : EReal) < b) {u : ℝ} (hu : 0 < u)
    (ψ : ℝ → ℂ)
    (hψ : ContinuousOn ψ {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hintegrable : IntegrableOn (fun x : ℝ => ‖ψ x‖ / Real.sqrt |x|)
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) :
    let D := {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
    let H := airyPerturbationControl ψ c
    let scale := u ^ (2 / 3 : ℝ)
    let E := fun x => AiryEnvelope.weight (scale * x)
    let M := fun x => AiryEnvelope.modulus (scale * x)
    let N := fun x => AiryEnvelope.derivativeModulus (scale * x)
    let lam := AiryEnvelope.errorConstant
    BoundedVariationOn H D ∧ ∃ εBi εAi : ℝ → ℂ,
      ContDiffOn ℝ 2 εBi D ∧ ContDiffOn ℝ 2 εAi D ∧
      (∀ x ∈ D,
        let WBi := fun t : ℝ => DLMF.Airy.airyBi (scale * t) + εBi t
        let WAi := fun t : ℝ => DLMF.Airy.airyAi (scale * t) + εAi t
        deriv (deriv WBi) x = ((u ^ 2 * x : ℝ) + ψ x) * WBi x ∧
        deriv (deriv WAi) x = ((u ^ 2 * x : ℝ) + ψ x) * WAi x) ∧
      Tendsto (fun x => εBi x / (M x * E x : ℝ))
        (comap (fun x : ℝ => (x : EReal)) (𝓝[>] a) ⊓ 𝓟 D) (𝓝 0) ∧
      Tendsto (fun x => deriv εBi x / (scale * N x * E x : ℝ))
        (comap (fun x : ℝ => (x : EReal)) (𝓝[>] a) ⊓ 𝓟 D) (𝓝 0) ∧
      Tendsto (fun x => εAi x / (M x / E x : ℝ))
        (comap (fun x : ℝ => (x : EReal)) (𝓝[<] b) ⊓ 𝓟 D) (𝓝 0) ∧
      Tendsto (fun x => deriv εAi x / (scale * N x / E x : ℝ))
        (comap (fun x : ℝ => (x : EReal)) (𝓝[<] b) ⊓ 𝓟 D) (𝓝 0) ∧
      ∀ x ∈ D,
        let leftVariation := (eVariationOn H (D ∩ Iic x)).toReal
        let rightVariation := (eVariationOn H (D ∩ Ici x)).toReal
        let leftBound := E x / lam * (Real.exp (lam * leftVariation / u) - 1)
        let rightBound := 1 / (lam * E x) * (Real.exp (lam * rightVariation / u) - 1)
        ‖εBi x‖ / M x ≤ leftBound ∧ ‖deriv εBi x‖ / (scale * N x) ≤ leftBound ∧
          ‖εAi x‖ / M x ≤ rightBound ∧ ‖deriv εAi x‖ / (scale * N x) ≤ rightBound := by
  sorry

end DLMF.AsymptoticApproximations.Real
