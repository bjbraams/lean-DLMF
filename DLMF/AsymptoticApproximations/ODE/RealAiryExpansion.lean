/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.RealAiryPerturbation
public import DLMFMathlib.Analysis.ODE.TurningPointCoefficients
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Higher real Airy expansions and variation errors

The coefficient sequence is the canonical generic turning-point recursion.
The finite approximant is an actual compound sum, and both function and derivative
errors use the exact source variation constants. A separate tail theorem gives
convergence of the variations from differentiated decay of the perturbation.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
Theorem 7.1 and its following discussion, pp. 409–412.
-/

@[expose] public noncomputable section

open Complex Filter Set ODE
open scoped Real Topology Asymptotics

namespace DLMF.AsymptoticApproximations.Real

/-- The compound real Airy approximation through `A_n,B_(n-1)`, with the two
opposite endpoint normalizations and all four exact variation bounds. Extended-real
endpoints include every convergent infinite-end case. Olver, Chapter 11,
Theorem 7.1, pp. 410–412. -/
theorem exists_airy_compound_expansion (a b : EReal)
    (ha : a < 0) (hb : 0 < b) {ψ : ℝ → ℂ} {A B : ℕ → ℝ → ℂ}
    (hcoeff : IsTurningPointCoefficientSequence ψ A B
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (n : ℕ) {u : ℝ} (hu : 0 < u)
    (hVzero : BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B 0 x)
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hVn : BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B n x)
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) :
    let D := {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
    let F := fun s x => (Real.sqrt |x| : ℂ) * B s x
    let scale := u ^ (2 / 3 : ℝ)
    let E := fun x => AiryEnvelope.weight (scale * x)
    let M := fun x => AiryEnvelope.modulus (scale * x)
    let N := fun x => AiryEnvelope.derivativeModulus (scale * x)
    let lam := AiryEnvelope.errorConstant
    ∃ εBi εAi : ℝ → ℂ, ContDiffOn ℝ 2 εBi D ∧ ContDiffOn ℝ 2 εAi D ∧
      (∀ x ∈ D,
        let WBi := fun t => turningPointPartialSum A B DLMF.Airy.airyBi u scale n t + εBi t
        let WAi := fun t => turningPointPartialSum A B DLMF.Airy.airyAi u scale n t + εAi t
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
        let VzeroLeft := (eVariationOn (F 0) (D ∩ Iic x)).toReal
        let VnLeft := (eVariationOn (F n) (D ∩ Iic x)).toReal
        let VzeroRight := (eVariationOn (F 0) (D ∩ Ici x)).toReal
        let VnRight := (eVariationOn (F n) (D ∩ Ici x)).toReal
        let leftBound := 2 * E x * Real.exp (2 * lam * VzeroLeft / u) * VnLeft / u ^ (2 * n + 1)
        let rightBound := 2 / E x * Real.exp (2 * lam * VzeroRight / u) *
          VnRight / u ^ (2 * n + 1)
        ‖εBi x‖ / M x ≤ leftBound ∧ ‖deriv εBi x‖ / (scale * N x) ≤ leftBound ∧
          ‖εAi x‖ / M x ≤ rightBound ∧ ‖deriv εAi x‖ / (scale * N x) ≤ rightBound := by
  sorry

/-- Differentiated real tail decay makes every A-coefficient bounded and every
weighted B-variation convergent at the selected real infinity. Both signs of
infinity are covered by `sigma=+-1`. Olver, Chapter 11, §7, pp. 411–412. -/
theorem exists_bounded_airy_coefficients_and_finite_variation
    {D : Set ℝ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℝ → ℂ} {A B : ℕ → ℝ → ℂ}
    (hcoeff : IsTurningPointCoefficientSequence ψ A B D)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : σ = 1 ∨ σ = -1)
    (hDtail : ∀ᶠ x : ℝ in comap (fun x : ℝ => σ * x) atTop, x ∈ D)
    (hdecay : ∀ s : ℕ, (iteratedDeriv s ψ) =O[comap (fun x : ℝ => σ * x) atTop]
      (fun x : ℝ => |x| ^ (-(s : ℝ) - 1 / 2 - δ))) (n : ℕ) :
    ∃ R C : ℝ, 1 ≤ R ∧ 0 ≤ C ∧ {x : ℝ | R ≤ σ * x} ⊆ D ∧
      (∀ x : ℝ, R ≤ σ * x → ‖A n x‖ ≤ C ∧ ‖B n x‖ ≤ C / Real.sqrt |x|) ∧
      BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B n x)
        {x : ℝ | R ≤ σ * x} := by
  sorry

end DLMF.AsymptoticApproximations.Real
