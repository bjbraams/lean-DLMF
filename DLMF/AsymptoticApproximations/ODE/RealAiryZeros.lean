/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.RealAiryPerturbation
public import DLMF.Airy.Zeros.RealAndAi

/-!
# Quantitative zeros of real Airy perturbations

Only complete comparison brackets contained in the transformed interval are used.
The error controls are supplied explicitly; the variation controls in the real
turning-point theorem have exactly the required monotonicities.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
§6, (6.01)–(6.08), pp. 405–408.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Real Topology

namespace DLMF.AsymptoticApproximations.Real

/-- Airy error controls smaller than one half give zero-free regions, exactly
one zero in each complete comparison bracket, and the explicit source displacement
bounds. Index zero denotes the `Bi` approximation, index one the `Ai` approximation.
Olver, Chapter 11, §6, pp. 405–408. -/
theorem airy_perturbation_zeros_and_displacement
    {a b : EReal} (ha : a < 0) (hb : 0 < b) {u : ℝ} (hu : 0 < u)
    {ψ : ℝ → ℝ} {W σ : Fin 2 → ℝ → ℝ}
    (hψ : ContinuousOn ψ {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hW : ∀ k, ContDiffOn ℝ 2 (W k) {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hODE : ∀ (k : Fin 2) (x : ℝ), a < (x : EReal) → (x : EReal) < b →
      deriv (deriv (W k)) x = (u ^ 2 * x + ψ x) * W k x)
    (hsmall : ∀ (k : Fin 2) (x : ℝ), a < (x : EReal) → (x : EReal) < b →
      0 ≤ σ k x ∧ σ k x < 1 / 2)
    (hmonotone : MonotoneOn (σ 0) {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hantitone : AntitoneOn (σ 1) {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (herror : ∀ (k : Fin 2) (x : ℝ), a < (x : EReal) → (x : EReal) < b →
      let v := u ^ (2 / 3 : ℝ)
      let C := if k = 0 then DLMF.Airy.Real.airyBi else DLMF.Airy.Real.airyAi
      let Cderiv := if k = 0 then DLMF.Airy.Real.airyBiDeriv
        else DLMF.Airy.Real.airyAiDeriv
      let E := if k = 0 then AiryEnvelope.weight (v * x) else
        (AiryEnvelope.weight (v * x))⁻¹
      |W k x - C (v * x)| ≤ E * AiryEnvelope.modulus (v * x) * σ k x ∧
      |deriv (W k) x - v * Cderiv (v * x)| ≤
        v * E * AiryEnvelope.derivativeModulus (v * x) * σ k x) :
    let v := u ^ (2 / 3 : ℝ)
    let D := {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
    (∀ x ∈ D, airyEnvCrit / v ≤ x → W 0 x ≠ 0) ∧
      (∀ x ∈ D, DLMF.Airy.airyBiZero 1 / v ≤ x → W 1 x ≠ 0) ∧
      (∀ n : ℕ, 1 ≤ n →
        let left := DLMF.Airy.airyAiZero n / v
        let right := (if n = 1 then airyEnvCrit else DLMF.Airy.airyAiZero (n - 1)) / v
        Icc left right ⊆ D →
          (∃! x, x ∈ Ioo left right ∧ W 0 x = 0) ∧
          ∀ x ∈ Ioo left right, W 0 x = 0 →
            |v * x - DLMF.Airy.airyBiZero n| ≤
              Real.pi ^ 2 / 3 * AiryEnvelope.modulus (v * right) ^ 2 * σ 0 right) ∧
      ∀ n : ℕ, 1 ≤ n →
        let left := DLMF.Airy.airyBiZero (n + 1) / v
        let right := DLMF.Airy.airyBiZero n / v
        Icc left right ⊆ D →
          (∃! x, x ∈ Ioo left right ∧ W 1 x = 0) ∧
          ∀ x ∈ Ioo left right, W 1 x = 0 →
            |v * x - DLMF.Airy.airyAiZero n| ≤
              Real.pi ^ 2 / 3 * AiryEnvelope.modulus (v * right) ^ 2 * σ 1 left := by
  sorry

end DLMF.AsymptoticApproximations.Real
