/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.ComplexEnvelopes
public import DLMFMathlib.Analysis.ODE.TurningPointCoefficients
public import DLMFMathlib.Analysis.ODE.ComplexGreenEquation

/-!
# Complex turning-point expansions with certified variation errors

The square-root lift is normalized in the reference recessive sector, and paths
avoid the turning point before their evaluation endpoint. This retains a genuine
continued branch of the phase. Every estimate uses the same lift for both
coefficient variations and includes the source's choice of adjacent modulus.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
Theorem 9.1, pp. 417–418.
-/

@[expose] public noncomputable section

open Complex Set Filter ODE DLMF.Airy.ComplexEnvelope
open scoped Real Topology

namespace DLMF.AsymptoticApproximations

/-- The complex compound Airy expansion normalized at a finite recessive reference
point. Both the error and its derivative satisfy the exact source envelope bound
on every admissible continued progressive path. Olver, Chapter 11,
Theorem 9.1, pp. 417–418. -/
theorem exists_complex_airy_expansion_finite_reference {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} {A B : ℕ → ℂ → ℂ}
    (hcoeff : IsTurningPointCoefficientSequence ψ A B D)
    {u v b : ℂ} (hu : u ≠ 0) (hscale : v ^ 3 = u ^ 2) (hb : b ∈ D) (hbzero : b ≠ 0)
    (j : ℤ) (hsector : |arg (rotation j * (v * b))| < Real.pi / 3) (n : ℕ) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧ ε b = 0 ∧ deriv ε b = 0 ∧
      (∀ z ∈ D,
        let W := fun t => turningPointPartialSum A B (solution j) u v n t + ε t
        deriv (deriv W) z = (u ^ 2 * z + ψ z) * W z) ∧
      ∀ γ p : ℝ → ℂ, TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = b →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        (∀ t ∈ Ico (0 : ℝ) 1, γ t ≠ 0) → ContinuousOn p (Icc 0 1) →
        (∀ t ∈ Icc (0 : ℝ) 1, p t ^ 2 = γ t) →
        u * b * p 0 = (rotation j * (v * b)) ^ (3 / 2 : ℂ) →
        AntitoneOn (fun t => (u * γ t * p t).re) (Icc 0 1) →
        BoundedVariationOn (fun t => p t * B 0 (γ t)) (Icc 0 1) →
        BoundedVariationOn (fun t => p t * B n (γ t)) (Icc 0 1) →
        ∀ k : ℤ,
          ((k = j + 1 ∧ v * γ 1 ∈ sector (j - 1) ∪ sector j) ∨
            (k = j - 1 ∧ v * γ 1 ∈ sector j ∪ sector (j + 1))) →
          let Vzero := (eVariationOn (fun t => p t * B 0 (γ t)) (Icc 0 1)).toReal
          let Vn := (eVariationOn (fun t => p t * B n (γ t)) (Icc 0 1)).toReal
          let errorBound := 4 * secondErrorConstant / weight j (v * γ 1) *
            Real.exp (4 * firstErrorConstant * Vzero / ‖u‖) * Vn / ‖u‖ ^ (2 * n + 1)
          ‖ε (γ 1)‖ / modulus k (v * γ 1) ≤ errorBound ∧
            ‖deriv ε (γ 1)‖ / (‖u‖ ^ (2 / 3 : ℝ) * derivativeModulus k (v * γ 1)) ≤
              errorBound := by
  sorry

/-- A prescribed boundary or infinite recessive tail gives the corresponding
complex Airy expansion. Every later path keeps that same initial tail, its square-
root branch and both coefficient variations. Olver, Chapter 11,
Theorem 9.1, pp. 417–418. -/
theorem exists_complex_airy_expansion_endpoint_reference {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} {A B : ℕ → ℂ → ℂ}
    (hcoeff : IsTurningPointCoefficientSequence ψ A B D)
    {u v : ℂ} (hu : u ≠ 0) (hscale : v ^ 3 = u ^ 2) (j : ℤ) (n : ℕ)
    {γ₀ p₀ : ℝ → ℂ} (hγ₀ : ContinuousOn γ₀ (Ioc 0 1))
    (hregular : ∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ₀ s 1)
    (himage : ∀ t ∈ Ioc (0 : ℝ) 1, γ₀ t ∈ D ∧ γ₀ t ≠ 0)
    (hp₀ : ContinuousOn p₀ (Ioc 0 1))
    (hroot : ∀ t ∈ Ioc (0 : ℝ) 1, p₀ t ^ 2 = γ₀ t)
    (hsector : ∀ t ∈ Ioc (0 : ℝ) 1, |arg (rotation j * (v * γ₀ t))| < Real.pi / 3)
    (hphase : ∀ t ∈ Ioc (0 : ℝ) 1,
      u * γ₀ t * p₀ t = (rotation j * (v * γ₀ t)) ^ (3 / 2 : ℂ))
    (hprogressive : AntitoneOn (fun t => (u * γ₀ t * p₀ t).re) (Ioc 0 1))
    (hend : (∃ b : ℂ, b ∉ D ∧ Tendsto γ₀ (𝓝[>] 0) (𝓝 b)) ∨
      Tendsto (fun t => ‖γ₀ t‖) (𝓝[>] 0) atTop)
    (hVzero : BoundedVariationOn (fun t => p₀ t * B 0 (γ₀ t)) (Ioc 0 1))
    (hVn : BoundedVariationOn (fun t => p₀ t * B n (γ₀ t)) (Ioc 0 1)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧
      (∀ z ∈ D,
        let W := fun t => turningPointPartialSum A B (solution j) u v n t + ε t
        deriv (deriv W) z = (u ^ 2 * z + ψ z) * W z) ∧
      Tendsto (fun t => ε (γ₀ t) * weight j (v * γ₀ t) / modulus (j + 1) (v * γ₀ t))
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => deriv ε (γ₀ t) * weight j (v * γ₀ t) /
        (‖u‖ ^ (2 / 3 : ℝ) * derivativeModulus (j + 1) (v * γ₀ t) : ℝ))
          (𝓝[>] 0) (𝓝 0) ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ p : ℝ → ℂ,
        TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = γ₀ s →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        (∀ t ∈ Ico (0 : ℝ) 1, γ t ≠ 0) → ContinuousOn p (Icc 0 1) →
        (∀ t ∈ Icc (0 : ℝ) 1, p t ^ 2 = γ t) → p 0 = p₀ s →
        AntitoneOn (fun t => (u * γ t * p t).re) (Icc 0 1) →
        BoundedVariationOn (fun t => p t * B 0 (γ t)) (Icc 0 1) →
        BoundedVariationOn (fun t => p t * B n (γ t)) (Icc 0 1) →
        ∀ k : ℤ,
          ((k = j + 1 ∧ v * γ 1 ∈ sector (j - 1) ∪ sector j) ∨
            (k = j - 1 ∧ v * γ 1 ∈ sector j ∪ sector (j + 1))) →
          let Vzero := (eVariationOn (fun t => p₀ t * B 0 (γ₀ t)) (Ioc 0 s)).toReal +
            (eVariationOn (fun t => p t * B 0 (γ t)) (Icc 0 1)).toReal
          let Vn := (eVariationOn (fun t => p₀ t * B n (γ₀ t)) (Ioc 0 s)).toReal +
            (eVariationOn (fun t => p t * B n (γ t)) (Icc 0 1)).toReal
          let errorBound := 4 * secondErrorConstant / weight j (v * γ 1) *
            Real.exp (4 * firstErrorConstant * Vzero / ‖u‖) * Vn / ‖u‖ ^ (2 * n + 1)
          ‖ε (γ 1)‖ / modulus k (v * γ 1) ≤ errorBound ∧
            ‖deriv ε (γ 1)‖ / (‖u‖ ^ (2 / 3 : ℝ) * derivativeModulus k (v * γ 1)) ≤
              errorBound := by
  sorry

end DLMF.AsymptoticApproximations
