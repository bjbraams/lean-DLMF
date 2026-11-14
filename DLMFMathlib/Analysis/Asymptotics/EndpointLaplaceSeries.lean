/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.LaplaceCoefficients
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Endpoint Laplace expansions with complex amplitude exponent

Olver, *Asymptotics and Special Functions*, Chapter 3, Theorem 8.1,
pp. 85–87, synopsis O-3.07. The coefficients are the finite formal-power
coefficients rather than an unspecified inverse-substitution sequence.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Asymptotics Finset PowerSeries
open scoped Topology

namespace Asymptotics

/-- A separated endpoint minimum with differentiable phase expansion gives the full Laplace
expansion, for arbitrary complex amplitude exponent of positive real part. Olver,
Chapter 3, Theorem 8.1, synopsis O-3.07. The real phase is normalized to vanish at the
endpoint; an arbitrary phase value is restored by multiplying by its exponential. -/
theorem hasAsymptoticExpansion_integral_exp_of_endpoint_series
    {S : Set ℝ} (hS : MeasurableSet S) (hpositive : S ⊆ Ioi 0)
    {p : ℝ → ℝ} {q : ℝ → ℂ} {μ δ x₀ : ℝ} {lam : ℂ}
    (hμ : 0 < μ) (hlam : 0 < lam.re) (hδ : 0 < δ) (hnear : Ioo 0 δ ⊆ S)
    (hp : AEStronglyMeasurable p (volume.restrict S))
    (hdiff : DifferentiableOn ℝ p (Ioo 0 δ))
    (hderiv : ContinuousOn (deriv p) (Ioo 0 δ))
    (hq : ContinuousOn q (Ioo 0 δ)) (P : ℝ⟦X⟧) (Q : ℂ⟦X⟧)
    (hP : 0 < constantCoeff P)
    (hphase : HasAsymptoticExpansion (𝓝[>] (0 : ℝ))
      (fun n t => t ^ ((n : ℝ) + μ)) (fun n => coeff n P) p)
    (hphase' : HasAsymptoticExpansion (𝓝[>] (0 : ℝ))
      (fun n t => t ^ ((n : ℝ) + μ - 1))
      (fun n => ((n : ℝ) + μ) * coeff n P) (deriv p))
    (hamplitude : HasAsymptoticExpansion (𝓝[>] (0 : ℝ))
      (fun n t => (t : ℂ) ^ ((n : ℂ) + lam - 1)) (fun n => coeff n Q) q)
    (hgap : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ t ∈ S, ε ≤ t → η ≤ p t)
    (hi : IntegrableOn (fun t => Real.exp (-x₀ * p t) • q t) S) :
    HasAsymptoticExpansion atTop
      (fun n (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + lam) / μ))
      (fun n => Complex.Gamma (((n : ℂ) + lam) / μ) / μ *
        coeff n (Q * logarithmicPower (PowerSeries.map Complex.ofRealHom P)
          (Real.log (constantCoeff P)) (-((n : ℂ) + lam) / μ)))
      (fun x => ∫ t in S, Real.exp (-x * p t) • q t) := by
  sorry

/-- The leading endpoint Laplace limit needs only differentiable equivalents, not a complete
asymptotic series. Olver, Chapter 3, Theorem 7.1, pp. 80–83, synopsis O-3.05. -/
theorem tendsto_rpow_mul_integral_exp_of_endpoint_equivalents
    {S : Set ℝ} (hS : MeasurableSet S) (hpositive : S ⊆ Ioi 0)
    {p : ℝ → ℝ} {q : ℝ → ℂ} {μ lam P δ x₀ : ℝ} {Q : ℂ}
    (hμ : 0 < μ) (hlam : 0 < lam) (hP : 0 < P) (hδ : 0 < δ)
    (hnear : Ioo 0 δ ⊆ S) (hp : AEStronglyMeasurable p (volume.restrict S))
    (hdiff : DifferentiableOn ℝ p (Ioo 0 δ))
    (hderiv : ContinuousOn (deriv p) (Ioo 0 δ)) (hq : ContinuousOn q (Ioo 0 δ))
    (hphase : Tendsto (fun t => p t / t ^ μ) (𝓝[>] 0) (𝓝 P))
    (hphase' : Tendsto (fun t => deriv p t / t ^ (μ - 1)) (𝓝[>] 0) (𝓝 (μ * P)))
    (hamplitude : Tendsto (fun t => q t / (t ^ (lam - 1) : ℝ)) (𝓝[>] 0) (𝓝 Q))
    (hgap : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ t ∈ S, ε ≤ t → η ≤ p t)
    (hi : IntegrableOn (fun t => Real.exp (-x₀ * p t) • q t) S) :
    Tendsto (fun x : ℝ => ((x ^ (lam / μ) : ℝ) : ℂ) *
      ∫ t in S, Real.exp (-x * p t) • q t) atTop
        (𝓝 (Q * Real.Gamma (lam / μ) / ((μ * P ^ (lam / μ) : ℝ) : ℂ))) := by
  sorry

end Asymptotics
