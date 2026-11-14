/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.SingularFourierRemainders
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Leading stationary-endpoint asymptotic with finite variation tails

Olver, *Asymptotics and Special Functions*, Chapter 3, Theorem 13.1,
pp. 100–102, synopsis O-3.14. Only two differentiated phase equivalents and
one differentiated amplitude equivalent are required. The right endpoint may be infinite.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Complex Asymptotics
open scoped Topology ENNReal

namespace Asymptotics

/-- The leading oscillatory endpoint term under the source's weak regularity and variation
hypotheses. Zero differentiated leading coefficients are expressed as limits to zero, so
exponents equal to one cause no false nonzero equivalent. Olver, Chapter 3,
Theorem 13.1, synopsis O-3.14. -/
theorem exists_stationaryEndpoint_leading_limit {a μ lam P : ℝ} {b : EReal} {Q : ℂ}
    (hab : (a : EReal) < b) (hμ : 0 < μ) (hlam : 0 < lam) (hlamμ : lam < μ)
    (hP : 0 < P) (hQ : Q ≠ 0) {p : ℝ → ℝ} {q : ℝ → ℂ}
    (hp : ContDiffOn ℝ 1 p {t | a < t ∧ (t : EReal) < b})
    (hq : ContinuousOn q {t | a < t ∧ (t : EReal) < b})
    (hpositive : ∀ t, a < t → (t : EReal) < b → 0 < deriv p t)
    (singular : Finset ℝ)
    (hpp : ContDiffOn ℝ 2 p ({t | a < t ∧ (t : EReal) < b} \ (singular : Set ℝ)))
    (hqp : ContDiffOn ℝ 1 q ({t | a < t ∧ (t : EReal) < b} \ (singular : Set ℝ)))
    (hp₀ : Tendsto (fun t => (p t - p a) / (t - a) ^ μ) (𝓝[>] a) (𝓝 P))
    (hp₁ : Tendsto (fun t => deriv p t / (t - a) ^ (μ - 1))
      (𝓝[>] a) (𝓝 (μ * P)))
    (hp₂ : Tendsto (fun t => iteratedDeriv 2 p t / (t - a) ^ (μ - 2))
      (𝓝[>] a) (𝓝 (μ * (μ - 1) * P)))
    (hq₀ : Tendsto (fun t => q t / ((t - a) ^ (lam - 1) : ℝ)) (𝓝[>] a) (𝓝 Q))
    (hq₁ : Tendsto (fun t => deriv q t / ((t - a) ^ (lam - 2) : ℝ))
      (𝓝[>] a) (𝓝 ((lam - 1 : ℝ) * Q)))
    (hvar : ∀ k : ℝ, a < k → (k : EReal) < b →
      BoundedVariationOn (fun t => q t / (deriv p t : ℝ)) {t | k ≤ t ∧ (t : EReal) < b})
    (hend : (∃ pb : ℝ, Tendsto p (comap (fun t : ℝ => (t : EReal)) (𝓝[<] b)) (𝓝 pb)) ∨
      (Tendsto p (comap (fun t : ℝ => (t : EReal)) (𝓝[<] b)) atTop ∧
        Tendsto (fun t => q t / (deriv p t : ℝ))
          (comap (fun t : ℝ => (t : EReal)) (𝓝[<] b)) (𝓝 0))) :
    ∃ F : ℝ → ℂ,
      (∀ x : ℝ, 0 < x → Tendsto (fun T : ℝ =>
        ∫ t in a..T, exp (I * x * p t) * q t)
          (comap (fun t : ℝ => (t : EReal)) (𝓝[<] b)) (𝓝 (F x))) ∧
      Tendsto (fun x : ℝ => ((x ^ (lam / μ) : ℝ) : ℂ) * exp (-I * x * p a) * F x)
        atTop (𝓝 (Q * Real.Gamma (lam / μ) * exp (I * Real.pi * lam / (2 * μ)) /
          ((μ * P ^ (lam / μ) : ℝ) : ℂ))) := by
  sorry

end Asymptotics
