/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Laplace integrals with a parameter-dependent perturbation

Olver, *Asymptotics and Special Functions*, Chapter 9, Theorems 2.1 and 4.1,
pp. 326–333: subcritical perturbations retain a Gamma leading term, whereas at the
critical scaling the leading coefficient is a convergent Faxen integral. The
hypotheses and the explicit power of the error are retained.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology Real Asymptotics

namespace Asymptotics

/-- A subcritical parameter perturbation of an endpoint Laplace integral preserves
its leading Gamma term with an explicit relative error power. Olver, Chapter 9,
Theorem 2.1, pp. 326–328. This is the finite-interval theorem; independent tails
are not included in the conclusion. -/
theorem isBigO_perturbed_laplace_endpoint
    {k X P μ μ₁ lam lam₁ ν α β R Q₁ : ℝ} {Q : ℂ}
    {p p' : ℝ → ℝ} {q r : ℝ → ℝ → ℂ}
    (hk : 0 < k) (hX : 0 < X) (hP : 0 < P) (hμ : 0 < μ) (hμ₁ : μ < μ₁)
    (hlam : 0 < lam) (hlam₁ : 0 < lam₁) (hν : 0 ≤ ν) (hQ : Q ≠ 0)
    (hα : α < min 1 (ν / μ)) (hβ : β < (lam₁ - lam) / μ)
    (hR : 0 ≤ R) (hQ₁ : 0 ≤ Q₁) (hp : ContinuousOn p (Icc 0 k))
    (hd : ∀ t ∈ Ioc 0 k, HasDerivAt p (p' t) t)
    (hpos : ∀ t ∈ Ioc 0 k, 0 < p' t)
    (hphase : (fun t => p t - p 0 - P * t ^ μ) =O[𝓝[>] 0] (fun t => t ^ μ₁))
    (hphase' : (fun t => p' t - μ * P * t ^ (μ - 1))
      =O[𝓝[>] 0] (fun t => t ^ (μ₁ - 1)))
    (hq : ∀ x, X ≤ x → ContinuousOn (q x) (Ioc 0 k))
    (hr : ∀ x, X ≤ x → ContinuousOn (r x) (Ioc 0 k))
    (hrbound : ∀ x, X ≤ x → ∀ t ∈ Ioc 0 k, ‖r x t‖ ≤ R * x ^ α * t ^ ν)
    (hqbound : ∀ x, X ≤ x → ∀ t ∈ Ioc 0 k,
      ‖q x t - Q * (t ^ (lam - 1) : ℝ)‖ ≤ Q₁ * x ^ β * t ^ (lam₁ - 1)) :
    (fun x =>
      (∫ t in (0 : ℝ)..k, Complex.exp (-(x * p t : ℝ) + r x t) * q x t) /
        (Q * (Real.Gamma (lam / μ) * Real.exp (-x * p 0) /
          (μ * (P * x) ^ (lam / μ)) : ℝ)) - 1)
      =O[atTop] (fun x => x ^ (-min (μ₁ - μ) (min (ν - μ * α)
        (lam₁ - lam - μ * β)) / μ)) := by
  sorry

/-- A nonpositive real perturbation has no positive exponential tail, so the
subcritical endpoint estimate does not need the additional restriction `alpha < 1`.
Olver, Chapter 9, Theorem 2.1, p. 328. -/
theorem isBigO_perturbed_laplace_endpoint_of_nonpos
    {k X P μ μ₁ lam lam₁ ν α β R Q₁ : ℝ} {Q : ℂ}
    {p p' : ℝ → ℝ} {q : ℝ → ℝ → ℂ} {r : ℝ → ℝ → ℝ}
    (hk : 0 < k) (hX : 0 < X) (hP : 0 < P) (hμ : 0 < μ) (hμ₁ : μ < μ₁)
    (hlam : 0 < lam) (hlam₁ : 0 < lam₁) (hν : 0 ≤ ν) (hQ : Q ≠ 0)
    (hα : α < ν / μ) (hβ : β < (lam₁ - lam) / μ)
    (hR : 0 ≤ R) (hQ₁ : 0 ≤ Q₁) (hp : ContinuousOn p (Icc 0 k))
    (hd : ∀ t ∈ Ioc 0 k, HasDerivAt p (p' t) t)
    (hpos : ∀ t ∈ Ioc 0 k, 0 < p' t)
    (hphase : (fun t => p t - p 0 - P * t ^ μ) =O[𝓝[>] 0] (fun t => t ^ μ₁))
    (hphase' : (fun t => p' t - μ * P * t ^ (μ - 1))
      =O[𝓝[>] 0] (fun t => t ^ (μ₁ - 1)))
    (hq : ∀ x, X ≤ x → ContinuousOn (q x) (Ioc 0 k))
    (hr : ∀ x, X ≤ x → ContinuousOn (r x) (Ioc 0 k))
    (hrnonpos : ∀ x, X ≤ x → ∀ t ∈ Ioc 0 k, r x t ≤ 0)
    (hrbound : ∀ x, X ≤ x → ∀ t ∈ Ioc 0 k, |r x t| ≤ R * x ^ α * t ^ ν)
    (hqbound : ∀ x, X ≤ x → ∀ t ∈ Ioc 0 k,
      ‖q x t - Q * (t ^ (lam - 1) : ℝ)‖ ≤ Q₁ * x ^ β * t ^ (lam₁ - 1)) :
    (fun x =>
      (∫ t in (0 : ℝ)..k, Complex.exp (-x * p t + r x t : ℝ) * q x t) /
        (Q * (Real.Gamma (lam / μ) * Real.exp (-x * p 0) /
          (μ * (P * x) ^ (lam / μ)) : ℝ)) - 1)
      =O[atTop] (fun x => x ^ (-min (μ₁ - μ) (min (ν - μ * α)
        (lam₁ - lam - μ * β)) / μ)) := by
  sorry

/-- At the critical perturbation scale the leading coefficient is a Faxen integral.
The error remains an absolute error after division by the common Laplace prefactor;
the Faxen coefficient is allowed to vanish. Olver, Chapter 9, Theorem 4.1, pp. 332–333. -/
theorem isBigO_critical_perturbed_laplace_endpoint
    {k P μ μ₁ lam lam₁ ν ν₁ : ℝ} {Q R : ℂ}
    {p p' : ℝ → ℝ} {q r : ℝ → ℂ}
    (hk : 0 < k) (hP : 0 < P) (hμ : 0 < μ) (hμ₁ : μ < μ₁)
    (hlam : 0 < lam) (hlam₁ : lam < lam₁) (hν : 0 ≤ ν) (hνμ : ν < μ)
    (hν₁ : ν < ν₁) (hQ : Q ≠ 0)
    (hp : ContinuousOn p (Icc 0 k))
    (hd : ∀ t ∈ Ioc 0 k, HasDerivAt p (p' t) t)
    (hpos : ∀ t ∈ Ioc 0 k, 0 < p' t)
    (hphase : (fun t => p t - p 0 - P * t ^ μ) =O[𝓝[>] 0] (fun t => t ^ μ₁))
    (hphase' : (fun t => p' t - μ * P * t ^ (μ - 1))
      =O[𝓝[>] 0] (fun t => t ^ (μ₁ - 1)))
    (hq : ContinuousOn q (Ioc 0 k)) (hr : ContinuousOn r (Ioc 0 k))
    (hqexp : (fun t => q t - Q * (t ^ (lam - 1) : ℝ))
      =O[𝓝[>] 0] (fun t => (t ^ (lam₁ - 1) : ℝ)))
    (hrexp : (fun t => r t - R * (t ^ ν : ℝ))
      =O[𝓝[>] 0] (fun t => (t ^ ν₁ : ℝ))) :
    (fun x =>
      (∫ t in (0 : ℝ)..k,
        Complex.exp (-(x * p t : ℝ) + (x ^ (ν / μ) : ℝ) * r t) * q t) /
        (Q * (Real.exp (-x * p 0) / (μ * (P * x) ^ (lam / μ)) : ℝ)) -
      ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(t : ℂ) + R / (P ^ (ν / μ) : ℝ) * (t ^ (ν / μ) : ℝ)) *
          (t ^ (lam / μ - 1) : ℝ))
      =O[atTop] (fun x => x ^ (-min (lam₁ - lam) (min (μ₁ - μ) (ν₁ - ν)) / μ)) := by
  sorry

end Asymptotics
