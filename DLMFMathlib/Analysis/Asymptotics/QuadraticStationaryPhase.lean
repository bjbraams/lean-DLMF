/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Quadratic stationary phase on a finite interval

The endpoint quadratic Fresnel estimate and its smooth-amplitude version are Duverney,
*An Introduction to Hypergeometric Functions*, Appendix D, Lemmas D.1 and D.2.
The stationary-point estimate is Theorem 7.4, equation (7.32). All remainders are
`O(x⁻¹)` as the real frequency tends to positive infinity.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real Asymptotics ContDiff

namespace Asymptotics

/-- The finite-endpoint Fresnel asymptotic. Duverney Appendix D, Lemma D.1,
equation (D.1), synopsis DU-D.01. -/
theorem isBigO_integral_exp_neg_I_mul_sq {A : ℝ} (hA : 0 < A) :
    (fun x : ℝ => (∫ u in (0 : ℝ)..A, exp (-I * x * u ^ 2)) -
      exp (-I * π / 4) * (Real.sqrt π / (2 * Real.sqrt x))) =O[atTop]
        (fun x : ℝ => (x : ℂ)⁻¹) := by
  sorry

/-- Smooth amplitudes at a quadratic endpoint.
Duverney Appendix D, Lemma D.2, equation (D.3), synopsis DU-D.02.
Complex amplitudes give a stronger form of the book's real-amplitude statement. -/
theorem isBigO_integral_mul_exp_neg_I_mul_sq {A : ℝ} (hA : 0 < A)
    {k : ℝ → ℂ} (hk : ContDiffOn ℝ ∞ k (Icc 0 A)) :
    (fun x : ℝ => (∫ u in (0 : ℝ)..A, k u * exp (-I * x * u ^ 2)) -
      k 0 * exp (-I * π / 4) * (Real.sqrt π / (2 * Real.sqrt x))) =O[atTop]
        (fun x : ℝ => (x : ℂ)⁻¹) := by
  sorry

/-- Stationary phase at a single nondegenerate maximum.
Duverney Chapter 7, Theorem 7.4, equation (7.32), synopsis DU-7.07. -/
theorem isBigO_integral_exp_mul_phase_of_maximum {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) {g : ℝ → ℂ} {h : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Icc a b)) (hh : ContDiffOn ℝ ∞ h (Icc a b))
    (hleft : ∀ t ∈ Ico a t₀, 0 < deriv h t)
    (hright : ∀ t ∈ Ioc t₀ b, deriv h t < 0)
    (hsecond : iteratedDeriv 2 h t₀ < 0) :
    (fun x : ℝ => (∫ t in a..b, g t * exp (I * x * h t)) -
      g t₀ * exp (I * (x * h t₀ - π / 4)) *
        Real.sqrt (-2 * π / (x * iteratedDeriv 2 h t₀))) =O[atTop]
          (fun x : ℝ => (x : ℂ)⁻¹) := by
  sorry

end Asymptotics
