/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TurningPointCoefficients
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import Mathlib.Analysis.BoundedVariation

/-!
# Global bounds for analytic turning-point coefficients

The clearance of the two domain boundaries scales as `abs(zeta)^(-1/2)`.
The fixed inner disc supplies uniform control through the turning point, while
weighted joining paths supply bounds at infinity. The square-root variation
corollary chooses paths with controlled passage through that inner disc.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
Theorem 9.2 and its corollary, p. 419.
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace ODE

/-- All six bounds have one constant per order independent of both parameter and
phase point, with the source's exact powers. Olver, Chapter 11,
Theorem 9.2, p. 419. -/
theorem exists_uniform_turningPoint_coefficient_bounds
    {ι : Type*} (ψ : ι → ℂ → ℂ) (A B : ι → ℕ → ℂ → ℂ)
    (D Γ : ι → Set ℂ) (a : ι → ℂ) (γ : ι → ℂ → ℝ → ℂ)
    {k ρ d L : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) (hd : 0 < d) (hL : 0 ≤ L)
    (initialBound : ℕ → ℝ) (hinitialBound : ∀ s, 0 ≤ initialBound s)
    (hD : ∀ i, IsOpen (D i)) (hΓopen : ∀ i, IsOpen (Γ i))
    (hΓ : ∀ i, Γ i ⊆ D i) (ha : ∀ i, a i ∈ Γ i)
    (hdisc : ∀ i, Metric.closedBall 0 d ⊆ Γ i)
    (hsequence : ∀ i, IsTurningPointCoefficientSequence (ψ i) (A i) (B i) (D i))
    (hclearance : ∀ i zB, zB ∈ frontier (Γ i) → ∀ w ∈ frontier (D i),
      d * ‖zB‖ ^ (-1 / 2 : ℝ) ≤ dist zB w)
    (hψ : ∀ i z, z ∈ D i → ‖ψ i z‖ ≤ k / (1 + ‖z‖ ^ (1 / 2 + ρ)))
    (hinitial : ∀ s i, ‖A i s (a i)‖ ≤ initialBound s)
    (hpaths : ∀ i z, z ∈ Γ i →
      TauCeti.IsPiecewiseC1On (γ i z) 0 1 ∧ γ i z 0 = a i ∧ γ i z 1 = z ∧
        γ i z '' Icc 0 1 ⊆ Γ i ∧
        (∫ t : ℝ in 0..1, ‖deriv (γ i z) t‖ /
          (1 + ‖γ i z t‖ ^ (1 + min ρ (3 / 2)))) ≤ L)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i z, z ∈ Γ i →
      ‖A i s z‖ ≤ C ∧
      ‖deriv (A i s) z‖ ≤ C / (1 + ‖z‖ ^ (1 + min ρ (3 / 2))) ∧
      ‖deriv (deriv (A i s)) z‖ ≤ C / (1 + ‖z‖ ^ (1 / 2 + min ρ (3 / 2))) ∧
      ‖B i s z‖ ≤ C / (1 + ‖z‖ ^ (1 / 2 : ℝ)) ∧
      ‖deriv (B i s) z‖ ≤ C / (1 + ‖z‖ ^ (3 / 2 : ℝ)) ∧
      ‖deriv (deriv (B i s)) z‖ ≤ C / (1 + ‖z‖ ^ (1 + min ρ (3 / 2))) := by
  sorry

/-- The joining paths and continuous square roots can be selected with uniformly
bounded variations of `sqrt(zeta)*B_s` for every fixed order. Selecting controlled
arcs inside the fixed inner disc supplies the local square-root variation bound.
Olver, Chapter 11, corollary to Theorem 9.2, p. 419. -/
theorem exists_uniform_turningPoint_coefficient_variation_paths
    {ι : Type*} (ψ : ι → ℂ → ℂ) (A B : ι → ℕ → ℂ → ℂ)
    (D Γ : ι → Set ℂ) (a : ι → ℂ) (γ : ι → ℂ → ℝ → ℂ)
    {k ρ d L : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) (hd : 0 < d) (hL : 0 ≤ L)
    (initialBound : ℕ → ℝ) (hinitialBound : ∀ s, 0 ≤ initialBound s)
    (hD : ∀ i, IsOpen (D i)) (hΓopen : ∀ i, IsOpen (Γ i))
    (hΓ : ∀ i, Γ i ⊆ D i) (ha : ∀ i, a i ∈ Γ i)
    (hdisc : ∀ i, Metric.closedBall 0 d ⊆ Γ i)
    (hsequence : ∀ i, IsTurningPointCoefficientSequence (ψ i) (A i) (B i) (D i))
    (hclearance : ∀ i zB, zB ∈ frontier (Γ i) → ∀ w ∈ frontier (D i),
      d * ‖zB‖ ^ (-1 / 2 : ℝ) ≤ dist zB w)
    (hψ : ∀ i z, z ∈ D i → ‖ψ i z‖ ≤ k / (1 + ‖z‖ ^ (1 / 2 + ρ)))
    (hinitial : ∀ s i, ‖A i s (a i)‖ ≤ initialBound s)
    (hpaths : ∀ i z, z ∈ Γ i →
      TauCeti.IsPiecewiseC1On (γ i z) 0 1 ∧ γ i z 0 = a i ∧ γ i z 1 = z ∧
        γ i z '' Icc 0 1 ⊆ Γ i ∧
        (∫ t : ℝ in 0..1, ‖deriv (γ i z) t‖ /
          (1 + ‖γ i z t‖ ^ (1 + min ρ (3 / 2)))) ≤ L)
    :
    ∃ path root : ι → ℂ → ℝ → ℂ,
      (∀ i z, z ∈ Γ i → TauCeti.IsPiecewiseC1On (path i z) 0 1 ∧
        path i z 0 = a i ∧ path i z 1 = z ∧ path i z '' Icc 0 1 ⊆ Γ i ∧
        ContinuousOn (root i z) (Icc 0 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, root i z t ^ 2 = path i z t) ∧
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i z, z ∈ Γ i →
        BoundedVariationOn (fun t => root i z t * B i s (path i z t)) (Icc 0 1) ∧
          (eVariationOn (fun t => root i z t * B i s (path i z t)) (Icc 0 1)).toReal ≤ C := by
  sorry

end ODE
