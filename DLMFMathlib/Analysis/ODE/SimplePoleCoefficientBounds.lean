/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.SimplePoleCoefficients
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import Mathlib.Analysis.BoundedVariation

/-!
# Global bounds for analytic simple-pole coefficients

The clearance of the two domain boundaries scales as `abs(zeta)^(1/2)`.
The fixed inner disc supplies uniform control through the simple pole, while
weighted joining paths supply bounds at infinity. The recurrences
retain all removable values at the simple pole.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
Theorem 11.1, pp. 462–463.
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace ODE

/-- All six bounds have one constant per order independent of both parameter and
phase point, with the source's exact powers. Olver, Chapter 12,
Theorem 11.1, pp. 462–463. -/
theorem exists_uniform_simplePole_coefficient_bounds
    {ι : Type*} (ψ : ι → ℂ → ℂ) (A B : ι → ℕ → ℂ → ℂ)
    (D Γ : ι → Set ℂ) (ν : ι → ℝ) (γ : ι → ℂ → ℝ → ℂ)
    {k ρ d L N : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) (hd : 0 < d) (hL : 0 ≤ L)
    (hν : ∀ i, 0 ≤ ν i ∧ ν i ≤ N)
    (initialBound : ℕ → ℝ) (hinitialBound : ∀ s, 0 ≤ initialBound s)
    (hD : ∀ i, IsOpen (D i)) (hΓopen : ∀ i, IsOpen (Γ i))
    (hΓ : ∀ i, Γ i ⊆ D i)
    (hdisc : ∀ i, Metric.closedBall 0 d ⊆ Γ i)
    (hsequence : ∀ i, IsSimplePoleCoefficientSequence (ψ i) (ν i) (A i) (B i) (D i))
    (hclearance : ∀ i zB, zB ∈ frontier (Γ i) → ∀ w ∈ frontier (D i),
      d * ‖zB‖ ^ (1 / 2 : ℝ) ≤ dist zB w)
    (hψ : ∀ i z, z ∈ D i → ‖ψ i z‖ ≤ k / (1 + ‖z‖ ^ (1 / 2 + ρ)))
    (hinitial : ∀ s i, ‖A i s 0‖ ≤ initialBound s)
    (hpaths : ∀ i z, z ∈ Γ i →
      TauCeti.IsPiecewiseC1On (γ i z) 0 1 ∧ γ i z 0 = 0 ∧ γ i z 1 = z ∧
        γ i z '' Icc 0 1 ⊆ Γ i ∧
        (∫ t : ℝ in 0..1, ‖deriv (γ i z) t‖ /
          (1 + ‖γ i z t‖ ^ (1 + min ρ (1 / 2)))) ≤ L)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i z, z ∈ Γ i →
      ‖A i s z‖ ≤ C ∧
      ‖deriv (A i s) z‖ ≤ C / (1 + ‖z‖ ^ (1 + min ρ (1 / 2))) ∧
      ‖deriv (deriv (A i s)) z‖ ≤ C / (1 + ‖z‖ ^ (3 / 2 + min ρ (1 / 2))) ∧
      ‖B i s z‖ ≤ C / (1 + ‖z‖ ^ (1 / 2 : ℝ)) ∧
      ‖deriv (B i s) z‖ ≤ C / (1 + ‖z‖ ^ (3 / 2 : ℝ)) ∧
      ‖deriv (deriv (B i s)) z‖ ≤ C / (1 + ‖z‖ ^ (2 + min ρ (1 / 2))) := by
  sorry


end ODE
