/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TurningPointCoefficients
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Formal forced Airy expansions with removable coefficient quotients

The zero values of the `A` coefficients are fixed by divisibility of each `G`
numerator, not by arbitrary integration constants. This is a formal construction;
no convergence of the parameter series or uniform remainder theorem is asserted.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
§12, (12.01)–(12.06), pp. 429–431.
-/

@[expose] public noncomputable section

open Set Finset

namespace ODE

/-- Analytic forced Airy coefficients. Multiplication by `z` records every
removable quotient, including its divisibility condition at zero.
Olver, Chapter 11, (12.03)–(12.06), pp. 430–431. -/
def IsForcedTurningPointCoefficientSequence (ψ ω : ℂ → ℂ)
    (A B G : ℕ → ℂ → ℂ) (D : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ ψ D ∧ AnalyticOnNhd ℂ ω D ∧
    (∀ n, AnalyticOnNhd ℂ (A n) D ∧ AnalyticOnNhd ℂ (B n) D ∧
      AnalyticOnNhd ℂ (G n) D) ∧
    (∀ z ∈ D, A 0 z = ω 0) ∧
    (∀ n z, z ∈ D →
      2 * z * deriv (B n) z + B n z = ψ z * A n z - deriv (deriv (A n)) z) ∧
    (∀ n z, z ∈ D →
      2 * deriv (A (n + 1)) z = ψ z * B n z - deriv (deriv (B n)) z) ∧
    (∀ z ∈ D, z * G 0 z = A 0 z - ω z) ∧
    ∀ n z, z ∈ D → z * G (n + 1) z =
      A (n + 1) z + 2 * deriv (B n) z + deriv (deriv (G n)) z - ψ z * G n z

/-- The analytic and differential conditions defining forced Airy coefficients. -/
theorem isForcedTurningPointCoefficientSequence_iff (ψ ω : ℂ → ℂ)
    (A B G : ℕ → ℂ → ℂ) (D : Set ℂ) :
    IsForcedTurningPointCoefficientSequence ψ ω A B G D ↔
      AnalyticOnNhd ℂ ψ D ∧ AnalyticOnNhd ℂ ω D ∧
        (∀ n, AnalyticOnNhd ℂ (A n) D ∧ AnalyticOnNhd ℂ (B n) D ∧
          AnalyticOnNhd ℂ (G n) D) ∧ (∀ z ∈ D, A 0 z = ω 0) ∧
        (∀ n z, z ∈ D →
          2 * z * deriv (B n) z + B n z = ψ z * A n z - deriv (deriv (A n)) z) ∧
        (∀ n z, z ∈ D →
          2 * deriv (A (n + 1)) z = ψ z * B n z - deriv (deriv (B n)) z) ∧
        (∀ z ∈ D, z * G 0 z = A 0 z - ω z) ∧
        ∀ n z, z ∈ D → z * G (n + 1) z =
          A (n + 1) z + 2 * deriv (B n) z + deriv (deriv (G n)) z - ψ z * G n z := Iff.rfl

/-- Divisibility determines the integration constant of the next `A`.
Olver, Chapter 11, §12, p. 431. -/
theorem IsForcedTurningPointCoefficientSequence.A_succ_zero
    {ψ ω : ℂ → ℂ} {A B G : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : IsForcedTurningPointCoefficientSequence ψ ω A B G D) (hzero : 0 ∈ D) (n : ℕ) :
    A (n + 1) 0 = -2 * deriv (B n) 0 - deriv (deriv (G n)) 0 + ψ 0 * G n 0 := by
  have heq := h.2.2.2.2.2.2.2 n 0 hzero
  simp only [zero_mul] at heq
  linear_combination -heq

/-- All quotients extend analytically, and the normalized coefficient sequences
exist throughout a simply connected domain containing zero. The first removable
quotient is the negative divided difference of `omega`.
Olver, Chapter 11, §12, pp. 430–431. -/
theorem exists_forcedTurningPointCoefficientSequence {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hzero : 0 ∈ D)
    {ψ ω : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ D) (hω : AnalyticOnNhd ℂ ω D) :
    ∃ A B G : ℕ → ℂ → ℂ, IsForcedTurningPointCoefficientSequence ψ ω A B G D ∧
      ∀ z ∈ D, G 0 z = -dslope ω 0 z := by
  sorry

/-- The actual finite forced Airy sum, using any normalized particular solution
`Wi''-z*Wi=1`. Olver, Chapter 11, (12.02), p. 430. -/
def forcedTurningPointPartialSum (A B G : ℕ → ℂ → ℂ) (Wi : ℂ → ℂ)
    (u v : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  v / u ^ 2 * turningPointPartialSum A B Wi u v n z +
    ∑ s ∈ range n, G s z / u ^ (2 * s + 2)

/-- The defining compound particular sum. -/
theorem forcedTurningPointPartialSum_def (A B G : ℕ → ℂ → ℂ) (Wi : ℂ → ℂ)
    (u v : ℂ) (n : ℕ) (z : ℂ) : forcedTurningPointPartialSum A B G Wi u v n z =
    v / u ^ 2 * turningPointPartialSum A B Wi u v n z +
      ∑ s ∈ range n, G s z / u ^ (2 * s + 2) := rfl

/-- Its exact residual is supported at the next formal order, including both
forcing contributions from the normalized particular Airy function.
Olver, Chapter 11, §12, pp. 430–431. -/
theorem forcedTurningPointPartialSum_residual {D : Set ℂ} (hD : IsOpen D)
    {ψ ω : ℂ → ℂ} {A B G : ℕ → ℂ → ℂ}
    (hseq : IsForcedTurningPointCoefficientSequence ψ ω A B G D)
    {Wi : ℂ → ℂ} (hWi : AnalyticOnNhd ℂ Wi univ)
    (hforced : ∀ z, deriv (deriv Wi) z - z * Wi z = 1)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ^ 3 = u ^ 2) (n : ℕ) {z : ℂ} (hz : z ∈ D) :
    deriv (deriv (forcedTurningPointPartialSum A B G Wi u v n)) z -
      (u ^ 2 * z + ψ z) * forcedTurningPointPartialSum A B G Wi u v n z - ω z =
        (z * G n z - v / u ^ 2 * Wi (v * z) *
          (2 * z * deriv (B n) z + B n z)) / u ^ (2 * n) := by
  sorry

end ODE
