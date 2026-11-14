/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TransitionCoordinates

/-!
# Formal coefficients for power comparison equations

The two recurrences are the exact coefficients of `P*A+P'*B/u^2` when
`P''=((u^2+b)*z^m+c/z^2)*P`. Analyticity at zero is retained as a genuine
constraint, and two explicitly permitted families are acquired with their
removable divisibility. Source: Olver, *Asymptotics and Special Functions*,
Chapter 12, (14.14)–(14.19), pp. 477–478.
-/

@[expose] public noncomputable section

open Complex Set

namespace ODE

/-- Analytic formal power-comparison coefficients. The differential identities
are imposed off zero, where the meromorphic comparison potential is defined;
the coefficient functions themselves are analytic at the transition point.
Olver, Chapter 12, §14, p. 477. -/
def IsPowerTransitionCoefficientSequence (φ : ℂ → ℂ) (m : ℤ) (b c : ℂ)
    (A B : ℕ → ℂ → ℂ) (D : Set ℂ) : Prop :=
  (∀ s, AnalyticOnNhd ℂ (A s) D ∧ AnalyticOnNhd ℂ (B s) D) ∧
    (∀ z ∈ D, A 0 z = 1) ∧
    (∀ s z, z ∈ D → z ≠ 0 →
      2 * deriv (A (s + 1)) z = φ z * B s z - deriv (deriv (B s)) z) ∧
    ∀ s z, z ∈ D → z ≠ 0 →
      let previous := if s = 0 then (fun _ : ℂ => 0) else B (s - 1)
      2 * z ^ m * deriv (B s) z + (m : ℂ) * z ^ (m - 1) * B s z =
        φ z * A s z - deriv (deriv (A s)) z -
          2 * (b * z ^ m + c / z ^ 2) * deriv previous z -
          (b * m * z ^ (m - 1) - 2 * c / z ^ 3) * previous z

/-- The exact two power-comparison recurrences and analytic coefficients. -/
theorem isPowerTransitionCoefficientSequence_iff (φ : ℂ → ℂ) (m : ℤ) (b c : ℂ)
    (A B : ℕ → ℂ → ℂ) (D : Set ℂ) :
    IsPowerTransitionCoefficientSequence φ m b c A B D ↔
      (∀ s, AnalyticOnNhd ℂ (A s) D ∧ AnalyticOnNhd ℂ (B s) D) ∧
        (∀ z ∈ D, A 0 z = 1) ∧
        (∀ s z, z ∈ D → z ≠ 0 →
          2 * deriv (A (s + 1)) z = φ z * B s z - deriv (deriv (B s)) z) ∧
        ∀ s z, z ∈ D → z ≠ 0 →
          let previous := if s = 0 then (fun _ : ℂ => 0) else B (s - 1)
          2 * z ^ m * deriv (B s) z + (m : ℂ) * z ^ (m - 1) * B s z =
            φ z * A s z - deriv (deriv (A s)) z -
              2 * (b * z ^ m + c / z ^ 2) * deriv previous z -
              (b * m * z ^ (m - 1) - 2 * c / z ^ 3) * previous z := Iff.rfl

/-- Every analytic lower numerator of the permitted higher-pole order has
analytic formal coefficients; each `B_s` has the stated zero multiplicity.
The integer division is the floor appearing in the source's square brackets.
Olver, Chapter 12, (14.16), p. 477. -/
theorem exists_higherPole_powerTransition_coefficients
    {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ 0) {M : ℕ} (hM : 3 ≤ M) (b c : ℂ)
    (constants : ℕ → ℂ) (hconstants : constants 0 = 1) :
    ∃ (r : ℝ) (A B H : ℕ → ℂ → ℂ), 0 < r ∧
      IsPowerTransitionCoefficientSequence (fun z => ψ z / z ^ ((M + 1) / 2))
        (-(M : ℤ)) b c A B (Metric.ball 0 r) ∧
      (∀ s, A s 0 = constants s ∧ AnalyticOnNhd ℂ (H s) (Metric.ball 0 r)) ∧
      ∀ s z, z ∈ Metric.ball (0 : ℂ) r → B s z = z ^ (M / 2 + 1) * H s z := by
  sorry

/-- The permitted higher-zero family has coefficient forms
`A_s=a_s(z^(m+2)),B_s=z*b_s(z^(m+2))`; all apparent denominators are removable.
Olver, Chapter 12, (14.17), p. 477. -/
theorem exists_higherZero_powerTransition_coefficients
    {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ 0) (m : ℕ) (c : ℂ)
    (constants : ℕ → ℂ) (hconstants : constants 0 = 1) :
    ∃ (r : ℝ) (A B a b : ℕ → ℂ → ℂ), 0 < r ∧
      IsPowerTransitionCoefficientSequence (fun z => z ^ m * ψ (z ^ (m + 2)))
        m 0 c A B (Metric.ball 0 r) ∧
      (∀ s, A s 0 = constants s ∧ AnalyticAt ℂ (a s) 0 ∧ AnalyticAt ℂ (b s) 0) ∧
      ∀ s z, z ∈ Metric.ball (0 : ℂ) r →
        A s z = a s (z ^ (m + 2)) ∧ B s z = z * b s (z ^ (m + 2)) := by
  sorry

end ODE
