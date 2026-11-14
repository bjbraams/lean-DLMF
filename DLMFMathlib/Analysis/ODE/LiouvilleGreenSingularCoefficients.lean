/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreenExpansion
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Liouville–Green coefficients at meromorphic singularities

The coefficient recurrence is written in the original variable, using the
chosen branch `h=1/sqrt(f)`. Convergent local Laurent data, rather than only a
pointwise equivalent on one ray, control all derivatives in the recurrence.
Source: Olver, *Asymptotics and Special Functions*, Chapter 10, Theorem 4.1
and Exercise 4.1, p. 369.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Complex

/-- The original-variable LG coefficient recurrence, with `h=1/sqrt(f)`.
Olver, Chapter 10, (2.09)–(2.10), pp. 365–366. -/
def IsOriginalVariableLiouvilleGreenCoefficientSequence
    (h g : ℂ → ℂ) (A : ℕ → ℂ → ℂ) (D : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ h D ∧ AnalyticOnNhd ℂ g D ∧
    (∀ z ∈ D, h z ≠ 0) ∧ (∀ n, AnalyticOnNhd ℂ (A n) D) ∧
    (∀ z ∈ D, A 0 z = 1) ∧ ∀ n z, z ∈ D →
      2 * deriv (A (n + 1)) z =
        (g z * h z - deriv (deriv h) z / 2 + deriv h z ^ 2 / (4 * h z)) * A n z -
          deriv h z * deriv (A n) z - h z * deriv (deriv (A n)) z

/-- Analyticity, the leading coefficient, and the original-variable recurrence. -/
theorem isOriginalVariableLiouvilleGreenCoefficientSequence_iff
    (h g : ℂ → ℂ) (A : ℕ → ℂ → ℂ) (D : Set ℂ) :
    IsOriginalVariableLiouvilleGreenCoefficientSequence h g A D ↔
      AnalyticOnNhd ℂ h D ∧ AnalyticOnNhd ℂ g D ∧
        (∀ z ∈ D, h z ≠ 0) ∧ (∀ n, AnalyticOnNhd ℂ (A n) D) ∧
        (∀ z ∈ D, A 0 z = 1) ∧ ∀ n z, z ∈ D →
          2 * deriv (A (n + 1)) z =
            (g z * h z - deriv (deriv h) z / 2 + deriv h z ^ 2 / (4 * h z)) * A n z -
              deriv h z * deriv (A n) z - h z * deriv (deriv (A n)) z := Iff.rfl

/-- Constructor for original-variable LG coefficients. -/
theorem IsOriginalVariableLiouvilleGreenCoefficientSequence.mk
    {h g : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {D : Set ℂ}
    (hh : AnalyticOnNhd ℂ h D) (hg : AnalyticOnNhd ℂ g D)
    (hne : ∀ z ∈ D, h z ≠ 0) (hA : ∀ n, AnalyticOnNhd ℂ (A n) D)
    (hzero : ∀ z ∈ D, A 0 z = 1)
    (hrec : ∀ n z, z ∈ D → 2 * deriv (A (n + 1)) z =
      (g z * h z - deriv (deriv h) z / 2 + deriv h z ^ 2 / (4 * h z)) * A n z -
        deriv h z * deriv (A n) z - h z * deriv (deriv (A n)) z) :
    IsOriginalVariableLiouvilleGreenCoefficientSequence h g A D :=
  ⟨hh, hg, hne, hA, hzero, hrec⟩

/-- The phase-variable coefficient recurrence pulls back to the original
variable. Olver, Chapter 10, (2.08)–(2.10), pp. 365–366. -/
theorem IsComplexLiouvilleGreenCoefficientSequence.comp_phase
    {D E : Set ℂ} (hD : IsOpen D) {h g phase ψ : ℂ → ℂ}
    {A : ℕ → ℂ → ℂ} (hh : AnalyticOnNhd ℂ h D)
    (hg : AnalyticOnNhd ℂ g D) (hphase : AnalyticOnNhd ℂ phase D)
    (hne : ∀ z ∈ D, h z ≠ 0) (him : MapsTo phase D E)
    (hderiv : ∀ z ∈ D, deriv phase z = (h z)⁻¹)
    (hψ : ∀ z ∈ D, ψ (phase z) =
      g z * h z ^ 2 - h z * deriv (deriv h) z / 2 + deriv h z ^ 2 / 4)
    (hA : IsComplexLiouvilleGreenCoefficientSequence ψ A E) :
    IsOriginalVariableLiouvilleGreenCoefficientSequence h g (fun n => A n ∘ phase) D := by
  sorry

/-- Every coefficient has finite radial variation and a finite limit at a
higher pole. The Laurent numerators are analytic at the pole; `2*p<m+2`
is the strict pole-order condition. Olver, Chapter 10, Theorem 4.1(i), p. 369. -/
theorem boundedVariationOn_liouvilleGreenCoefficient_at_higherPole
    {F G h : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {z₀ ρ θ : ℂ} {r : ℝ} {m p : ℕ}
    (hr : 0 < r) (hρ : ρ ≠ 0) (hθ : ‖θ‖ = 1) (hcut : θ / ρ ∈ slitPlane)
    (hm : 2 < m) (hp : 2 * p < m + 2)
    (hF : AnalyticOnNhd ℂ F (Metric.ball z₀ r))
    (hG : AnalyticOnNhd ℂ G (Metric.ball z₀ r))
    (hFne : ∀ z ∈ Metric.ball z₀ r, F z ≠ 0)
    (hroot : ∀ z ∈ Metric.ball z₀ r, (z - z₀) / ρ ∈ slitPlane →
      h z ^ 2 * F z = (z - z₀) ^ m)
    (hA : IsOriginalVariableLiouvilleGreenCoefficientSequence h
      (fun z => G z / (z - z₀) ^ p) A
      {z | z ∈ Metric.ball z₀ r ∧ (z - z₀) / ρ ∈ slitPlane}) (n : ℕ) :
    BoundedVariationOn (fun t : ℝ => A n (z₀ + t * θ)) (Ioc 0 (r / 2)) ∧
      ∃ a : ℂ, Tendsto (fun t : ℝ => A n (z₀ + t * θ)) (𝓝[>] 0) (𝓝 a) := by
  sorry

/-- For a double pole with double-pole coefficient `-1/4`, every LG
coefficient extends analytically through the pole. Olver, Chapter 10,
Theorem 4.1(ii), p. 369. -/
theorem exists_analytic_extension_liouvilleGreenCoefficient_at_doublePole
    {F G h : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {z₀ ρ : ℂ} {r : ℝ}
    (hr : 0 < r) (hρ : ρ ≠ 0)
    (hF : AnalyticOnNhd ℂ F (Metric.ball z₀ r))
    (hG : AnalyticOnNhd ℂ G (Metric.ball z₀ r))
    (hFne : ∀ z ∈ Metric.ball z₀ r, F z ≠ 0) (hGzero : G z₀ = -1 / 4)
    (hroot : ∀ z ∈ Metric.ball z₀ r, (z - z₀) / ρ ∈ slitPlane →
      h z ^ 2 * F z = (z - z₀) ^ 2)
    (hA : IsOriginalVariableLiouvilleGreenCoefficientSequence h
      (fun z => G z / (z - z₀) ^ 2) A
      {z | z ∈ Metric.ball z₀ r ∧ (z - z₀) / ρ ∈ slitPlane}) (n : ℕ) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (Metric.ball z₀ r) ∧
      ∀ z ∈ Metric.ball z₀ r, (z - z₀) / ρ ∈ slitPlane → B z = A n z := by
  sorry

/-- Moving a constant from the double-pole numerator to the squared parameter
sets the remaining pole coefficient to `-1/4`. Olver, Chapter 10, §4.2, p. 369. -/
theorem liouvilleGreen_doublePole_parameter_shift (F G : ℂ → ℂ) (z₀ u z : ℂ)
    (hF : F z₀ ≠ 0) :
    let c := (G z₀ + 1 / 4) / F z₀
    u ^ 2 * F z + G z = (u ^ 2 + c) * F z + (G z - c * F z) ∧
      G z₀ - c * F z₀ = -1 / 4 := by
  dsimp only
  constructor
  · ring
  · field_simp [hF]
    ring

/-- Convergent Laurent expansions at infinity imply finite variation on every
fixed radial tail. The integer exponents may be negative. Olver, Chapter 10,
Exercise 4.1, p. 369, first case. -/
theorem boundedVariationOn_liouvilleGreenCoefficient_at_infinity
    {F G h : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {ρ θ : ℂ} {r : ℝ} {m p : ℤ}
    (hr : 0 < r) (hρ : ρ ≠ 0) (hθ : ‖θ‖ = 1) (hcut : θ / ρ ∈ slitPlane)
    (hm : -2 < m) (hp : 2 * p < m - 2)
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 r))
    (hG : AnalyticOnNhd ℂ G (Metric.ball 0 r))
    (hFne : ∀ z ∈ Metric.ball 0 r, F z ≠ 0)
    (hroot : ∀ z : ℂ, 2 / r < ‖z‖ → z / ρ ∈ slitPlane →
      h z ^ 2 * z ^ m * F z⁻¹ = 1)
    (hA : IsOriginalVariableLiouvilleGreenCoefficientSequence h
      (fun z => z ^ p * G z⁻¹) A {z : ℂ | 2 / r < ‖z‖ ∧ z / ρ ∈ slitPlane}) (n : ℕ) :
    BoundedVariationOn (fun t : ℝ => A n (t * θ)) (Ioi (2 / r)) ∧
      ∃ a : ℂ, Tendsto (fun t : ℝ => A n (t * θ)) atTop (𝓝 a) := by
  sorry

/-- The exceptional inverse-square pair has analytic LG coefficients in the
reciprocal variable, and therefore convergent variation at infinity. Olver,
Chapter 10, Exercise 4.1, p. 369, second case. -/
theorem exists_analytic_extension_liouvilleGreenCoefficient_at_infinity
    {F G h : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {ρ : ℂ} {r : ℝ}
    (hr : 0 < r) (hρ : ρ ≠ 0)
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 r))
    (hG : AnalyticOnNhd ℂ G (Metric.ball 0 r))
    (hFne : ∀ z ∈ Metric.ball 0 r, F z ≠ 0) (hGzero : G 0 = -1 / 4)
    (hroot : ∀ z : ℂ, 2 / r < ‖z‖ → z / ρ ∈ slitPlane →
      h z ^ 2 * F z⁻¹ = z ^ 2)
    (hA : IsOriginalVariableLiouvilleGreenCoefficientSequence h
      (fun z => G z⁻¹ / z ^ 2) A {z : ℂ | 2 / r < ‖z‖ ∧ z / ρ ∈ slitPlane}) (n : ℕ) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (Metric.ball 0 (r / 2)) ∧
      ∀ z : ℂ, 2 / r < ‖z‖ → z / ρ ∈ slitPlane → B z⁻¹ = A n z := by
  sorry

end Complex
