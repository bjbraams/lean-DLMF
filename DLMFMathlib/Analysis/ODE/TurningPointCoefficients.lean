/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.WeightedRayPrimitive
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Turning-point compound expansion coefficients

The coefficient values are complex, while their variable may be real or complex.
The weighted primitive is equivalent to the first-order B relation on star-shaped
domains; the differential form also permits analytic continuation to other domains.
Integration constants are prescribed separately.
The compound finite sum has an exact residual for any entire Airy-equation solution.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
§7 and Theorem 7.1, pp. 409–412; §9, pp. 417–419.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real BigOperators

namespace ODE

variable {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ]

/-- The compound turning-point coefficient recursion. The `B` integrals have no
free constants; the derivative relation for `A_(s+1)` permits one constant at
each order. Olver, Chapter 11, §7, pp. 409–410. -/
def IsTurningPointCoefficientSequence (ψ : 𝕜 → ℂ) (A B : ℕ → 𝕜 → ℂ)
    (D : Set 𝕜) : Prop :=
  ContDiffOn 𝕜 (⊤ : ℕ∞) ψ D ∧
    (∀ s, ContDiffOn 𝕜 (⊤ : ℕ∞) (A s) D ∧ ContDiffOn 𝕜 (⊤ : ℕ∞) (B s) D) ∧
    (∀ z ∈ D, A 0 z = 1) ∧
    (∀ s z, z ∈ D → 2 * algebraMap 𝕜 ℂ z * deriv (B s) z + B s z =
      ψ z * A s z - deriv (deriv (A s)) z) ∧
    ∀ s z, z ∈ D → 2 * deriv (A (s + 1)) z = ψ z * B s z - deriv (deriv (B s)) z

/-- The explicit smoothness, weighted primitive and derivative-recursion conditions. -/
theorem isTurningPointCoefficientSequence_iff (ψ : 𝕜 → ℂ) (A B : ℕ → 𝕜 → ℂ)
    (D : Set 𝕜) : IsTurningPointCoefficientSequence ψ A B D ↔
      ContDiffOn 𝕜 (⊤ : ℕ∞) ψ D ∧
      (∀ s, ContDiffOn 𝕜 (⊤ : ℕ∞) (A s) D ∧ ContDiffOn 𝕜 (⊤ : ℕ∞) (B s) D) ∧
      (∀ z ∈ D, A 0 z = 1) ∧
      (∀ s z, z ∈ D → 2 * algebraMap 𝕜 ℂ z * deriv (B s) z + B s z =
        ψ z * A s z - deriv (deriv (A s)) z) ∧
      ∀ s z, z ∈ D → 2 * deriv (A (s + 1)) z = ψ z * B s z - deriv (deriv (B s)) z :=
  Iff.rfl

/-- Construct turning-point coefficient data from its actual defining relations. -/
theorem IsTurningPointCoefficientSequence.mk {ψ : 𝕜 → ℂ} {A B : ℕ → 𝕜 → ℂ}
    {D : Set 𝕜} (hψ : ContDiffOn 𝕜 (⊤ : ℕ∞) ψ D)
    (hsmooth : ∀ s, ContDiffOn 𝕜 (⊤ : ℕ∞) (A s) D ∧ ContDiffOn 𝕜 (⊤ : ℕ∞) (B s) D)
    (hzero : ∀ z ∈ D, A 0 z = 1)
    (hB : ∀ s z, z ∈ D → 2 * algebraMap 𝕜 ℂ z * deriv (B s) z + B s z =
      ψ z * A s z - deriv (deriv (A s)) z)
    (hA : ∀ s z, z ∈ D →
      2 * deriv (A (s + 1)) z = ψ z * B s z - deriv (deriv (B s)) z) :
    IsTurningPointCoefficientSequence ψ A B D := ⟨hψ, hsmooth, hzero, hB, hA⟩

/-- The removable weighted-primitive value at zero. Olver, Chapter 11,
Lemma 7.1 and the coefficient construction of §7, p. 410. -/
theorem IsTurningPointCoefficientSequence.B_zero {ψ : 𝕜 → ℂ} {A B : ℕ → 𝕜 → ℂ}
    {D : Set 𝕜} (h : IsTurningPointCoefficientSequence ψ A B D) (hzero : 0 ∈ D) (s : ℕ) :
    B s 0 = ψ 0 * A s 0 - deriv (deriv (A s)) 0 := by
  simpa only [map_zero, mul_zero, zero_mul, zero_add] using h.2.2.2.1 s 0 hzero

/-- On a star-shaped coefficient domain, the smooth differential relation is
exactly the weighted-integral recursion, including its removable value at zero.
Olver, Chapter 11, Lemma 7.1 and §7, pp. 409–410. -/
theorem IsTurningPointCoefficientSequence.B_eq_weightedRayPrimitive
    [IsScalarTower ℝ 𝕜 ℂ] {ψ : 𝕜 → ℂ} {A B : ℕ → 𝕜 → ℂ} {D : Set 𝕜}
    (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    (h : IsTurningPointCoefficientSequence ψ A B D) (s : ℕ) {z : 𝕜} (hz : z ∈ D) :
    B s z = (1 / 2 : ℂ) *
      weightedRayPrimitive (-1 / 2) (fun w => ψ w * A s w - deriv (deriv (A s)) w) z := by
  sorry

/-- Smooth complex-valued real data admit the full coefficient recursion through
zero, with every integration constant prescribed. Olver, Chapter 11,
§7 and Theorem 7.1, pp. 409–412. -/
theorem exists_turningPointCoefficientSequence_real {D : Set ℝ} (hD : IsOpen D)
    (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D) {ψ : ℝ → ℂ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ D) (initial : ℕ → ℂ) :
    ∃ A B : ℕ → ℝ → ℂ, IsTurningPointCoefficientSequence ψ A B D ∧
      ∀ s, A (s + 1) 0 = initial s := by
  sorry

/-- Analytic data admit analytic turning-point coefficients on an open star-shaped
domain, with prescribed constants at zero. Olver, Chapter 11, §9, pp. 417–419. -/
theorem exists_turningPointCoefficientSequence_complex {D : Set ℂ} (hD : IsOpen D)
    (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ D) (initial : ℕ → ℂ) :
    ∃ A B : ℕ → ℂ → ℂ, IsTurningPointCoefficientSequence ψ A B D ∧
      (∀ s, AnalyticOnNhd ℂ (A s) D ∧ AnalyticOnNhd ℂ (B s) D) ∧
      ∀ s, A (s + 1) 0 = initial s := by
  sorry

/-- Analytic coefficient construction extends to an arbitrary simply connected
domain containing the turning point. The differential recursion gives the
continuation of the weighted primitive without requiring every straight segment
to stay in the domain. Olver, Chapter 11, §9, pp. 417–419. -/
theorem exists_turningPointCoefficientSequence_complex_on_simplyConnected
    {D : Set ℂ} (hD : IsOpen D) (hsc : IsSimplyConnected D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ D) (initial : ℕ → ℂ) :
    ∃ A B : ℕ → ℂ → ℂ, IsTurningPointCoefficientSequence ψ A B D ∧
      (∀ s, AnalyticOnNhd ℂ (A s) D ∧ AnalyticOnNhd ℂ (B s) D) ∧
      ∀ s, A (s + 1) 0 = initial s := by
  sorry

/-- The actual compound sum through `A_n,B_(n-1)`. The scale relation `v^3=u^2`
is asserted in its residual theorem; for positive real `u`, take `v=u^(2/3)`.
Olver, Chapter 11, Theorem 7.1, pp. 410–412. -/
def turningPointPartialSum (A B : ℕ → 𝕜 → ℂ) (C : ℂ → ℂ)
    (u v : ℂ) (n : ℕ) (z : 𝕜) : ℂ :=
  C (v * algebraMap 𝕜 ℂ z) * (∑ s ∈ Finset.range (n + 1), A s z / u ^ (2 * s)) +
    v / u ^ 2 * deriv C (v * algebraMap 𝕜 ℂ z) *
      (∑ s ∈ Finset.range n, B s z / u ^ (2 * s))

/-- The defining pair of finite sums. -/
theorem turningPointPartialSum_def (A B : ℕ → 𝕜 → ℂ) (C : ℂ → ℂ)
    (u v : ℂ) (n : ℕ) (z : 𝕜) : turningPointPartialSum A B C u v n z =
      C (v * algebraMap 𝕜 ℂ z) * (∑ s ∈ Finset.range (n + 1), A s z / u ^ (2 * s)) +
        v / u ^ 2 * deriv C (v * algebraMap 𝕜 ℂ z) *
          (∑ s ∈ Finset.range n, B s z / u ^ (2 * s)) := rfl

/-- The zero-order compound sum is the chosen Airy solution times `A_0`. -/
@[simp] theorem turningPointPartialSum_zero (A B : ℕ → 𝕜 → ℂ) (C : ℂ → ℂ)
    (u v : ℂ) (z : 𝕜) :
    turningPointPartialSum A B C u v 0 z = C (v * algebraMap 𝕜 ℂ z) * A 0 z := by
  simp [turningPointPartialSum]

/-- The exact compound residual is a single Airy factor times `B_n+2zB_n'`.
This is the derivative of the weighted coefficient `sqrt(z)*B_n`, and is the
quantity controlling the error variation. Olver, Chapter 11, Theorem 7.1,
pp. 410–412, and the complex version of §9, pp. 417–418. -/
theorem turningPointPartialSum_residual [IsScalarTower ℝ 𝕜 ℂ]
    {ψ : 𝕜 → ℂ} {A B : ℕ → 𝕜 → ℂ} {D : Set 𝕜}
    (hD : IsOpen D) (hcoeff : IsTurningPointCoefficientSequence ψ A B D)
    {C : ℂ → ℂ} (hC : AnalyticOnNhd ℂ C univ)
    (hCode : ∀ w : ℂ, deriv (deriv C) w = w * C w)
    {u v : ℂ} (hu : u ≠ 0) (hscale : v ^ 3 = u ^ 2) (n : ℕ) {z : 𝕜} (hz : z ∈ D) :
    deriv (deriv (turningPointPartialSum A B C u v n)) z -
      (u ^ 2 * algebraMap 𝕜 ℂ z + ψ z) * turningPointPartialSum A B C u v n z =
        -C (v * algebraMap 𝕜 ℂ z) *
          (B n z + 2 * algebraMap 𝕜 ℂ z * deriv (B n) z) / u ^ (2 * n) := by
  sorry

end ODE
