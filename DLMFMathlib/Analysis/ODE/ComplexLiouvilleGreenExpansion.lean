/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen

/-!
# Complex Liouville–Green coefficient sequences and finite-order errors

Olver, *Asymptotics and Special Functions*, Chapter 10, §2 and Theorem 3.1,
pp. 364–367. The coefficients obey the exact analytic differential recursion.
Each finite truncation has an explicitly computed residual, and an exact nearby
solution has both function and derivative bounds on progressive paths. Finite and
prescribed infinite reference points are treated separately; the solution may
depend on the truncation order.
-/

@[expose] public noncomputable section

open Set Filter Finset
open scoped Topology

namespace Complex

/-- Analytic coefficient data for `W''=(u²+psi)W`, with `A_0=1` and
`2 A_(n+1)'=psi*A_n-A_n''`. Olver, Chapter 10, §2, pp. 364–365.
The values at a reference point supply the integration constants. -/
def IsComplexLiouvilleGreenCoefficientSequence (ψ : ℂ → ℂ) (A : ℕ → ℂ → ℂ)
    (D : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ ψ D ∧ (∀ n, AnalyticOnNhd ℂ (A n) D) ∧
    (∀ z ∈ D, A 0 z = 1) ∧
    ∀ n z, z ∈ D → 2 * deriv (A (n + 1)) z = ψ z * A n z - deriv (deriv (A n)) z

/-- The analytic hypotheses and coefficient differential recursion. -/
theorem isComplexLiouvilleGreenCoefficientSequence_iff
    (ψ : ℂ → ℂ) (A : ℕ → ℂ → ℂ) (D : Set ℂ) :
    IsComplexLiouvilleGreenCoefficientSequence ψ A D ↔
      AnalyticOnNhd ℂ ψ D ∧ (∀ n, AnalyticOnNhd ℂ (A n) D) ∧
        (∀ z ∈ D, A 0 z = 1) ∧
        ∀ n z, z ∈ D →
          2 * deriv (A (n + 1)) z = ψ z * A n z - deriv (deriv (A n)) z := Iff.rfl

/-- Constructor from analyticity, leading normalization and the differential recurrence. -/
theorem IsComplexLiouvilleGreenCoefficientSequence.mk
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {D : Set ℂ}
    (hψ : AnalyticOnNhd ℂ ψ D) (hA : ∀ n, AnalyticOnNhd ℂ (A n) D)
    (h₀ : ∀ z ∈ D, A 0 z = 1)
    (hrec : ∀ n z, z ∈ D →
      2 * deriv (A (n + 1)) z = ψ z * A n z - deriv (deriv (A n)) z) :
    IsComplexLiouvilleGreenCoefficientSequence ψ A D := ⟨hψ, hA, h₀, hrec⟩

/-- Each coefficient is analytic on its branch domain. -/
theorem IsComplexLiouvilleGreenCoefficientSequence.analytic_coefficient
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : IsComplexLiouvilleGreenCoefficientSequence ψ A D) (n : ℕ) :
    AnalyticOnNhd ℂ (A n) D := h.2.1 n

/-- Extraction of the coefficient recurrence without unfolding the predicate. -/
theorem IsComplexLiouvilleGreenCoefficientSequence.recurrence
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {D : Set ℂ}
    (h : IsComplexLiouvilleGreenCoefficientSequence ψ A D) (n : ℕ) {z : ℂ}
    (hz : z ∈ D) :
    2 * deriv (A (n + 1)) z = ψ z * A n z - deriv (deriv (A n)) z := h.2.2.2 n z hz

/-- Arbitrarily prescribed integration constants determine an analytic coefficient
sequence on a simply connected branch domain. Olver, Chapter 10, §2, p. 365. -/
theorem exists_isComplexLiouvilleGreenCoefficientSequence {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) {b : ℂ} (hb : b ∈ D)
    {ψ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ D) (c : ℕ → ℂ) (hc : c 0 = 1) :
    ∃ A : ℕ → ℂ → ℂ, IsComplexLiouvilleGreenCoefficientSequence ψ A D ∧
      ∀ n : ℕ, A n b = c n := by
  sorry

/-- The finite exponential Liouville–Green expansion. The choice `-u` gives the
opposite sign in the exponential and alternating coefficients. Olver, Chapter 10,
(2.01), p. 364. -/
def liouvilleGreenPartialSum (A : ℕ → ℂ → ℂ) (u : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  exp (u * z) * ∑ s ∈ range n, A s z / u ^ s

/-- The defining finite coefficient sum of the Liouville–Green approximant. -/
theorem liouvilleGreenPartialSum_def (A : ℕ → ℂ → ℂ) (u : ℂ) (n : ℕ) (z : ℂ) :
    liouvilleGreenPartialSum A u n z = exp (u * z) * ∑ s ∈ range n, A s z / u ^ s := rfl

/-- The empty exponential truncation is zero. -/
@[simp] theorem liouvilleGreenPartialSum_zero (A : ℕ → ℂ → ℂ) (u z : ℂ) :
    liouvilleGreenPartialSum A u 0 z = 0 := by
  simp [liouvilleGreenPartialSum]

/-- Telescoping the coefficient recurrence leaves exactly the next coefficient
variation as the differential residual. Olver, Chapter 10, §3, p. 366. -/
theorem liouvilleGreenPartialSum_residual {D : Set ℂ} (hD : IsOpen D)
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ}
    (hA : IsComplexLiouvilleGreenCoefficientSequence ψ A D)
    {u : ℂ} (hu : u ≠ 0) {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ D) :
    deriv (deriv (liouvilleGreenPartialSum A u n)) z -
      (u ^ 2 + ψ z) * liouvilleGreenPartialSum A u n z =
        -2 * exp (u * z) * deriv (A n) z / u ^ (n - 1) := by
  sorry

/-- At a finite reference point there is a solution with exactly the initial values
of the chosen truncation. Its additive error and derivative satisfy the source's
explicit bound on every progressive piecewise smooth path. Olver, Chapter 10,
Theorem 3.1, pp. 366–367. Replacing `u` by `-u` gives the other solution. -/
theorem exists_complexLiouvilleGreen_expansion_finite_reference
    {D : Set ℂ} (hD : IsOpen D) (hsc : IsSimplyConnected D)
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ}
    (hA : IsComplexLiouvilleGreenCoefficientSequence ψ A D)
    {u b : ℂ} (hu : u ≠ 0) (hb : b ∈ D) {n : ℕ} (hn : 1 ≤ n) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧ ε b = 0 ∧ deriv ε b = 0 ∧
      (∀ z ∈ D,
        let W := fun t => liouvilleGreenPartialSum A u n t + ε t
        deriv (deriv W) z = (u ^ 2 + ψ z) * W z) ∧
      ∀ γ : ℝ → ℂ, TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = b →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        MonotoneOn (fun t => (u * γ t).re) (Icc 0 1) →
        BoundedVariationOn (A 1 ∘ γ) (Icc 0 1) →
        BoundedVariationOn (A n ∘ γ) (Icc 0 1) →
        let B := 2 * ‖exp (u * γ 1)‖ / ‖u‖ ^ n *
          (eVariationOn (A n ∘ γ) (Icc 0 1)).toReal *
          Real.exp (2 * (eVariationOn (A 1 ∘ γ) (Icc 0 1)).toReal / ‖u‖)
        ‖ε (γ 1)‖ ≤ B ∧ ‖deriv ε (γ 1)‖ / ‖u‖ ≤ B := by
  sorry

/-- Finite coefficient variations on a prescribed recessive initial tail permit an
infinite reference point. Both normalized errors vanish there. Finite joining paths
retain the variation on that same initial tail. Olver, Chapter 10, Theorem 3.1,
pp. 366–367. -/
theorem exists_complexLiouvilleGreen_expansion_endpoint_reference
    {D : Set ℂ} (hD : IsOpen D) (hsc : IsSimplyConnected D)
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ}
    (hA : IsComplexLiouvilleGreenCoefficientSequence ψ A D)
    {u : ℂ} (hu : u ≠ 0) {n : ℕ} (hn : 1 ≤ n) {γ₀ : ℝ → ℂ}
    (hγ₀ : ContinuousOn γ₀ (Ioc 0 1))
    (hregular : ∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ₀ s 1)
    (himage : ∀ t ∈ Ioc (0 : ℝ) 1, γ₀ t ∈ D)
    (hprogressive : MonotoneOn (fun t => (u * γ₀ t).re) (Ioc 0 1))
    (hend : Tendsto (fun t => (u * γ₀ t).re) (𝓝[>] 0) atBot)
    (hvariation₁ : BoundedVariationOn (A 1 ∘ γ₀) (Ioc 0 1))
    (hvariationN : BoundedVariationOn (A n ∘ γ₀) (Ioc 0 1)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧
      (∀ z ∈ D,
        let W := fun t => liouvilleGreenPartialSum A u n t + ε t
        deriv (deriv W) z = (u ^ 2 + ψ z) * W z) ∧
      Tendsto (fun t => ε (γ₀ t) / exp (u * γ₀ t)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => deriv ε (γ₀ t) / (u * exp (u * γ₀ t))) (𝓝[>] 0) (𝓝 0) ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ → ℂ,
        TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = γ₀ s →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        MonotoneOn (fun t => (u * γ t).re) (Icc 0 1) →
        BoundedVariationOn (A 1 ∘ γ) (Icc 0 1) →
        BoundedVariationOn (A n ∘ γ) (Icc 0 1) →
        let V₁ := (eVariationOn (A 1 ∘ γ₀) (Ioc 0 s)).toReal +
          (eVariationOn (A 1 ∘ γ) (Icc 0 1)).toReal
        let VN := (eVariationOn (A n ∘ γ₀) (Ioc 0 s)).toReal +
          (eVariationOn (A n ∘ γ) (Icc 0 1)).toReal
        let B := 2 * ‖exp (u * γ 1)‖ / ‖u‖ ^ n * VN * Real.exp (2 * V₁ / ‖u‖)
        ‖ε (γ 1)‖ ≤ B ∧ ‖deriv ε (γ 1)‖ / ‖u‖ ≤ B := by
  sorry

end Complex
