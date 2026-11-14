/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreenExpansion
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On

/-!
# Uniform complex Liouville–Green coefficient bounds

The fixed boundary buffer and weighted joining paths make the bounds uniform in
both the parameter and the possibly unbounded phase variable. A separate theorem
constructs one exact solution with every truncation order simultaneously at finite
reference points; it does not infer this from solutions depending on the truncation.
Source: Olver, *Asymptotics and Special Functions*, Chapter 10,
Theorem 5.1, pp. 370–371, and §6, pp. 371–373.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Real Topology

namespace Complex

/-- Uniform bounds for every coefficient and its derivative, with the source's
weighted derivative decay and all parameter dependence retained. The ball buffer
is the equivalent interior formulation of fixed distance from the domain boundary.
Olver, Chapter 10, Theorem 5.1, pp. 370–371. -/
theorem exists_uniform_liouvilleGreen_coefficient_bounds
    {ι : Type*} (ψ : ι → ℂ → ℂ) (A : ι → ℕ → ℂ → ℂ)
    (D Γ : ι → Set ℂ) (a : ι → ℂ) (γ : ι → ℂ → ℝ → ℂ)
    {k p d L : ℝ} (hk : 0 ≤ k) (hp : 0 < p) (hd : 0 < d) (hL : 0 ≤ L)
    (initialBound : ℕ → ℝ) (hinitialBound : ∀ n, 0 ≤ initialBound n)
    (hD : ∀ i, IsOpen (D i))
    (hsequence : ∀ i, IsComplexLiouvilleGreenCoefficientSequence (ψ i) (A i) (D i))
    (hΓ : ∀ i, Γ i ⊆ D i) (ha : ∀ i, a i ∈ Γ i)
    (hbuffer : ∀ i z, z ∈ Γ i → Metric.ball z d ⊆ D i)
    (hψ : ∀ i z, z ∈ D i → ‖ψ i z‖ ≤ k / (1 + ‖z‖ ^ (1 + p)))
    (hinitial : ∀ n i, ‖A i n (a i)‖ ≤ initialBound n)
    (hpaths : ∀ i z, z ∈ Γ i →
      TauCeti.IsPiecewiseC1On (γ i z) 0 1 ∧ γ i z 0 = a i ∧ γ i z 1 = z ∧
        γ i z '' Icc 0 1 ⊆ Γ i ∧
        (∫ t : ℝ in 0..1, ‖deriv (γ i z) t‖ / (1 + ‖γ i z t‖ ^ (1 + p))) ≤ L)
    (n : ℕ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 ≤ M ∧ ∀ i z, z ∈ Γ i →
      ‖A i n z‖ ≤ K ∧ ‖deriv (A i n) z‖ ≤ M / (1 + ‖z‖ ^ (1 + p)) := by
  sorry

/-- On simply connected analytic domains, finite-reference all-orders initial
matching gives one exact solution per parameter with every asymptotic order at
once, uniformly on the progressive joining paths. Initial matching is chosen as
part of the construction, so uniqueness is not asserted. Replacing `u` by `-u`
gives the opposite solution and progressive direction. Olver, Chapter 10,
§6, pp. 371–373, under the hypotheses of Theorem 5.1. -/
theorem exists_allOrders_complexLiouvilleGreen_finite_reference
    {ι : Type*} (ψ : ι → ℂ → ℂ) (A : ι → ℕ → ℂ → ℂ)
    (D Γ : ι → Set ℂ) (a : ι → ℂ) (γ : ι → ℂ → ℝ → ℂ)
    {k p d L : ℝ} (hk : 0 ≤ k) (hp : 0 < p) (hd : 0 < d) (hL : 0 ≤ L)
    (initialBound : ℕ → ℝ) (hinitialBound : ∀ n, 0 ≤ initialBound n)
    (hD : ∀ i, IsOpen (D i))
    (hsequence : ∀ i, IsComplexLiouvilleGreenCoefficientSequence (ψ i) (A i) (D i))
    (hΓ : ∀ i, Γ i ⊆ D i) (ha : ∀ i, a i ∈ Γ i)
    (hbuffer : ∀ i z, z ∈ Γ i → Metric.ball z d ⊆ D i)
    (hψ : ∀ i z, z ∈ D i → ‖ψ i z‖ ≤ k / (1 + ‖z‖ ^ (1 + p)))
    (hinitial : ∀ n i, ‖A i n (a i)‖ ≤ initialBound n)
    (hpaths : ∀ i z, z ∈ Γ i →
      TauCeti.IsPiecewiseC1On (γ i z) 0 1 ∧ γ i z 0 = a i ∧ γ i z 1 = z ∧
        γ i z '' Icc 0 1 ⊆ Γ i ∧
        (∫ t : ℝ in 0..1, ‖deriv (γ i z) t‖ / (1 + ‖γ i z t‖ ^ (1 + p))) ≤ L)
    (hsc : ∀ i, IsSimplyConnected (D i)) (u : ι → ℂ) (hu : ∀ i, u i ≠ 0)
    (l : Filter ι) (huAtInfinity : Tendsto (fun i => ‖u i‖) l atTop)
    (hprogressive : ∀ i z, z ∈ Γ i →
      MonotoneOn (fun t : ℝ => (u i * γ i z t).re) (Icc 0 1)) :
    ∃ W : ι → ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (W i) (D i) ∧ ∀ z ∈ D i,
        deriv (deriv (W i)) z = (u i ^ 2 + ψ i z) * W i z) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in l, ∀ z ∈ Γ i,
        ‖(W i z - liouvilleGreenPartialSum (A i) (u i) N z) * exp (-u i * z)‖ ≤
          C / ‖u i‖ ^ N ∧
        ‖((deriv (W i) z - deriv (liouvilleGreenPartialSum (A i) (u i) N) z) / u i) *
          exp (-u i * z)‖ ≤ C / ‖u i‖ ^ N := by
  sorry

/-- One recessively normalized exact solution has every truncation order at an
infinite reference point. The coefficient constants vanish there for positive
indices. Uniform variation bounds are precisely the conclusion supplied by the
weighted-path hypotheses of Theorem 5.1. Olver, Chapter 10, §6, pp. 371–373. -/
theorem exists_allOrders_complexLiouvilleGreen_endpoint_reference
    {ι : Type*} (ψ : ι → ℂ → ℂ) (A : ι → ℕ → ℂ → ℂ)
    (D Γ : ι → Set ℂ) (u : ι → ℂ)
    (tail : ι → ℝ → ℂ) (joining : ι → ℂ → ℝ → ℂ)
    (variationBound : ℕ → ℝ) (hbound : ∀ n, 0 ≤ variationBound n)
    (hD : ∀ i, IsOpen (D i)) (hsc : ∀ i, IsSimplyConnected (D i))
    (hsequence : ∀ i, IsComplexLiouvilleGreenCoefficientSequence (ψ i) (A i) (D i))
    (hu : ∀ i, u i ≠ 0) (hΓ : ∀ i, Γ i ⊆ D i)
    (htail : ∀ i, ContinuousOn (tail i) (Ioc 0 1) ∧
      (∀ a : ℝ, 0 < a → a < 1 → TauCeti.IsPiecewiseC1On (tail i) a 1) ∧
      tail i '' Ioc 0 1 ⊆ D i ∧
      Tendsto (fun t => (u i * tail i t).re) (𝓝[>] 0) atBot ∧
      MonotoneOn (fun t => (u i * tail i t).re) (Ioc 0 1))
    (hlimit : ∀ i n, 0 < n → Tendsto (A i n ∘ tail i) (𝓝[>] 0) (𝓝 0))
    (hpaths : ∀ i z, z ∈ Γ i →
      TauCeti.IsPiecewiseC1On (joining i z) 0 1 ∧ joining i z 0 = tail i 1 ∧
        joining i z 1 = z ∧ joining i z '' Icc 0 1 ⊆ D i ∧
        MonotoneOn (fun t => (u i * joining i z t).re) (Icc 0 1))
    (hvariation : ∀ i n z, z ∈ Γ i →
      BoundedVariationOn (A i n ∘ tail i) (Ioc 0 1) ∧
        BoundedVariationOn (A i n ∘ joining i z) (Icc 0 1) ∧
        (eVariationOn (A i n ∘ tail i) (Ioc 0 1)).toReal +
          (eVariationOn (A i n ∘ joining i z) (Icc 0 1)).toReal ≤ variationBound n) :
    ∃ W : ι → ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (W i) (D i) ∧
        (∀ z ∈ D i, deriv (deriv (W i)) z = (u i ^ 2 + ψ i z) * W i z) ∧
        Tendsto (fun t => W i (tail i t) * exp (-u i * tail i t))
          (𝓝[>] 0) (𝓝 1)) ∧
      ∀ N : ℕ, 0 < N → ∀ i z, z ∈ Γ i →
        ‖(W i z - liouvilleGreenPartialSum (A i) (u i) N z) * exp (-u i * z)‖ ≤
          2 * variationBound N / ‖u i‖ ^ N *
            Real.exp (2 * variationBound 1 / ‖u i‖) ∧
        ‖((deriv (W i) z - deriv (liouvilleGreenPartialSum (A i) (u i) N) z) / u i) *
          exp (-u i * z)‖ ≤ 2 * variationBound N / ‖u i‖ ^ N *
            Real.exp (2 * variationBound 1 / ‖u i‖) := by
  sorry

end Complex
