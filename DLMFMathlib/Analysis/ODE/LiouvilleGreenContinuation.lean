/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LinearODEContinuation
public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen

/-!
# Progressive Liouville–Green estimates on continued branches

Olver, *Asymptotics and Special Functions*, Chapter 6, Theorem 11.1,
p. 222, synopsis O-6.17. A branch on a covering surface is represented
by actual compatible analytic germs along its path, using TauCeti's canonical
continuation predicate. No single-valued phase or fourth root on the original
domain is assumed. Finite and prescribed improper initial arcs are both retained.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Complex

/-- Actual continued fourth-root, phase and control germs along a path. The algebraic
and differential branch relations hold in neighborhoods of its points.
Olver, Chapter 6, §11, synopsis O-6.17. -/
def IsLiouvilleGreenContinuation (f g : ℂ → ℂ) (path : ℝ → ℂ) (s : Set ℝ)
    (amplitude phase control : ℝ → ℂ → ℂ) : Prop :=
  TauCeti.IsAnalyticContinuationAlong amplitude path s ∧
    TauCeti.IsAnalyticContinuationAlong phase path s ∧
    TauCeti.IsAnalyticContinuationAlong control path s ∧
    ∀ t ∈ s, ∀ᶠ z in 𝓝 (path t),
      amplitude t z ^ 4 * f z = 1 ∧ deriv (phase t) z = (amplitude t z ^ 2)⁻¹ ∧
        deriv (control t) z = amplitude t z * deriv (deriv (amplitude t)) z -
          g z * amplitude t z ^ 2

/-- The defining compatible germs and local LG branch equations. -/
theorem isLiouvilleGreenContinuation_iff (f g : ℂ → ℂ) (path : ℝ → ℂ) (s : Set ℝ)
    (amplitude phase control : ℝ → ℂ → ℂ) :
    IsLiouvilleGreenContinuation f g path s amplitude phase control ↔
      TauCeti.IsAnalyticContinuationAlong amplitude path s ∧
        TauCeti.IsAnalyticContinuationAlong phase path s ∧
        TauCeti.IsAnalyticContinuationAlong control path s ∧
        ∀ t ∈ s, ∀ᶠ z in 𝓝 (path t),
          amplitude t z ^ 4 * f z = 1 ∧ deriv (phase t) z = (amplitude t z ^ 2)⁻¹ ∧
            deriv (control t) z = amplitude t z * deriv (deriv (amplitude t)) z -
              g z * amplitude t z ^ 2 := Iff.rfl

/-- Every path in an analytic zero-free coefficient domain carries its specified
fourth-root germ and the two normalized primitives. The domain may be multiply connected.
Olver, Chapter 6, §11, synopsis O-6.17. -/
theorem exists_liouvilleGreenContinuation {D : Set ℂ} (hD : IsOpen D)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D)
    (hne : ∀ z ∈ D, f z ≠ 0) {path : ℝ → ℂ}
    (hpath : ContinuousOn path (Icc (0 : ℝ) 1))
    (him : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D)
    {a₀ : ℂ} (ha₀ : a₀ ^ 4 * f (path 0) = 1) :
    ∃ amplitude phase control : ℝ → ℂ → ℂ,
      IsLiouvilleGreenContinuation f g path (Icc 0 1) amplitude phase control ∧
      amplitude 0 (path 0) = a₀ ∧ phase 0 (path 0) = 0 ∧ control 0 (path 0) = 0 := by
  sorry

/-- The finite-reference progressive estimate survives arbitrary continuation along
the actual path, including nontrivial monodromy of its coefficient roots and primitives.
Olver, Chapter 6, Theorem 11.1, synopsis O-6.17. -/
theorem exists_liouvilleGreenContinuation_error {D : Set ℂ} (hD : IsOpen D)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D)
    {path : ℝ → ℂ} (hpath : TauCeti.IsPiecewiseC1On path 0 1)
    (him : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D)
    {A Ξ F : ℝ → ℂ → ℂ} (hdata : IsLiouvilleGreenContinuation f g path (Icc 0 1) A Ξ F)
    {u : ℂ} (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hprogress : MonotoneOn (fun t => σ * (u * Ξ t (path t)).re) (Icc 0 1))
    (hvar : BoundedVariationOn (fun t => F t (path t)) (Icc 0 1)) :
    ∃ W ε : ℝ → ℂ → ℂ,
      IsLinearSecondOrderContinuation (fun _ => 0) (fun z => -(u ^ 2 * f z + g z)) D path W ∧
      TauCeti.IsAnalyticContinuationAlong ε path (Icc 0 1) ∧
      ε 0 (path 0) = 0 ∧ deriv (ε 0) (path 0) = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ z in 𝓝 (path t),
        W t z = A t z * exp (σ * u * Ξ t z) * (1 + ε t z)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        ‖ε t (path t)‖ ≤
          Real.exp ((eVariationOn (fun s => F s (path s)) (Icc 0 t)).toReal / ‖u‖) - 1 ∧
        ‖A t (path t) ^ 2 * deriv (ε t) (path t) / u‖ ≤
          Real.exp ((eVariationOn (fun s => F s (path s)) (Icc 0 t)).toReal / ‖u‖) - 1) := by
  sorry

/-- A prescribed improper progressive initial arc gives continued solution/error germs,
zero endpoint errors, and every initial-tail variation bound on its covering branch.
Olver, Chapter 6, Theorem 11.1, synopsis O-6.17. -/
theorem exists_liouvilleGreenContinuation_endpoint_error {D : Set ℂ} (hD : IsOpen D)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (hg : AnalyticOnNhd ℂ g D)
    {path : ℝ → ℂ} (hpath : ContinuousOn path (Ioc (0 : ℝ) 1))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) 1, TauCeti.IsPiecewiseC1On path t 1)
    (him : ∀ t ∈ Ioc (0 : ℝ) 1, path t ∈ D)
    {A Ξ F : ℝ → ℂ → ℂ} (hdata : IsLiouvilleGreenContinuation f g path (Ioc 0 1) A Ξ F)
    {u : ℂ} (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hprogress : MonotoneOn (fun t => σ * (u * Ξ t (path t)).re) (Ioc 0 1))
    (hinitial : Tendsto (fun t => σ * (u * Ξ t (path t)).re) (𝓝[>] 0) atBot)
    (hvar : BoundedVariationOn (fun t => F t (path t)) (Ioc 0 1)) :
    ∃ W ε : ℝ → ℂ → ℂ,
      TauCeti.IsAnalyticContinuationAlong W path (Ioc 0 1) ∧
      TauCeti.IsAnalyticContinuationAlong ε path (Ioc 0 1) ∧
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ᶠ z in 𝓝 (path t),
        deriv (deriv (W t)) z = (u ^ 2 * f z + g z) * W t z ∧
        W t z = A t z * exp (σ * u * Ξ t z) * (1 + ε t z)) ∧
      Tendsto (fun t => ε t (path t)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => A t (path t) ^ 2 * deriv (ε t) (path t) / u) (𝓝[>] 0) (𝓝 0) ∧
      ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖ε t (path t)‖ ≤
          Real.exp ((eVariationOn (fun s => F s (path s)) (Ioc 0 t)).toReal / ‖u‖) - 1 ∧
        ‖A t (path t) ^ 2 * deriv (ε t) (path t) / u‖ ≤
          Real.exp ((eVariationOn (fun s => F s (path s)) (Ioc 0 t)).toReal / ‖u‖) - 1 := by
  sorry

end Complex
