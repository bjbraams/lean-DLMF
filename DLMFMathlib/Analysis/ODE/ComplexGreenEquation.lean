/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Complex Green equations and explicit residual bounds

An arbitrary analytic fundamental pair supplies a fully specified kernel and
its derivative. The source weights are actual functions of that pair, and all
integrals use absolute arc length for their bounds. The endpoint theorem keeps
a prescribed initial tail and asserts convergence separately.
Source: Olver, *Asymptotics and Special Functions*, Chapter 6,
§10.2 and Theorems 10.1–10.2, pp. 218–220.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Real Topology

namespace Complex

/-- The exact oriented Green residual equation and its normalized error bounds
for a prescribed analytic fundamental pair. The two derivatives in the conclusion
are bounded by the same explicit `A*exp(B)`. Olver, Chapter 6, Theorem 10.2,
p. 220, and its fundamental-pair specialization. -/
theorem complexGreen_error_integral_and_bound {D : Set ℂ} (hD : IsOpen D)
    {Q R T U V ε : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q D)
    (hR : AnalyticOnNhd ℂ R D) (hT : AnalyticOnNhd ℂ T D)
    (hU : AnalyticOnNhd ℂ U D) (hV : AnalyticOnNhd ℂ V D)
    (hε : AnalyticOnNhd ℂ ε D)
    (hUode : ∀ z ∈ D, deriv (deriv U) z = Q z * U z)
    (hVode : ∀ z ∈ D, deriv (deriv V) z = Q z * V z)
    (hW : ∀ z ∈ D, U z * deriv V z - deriv U z * V z ≠ 0)
    (hεode : ∀ z ∈ D, deriv (deriv ε) z = Q z * ε z - R z + T z * ε z)
    {b : ℂ} (hb : b ∈ D) (hzero : ε b = 0) (hderivzero : deriv ε b = 0)
    {γ : ℝ → ℂ} (hγ : TauCeti.IsPiecewiseC1On γ 0 1) (hbase : γ 0 = b)
    (himage : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) :
    let W := fun z => U z * deriv V z - deriv U z * V z
    let P₀ := fun z => ‖U z‖ + ‖V z‖
    let P₁ := fun z => ‖deriv U z‖ + ‖deriv V z‖
    let k := fun z => max ‖U z‖ ‖V z‖ / ‖W z‖
    let forcing := fun z => -R z + T z * ε z
    let A := ∫ t : ℝ in 0..1, k (γ t) * ‖R (γ t)‖ * ‖deriv γ t‖
    let B := ∫ t : ℝ in 0..1, k (γ t) * ‖T (γ t)‖ * P₀ (γ t) * ‖deriv γ t‖
    ε (γ 1) = ∫ t : ℝ in 0..1,
      (U (γ t) * V (γ 1) - V (γ t) * U (γ 1)) / W (γ t) * forcing (γ t) * deriv γ t ∧
    deriv ε (γ 1) = ∫ t : ℝ in 0..1,
      (U (γ t) * deriv V (γ 1) - V (γ t) * deriv U (γ 1)) / W (γ t) *
        forcing (γ t) * deriv γ t ∧
    ‖ε (γ 1)‖ / P₀ (γ 1) ≤ A * Real.exp B ∧
      ‖deriv ε (γ 1)‖ / P₁ (γ 1) ≤ A * Real.exp B := by
  sorry

/-- An integrable prescribed initial tail supports the Green construction even
when its reference endpoint lies on the boundary or at infinity. Both normalized
errors vanish at that endpoint; the actual Green integral and its integrability
are recorded for every initial-tail segment. Olver, Chapter 6,
Theorems 10.1–10.2, pp. 219–220. -/
theorem exists_complexGreen_error_endpoint {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D)
    {Q R T U V : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q D)
    (hR : AnalyticOnNhd ℂ R D) (hT : AnalyticOnNhd ℂ T D)
    (hU : AnalyticOnNhd ℂ U D) (hV : AnalyticOnNhd ℂ V D)
    (hUode : ∀ z ∈ D, deriv (deriv U) z = Q z * U z)
    (hVode : ∀ z ∈ D, deriv (deriv V) z = Q z * V z)
    (hW : ∀ z ∈ D, U z * deriv V z - deriv U z * V z ≠ 0)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ioc 0 1))
    (hregular : ∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ s 1)
    (himage : ∀ t ∈ Ioc (0 : ℝ) 1, γ t ∈ D)
    (hend : (∃ b : ℂ, b ∉ D ∧ Tendsto γ (𝓝[>] 0) (𝓝 b)) ∨
      Tendsto (fun t => ‖γ t‖) (𝓝[>] 0) atTop)
    (hRint : IntegrableOn (fun t : ℝ =>
      max ‖U (γ t)‖ ‖V (γ t)‖ / ‖U (γ t) * deriv V (γ t) - deriv U (γ t) * V (γ t)‖ *
        ‖R (γ t)‖ * ‖deriv γ t‖) (Ioc 0 1))
    (hTint : IntegrableOn (fun t : ℝ =>
      max ‖U (γ t)‖ ‖V (γ t)‖ / ‖U (γ t) * deriv V (γ t) - deriv U (γ t) * V (γ t)‖ *
        ‖T (γ t)‖ * (‖U (γ t)‖ + ‖V (γ t)‖) * ‖deriv γ t‖) (Ioc 0 1)) :
    let W := fun z => U z * deriv V z - deriv U z * V z
    let P₀ := fun z => ‖U z‖ + ‖V z‖
    let P₁ := fun z => ‖deriv U z‖ + ‖deriv V z‖
    let k := fun z => max ‖U z‖ ‖V z‖ / ‖W z‖
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧
      (∀ z ∈ D, deriv (deriv ε) z = Q z * ε z - R z + T z * ε z) ∧
      Tendsto (fun t => ‖ε (γ t)‖ / P₀ (γ t)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => ‖deriv ε (γ t)‖ / P₁ (γ t)) (𝓝[>] 0) (𝓝 0) ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        let integrand := fun t =>
          (U (γ t) * V (γ s) - V (γ t) * U (γ s)) / W (γ t) *
            (-R (γ t) + T (γ t) * ε (γ t)) * deriv γ t
        let A := ∫ t in Ioc 0 s, k (γ t) * ‖R (γ t)‖ * ‖deriv γ t‖
        let B := ∫ t in Ioc 0 s, k (γ t) * ‖T (γ t)‖ * P₀ (γ t) * ‖deriv γ t‖
        IntegrableOn integrand (Ioc 0 s) ∧ ε (γ s) = ∫ t in Ioc 0 s, integrand t ∧
          ‖ε (γ s)‖ / P₀ (γ s) ≤ A * Real.exp B ∧
            ‖deriv ε (γ s)‖ / P₁ (γ s) ≤ A * Real.exp B := by
  sorry

end Complex
