/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexGreenEquation

/-!
# Complex Green errors with first-derivative coupling

Olver, *Asymptotics and Special Functions*, Chapter 6, Theorems 10.1–10.2,
and Chapter 7, Theorem 12.1, pp. 265–270, synopsis O-7.18. The comparison
pair may solve an equation with a first-derivative term. Both the value error
and its derivative enter the computable absolute-arc-length majorant.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Complex

/-- A full derivative-coupled Green equation and explicit bounds with arbitrary finite
initial errors. The initial homogeneous coefficients are solved from the actual value
and derivative at the initial point. Olver, Chapter 7, Theorem 12.1, synopsis O-7.18. -/
theorem complexGreen_derivative_coupling_error {D : Set ℂ} (hD : IsOpen D)
    {p q P Q R U V ε : ℂ → ℂ}
    (han : ∀ f ∈ ({p, q, P, Q, R, U, V, ε} : Set (ℂ → ℂ)), AnalyticOnNhd ℂ f D)
    (hU : ∀ z ∈ D, deriv (deriv U) z + P z * deriv U z + Q z * U z = 0)
    (hV : ∀ z ∈ D, deriv (deriv V) z + P z * deriv V z + Q z * V z = 0)
    (hW : ∀ z ∈ D, U z * deriv V z - deriv U z * V z ≠ 0)
    (hε : ∀ z ∈ D, deriv (deriv ε) z + p z * deriv ε z + q z * ε z = -R z)
    {γ : ℝ → ℂ} (hγ : TauCeti.IsPiecewiseC1On γ 0 1)
    (himage : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) :
    let W := fun z => U z * deriv V z - deriv U z * V z
    let P₀ := fun z => ‖U z‖ + ‖V z‖
    let P₁ := fun z => ‖deriv U z‖ + ‖deriv V z‖
    let k := fun z => max ‖U z‖ ‖V z‖ / ‖W z‖
    let C₁ := (ε (γ 0) * deriv V (γ 0) - deriv ε (γ 0) * V (γ 0)) / W (γ 0)
    let C₂ := (deriv ε (γ 0) * U (γ 0) - ε (γ 0) * deriv U (γ 0)) / W (γ 0)
    let forcing := fun z => -R z - (p z - P z) * deriv ε z - (q z - Q z) * ε z
    let A := ∫ t : ℝ in 0..1, k (γ t) * ‖R (γ t)‖ * ‖deriv γ t‖
    let B := ∫ t : ℝ in 0..1, k (γ t) *
      (‖p (γ t) - P (γ t)‖ * P₁ (γ t) + ‖q (γ t) - Q (γ t)‖ * P₀ (γ t)) * ‖deriv γ t‖
    ε (γ 1) = C₁ * U (γ 1) + C₂ * V (γ 1) + ∫ t : ℝ in 0..1,
      (U (γ t) * V (γ 1) - V (γ t) * U (γ 1)) / W (γ t) * forcing (γ t) * deriv γ t ∧
    deriv ε (γ 1) = C₁ * deriv U (γ 1) + C₂ * deriv V (γ 1) + ∫ t : ℝ in 0..1,
      (U (γ t) * deriv V (γ 1) - V (γ t) * deriv U (γ 1)) / W (γ t) *
        forcing (γ t) * deriv γ t ∧
    ‖ε (γ 1)‖ / P₀ (γ 1) ≤ (max ‖C₁‖ ‖C₂‖ + A) * Real.exp B ∧
      ‖deriv ε (γ 1)‖ / P₁ (γ 1) ≤ (max ‖C₁‖ ‖C₂‖ + A) * Real.exp B := by
  sorry

/-- An actual integrable initial tail gives a derivative-coupled residual correction,
the absolutely convergent Green equation, zero normalized endpoint errors, and explicit
value/derivative majorants. Olver, Chapter 7, Theorem 12.1, synopsis O-7.18. -/
theorem exists_complexGreen_derivative_coupling_endpoint {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) {p q P Q R U V : ℂ → ℂ}
    (han : ∀ f ∈ ({p, q, P, Q, R, U, V} : Set (ℂ → ℂ)), AnalyticOnNhd ℂ f D)
    (hU : ∀ z ∈ D, deriv (deriv U) z + P z * deriv U z + Q z * U z = 0)
    (hV : ∀ z ∈ D, deriv (deriv V) z + P z * deriv V z + Q z * V z = 0)
    (hW : ∀ z ∈ D, U z * deriv V z - deriv U z * V z ≠ 0)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ioc 0 1))
    (hregular : ∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ s 1)
    (himage : ∀ t ∈ Ioc (0 : ℝ) 1, γ t ∈ D)
    (hend : (∃ b : ℂ, b ∉ D ∧ Tendsto γ (𝓝[>] 0) (𝓝 b)) ∨
      Tendsto (fun t => ‖γ t‖) (𝓝[>] 0) atTop)
    (hRint : IntegrableOn (fun t : ℝ =>
      max ‖U (γ t)‖ ‖V (γ t)‖ / ‖U (γ t) * deriv V (γ t) - deriv U (γ t) * V (γ t)‖ *
        ‖R (γ t)‖ * ‖deriv γ t‖) (Ioc 0 1))
    (hcoupling : IntegrableOn (fun t : ℝ =>
      max ‖U (γ t)‖ ‖V (γ t)‖ / ‖U (γ t) * deriv V (γ t) - deriv U (γ t) * V (γ t)‖ *
        (‖p (γ t) - P (γ t)‖ * (‖deriv U (γ t)‖ + ‖deriv V (γ t)‖) +
          ‖q (γ t) - Q (γ t)‖ * (‖U (γ t)‖ + ‖V (γ t)‖)) * ‖deriv γ t‖) (Ioc 0 1)) :
    let W := fun z => U z * deriv V z - deriv U z * V z
    let P₀ := fun z => ‖U z‖ + ‖V z‖
    let P₁ := fun z => ‖deriv U z‖ + ‖deriv V z‖
    let k := fun z => max ‖U z‖ ‖V z‖ / ‖W z‖
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧
      (∀ z ∈ D, deriv (deriv ε) z + p z * deriv ε z + q z * ε z = -R z) ∧
      Tendsto (fun t => ‖ε (γ t)‖ / P₀ (γ t)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => ‖deriv ε (γ t)‖ / P₁ (γ t)) (𝓝[>] 0) (𝓝 0) ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        let integrand := fun t =>
          (U (γ t) * V (γ s) - V (γ t) * U (γ s)) / W (γ t) *
            (-R (γ t) - (p (γ t) - P (γ t)) * deriv ε (γ t) -
              (q (γ t) - Q (γ t)) * ε (γ t)) * deriv γ t
        let A := ∫ t in Ioc 0 s, k (γ t) * ‖R (γ t)‖ * ‖deriv γ t‖
        let B := ∫ t in Ioc 0 s, k (γ t) *
          (‖p (γ t) - P (γ t)‖ * P₁ (γ t) + ‖q (γ t) - Q (γ t)‖ * P₀ (γ t)) * ‖deriv γ t‖
        IntegrableOn integrand (Ioc 0 s) ∧ ε (γ s) = ∫ t in Ioc 0 s, integrand t ∧
          ‖ε (γ s)‖ / P₀ (γ s) ≤ A * Real.exp B ∧
            ‖deriv ε (γ s)‖ / P₁ (γ s) ≤ A * Real.exp B := by
  sorry

end Complex
