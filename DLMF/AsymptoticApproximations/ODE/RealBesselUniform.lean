/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.RealBesselExpansion
public import DLMFMathlib.Analysis.ODE.SimplePoleRealUniform

/-!
# All-orders and order-uniform real Bessel comparison solutions

A single exact solution is chosen before the truncation index. Compact-order
uniformity retains uniform weighted coefficient variations. The leading modified
Bessel result has a separate integrability criterion and allows every nonnegative
order; no such unbounded-order claim is made for the oscillatory estimates.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
§5 and Exercise 5.1, pp. 447–448.
-/

@[expose] public noncomputable section

open Complex Set Filter ODE MeasureTheory
open scoped Real Topology

namespace DLMF.AsymptoticApproximations.Real

/-- The complete compound expansions hold for one exact solution per parameter,
with constants uniform on every prescribed compact order interval. The variation
hypothesis is the source's uniform endpoint condition; differentiated tails give
it via the coefficient-tail API. `sign=0` is the positive interval and `sign=1`
the negative interval. Olver, Chapter 12, §5.2, pp. 447–448. -/
theorem exists_allOrders_real_bessel_comparison
    {a b : EReal} (ha : a < 0) (hb : 0 < b) {N : ℝ} (hN : 0 ≤ N)
    {ψ : ℝ → ℂ} (A B : ℝ → ℕ → ℝ → ℂ)
    (hcoeff : ∀ ν ∈ Icc 0 N, IsSimplePoleCoefficientSequence ψ ν (A ν) (B ν)
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hinitial : ∀ ν ∈ Icc 0 N, ∀ s, A ν s 0 = if s = 0 then 1 else 0)
    (hvar : ∀ s : ℕ, ∃ V : ℝ, 0 ≤ V ∧ ∀ ν ∈ Icc 0 N,
      BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B ν s x)
        {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} ∧
      (eVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B ν s x)
        {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}).toReal ≤ V) :
    ∃ W : Fin 2 → Fin 2 → ℝ → ℝ → ℝ → ℂ,
      (∀ (sign k : Fin 2) (ν u : ℝ), ν ∈ Icc 0 N → 0 < u →
        let D := if sign = 0 then {x : ℝ | 0 < x ∧ (x : EReal) < b}
          else {x : ℝ | a < (x : EReal) ∧ x < 0}
        ContDiffOn ℝ 2 (W sign k ν u) D ∧ ∀ x ∈ D,
          deriv (deriv (W sign k ν u)) x =
            (u ^ 2 / (4 * x) + (ν ^ 2 - 1) / (4 * x ^ 2) + ψ x / x) * W sign k ν u x) ∧
      ∀ n : ℕ, ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
        ∀ (sign k : Fin 2) (ν u x : ℝ), ν ∈ Icc 0 N → R ≤ u →
          (if sign = 0 then 0 < x ∧ (x : EReal) < b else a < (x : EReal) ∧ x < 0) →
          let pair := if sign = 0 then BesselComparison.positivePair k ν u
            else BesselComparison.negativePair k ν u
          let E := if sign = 0 then ‖(pair x).1‖ else
            Real.sqrt |x| * BesselEnvelope.modulus ν (u * Real.sqrt |x|) *
              if k = 0 then (BesselEnvelope.weight ν (u * Real.sqrt |x|))⁻¹
              else BesselEnvelope.weight ν (u * Real.sqrt |x|)
          ‖W sign k ν u x - simplePolePartialSum (A ν) (B ν)
            (fun t => (pair t).1) (fun t => (pair t).2) u n x‖ ≤ C * E / u ^ (2 * n + 1) := by
  sorry

/-- The leading positive-variable approximation is uniform even for unbounded
nonnegative order under one order-independent weighted integrability condition.
The two exact solutions are selected separately at their opposite endpoints.
Olver, Chapter 12, Exercise 5.1, p. 448. -/
theorem exists_uniform_nonnegative_order_bessel_comparison
    {β : EReal} (hβ : 0 < β) {ψ : ℝ → ℂ}
    (hψ : ContinuousOn ψ {x : ℝ | 0 ≤ x ∧ (x : EReal) < β})
    (hint : IntegrableOn (fun x : ℝ => ‖ψ x‖ / Real.sqrt x)
      {x : ℝ | 0 < x ∧ (x : EReal) < β}) :
    ∃ (W : Fin 2 → ℝ → ℝ → ℝ → ℂ) (C R : ℝ), 0 < C ∧ 0 < R ∧
      ∀ (k : Fin 2) (ν u : ℝ), 0 ≤ ν → R ≤ u →
        ContDiffOn ℝ 2 (W k ν u) {x : ℝ | 0 < x ∧ (x : EReal) < β} ∧
        ∀ x : ℝ, 0 < x → (x : EReal) < β →
          deriv (deriv (W k ν u)) x =
            (u ^ 2 / (4 * x) + (ν ^ 2 - 1) / (4 * x ^ 2) + ψ x / x) * W k ν u x ∧
          ‖W k ν u x / (BesselComparison.positivePair k ν u x).1 - 1‖ ≤ C / u := by
  sorry

end DLMF.AsymptoticApproximations.Real
