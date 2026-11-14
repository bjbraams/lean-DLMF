/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Analytic normal coordinates and level arcs at critical points

Olver, *Asymptotics and Special Functions*, Chapter 4, §10, pp. 135–137,
synopsis O-4.13. The normal coordinate handles arbitrary finite critical multiplicity,
not only simple saddles. All `2m` outgoing level rays are explicitly enumerated.
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Topology

namespace Complex

/-- An analytic function of finite order `m` has an invertible local coordinate in which its
increment is exactly `u^m`. The chosen tangent fixes the root normalization.
Olver, Chapter 4, §10, synopsis O-4.13. -/
theorem exists_analytic_critical_normalForm {p : ℂ → ℂ} {a c d : ℂ} {m : ℕ}
    (hp : AnalyticAt ℂ p a) (hm : 0 < m)
    (hvanish : ∀ k : ℕ, 0 < k → k < m → iteratedDeriv k p a = 0)
    (hc : iteratedDeriv m p a / (m.factorial : ℂ) = c) (hc₀ : c ≠ 0)
    (hd : c * d ^ m = 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 R) ∧ h 0 = a ∧ HasDerivAt h d 0 ∧
      Set.InjOn h (Metric.ball 0 R) ∧ h '' Metric.ball 0 R ∈ 𝓝 a ∧
      ∀ u ∈ Metric.ball (0 : ℂ) R, p (h u) = p a + u ^ m := by
  sorry

/-- The real-level set through an order-`m` critical point consists locally of `2m` regular
outgoing rays, with tangent factors `exp(i*k*pi/m)`. Adjacent tangent directions differ by
`pi/m`; opposite rays join into `m` arcs. Olver, Chapter 4, §10, synopsis O-4.13. -/
theorem exists_critical_level_arcs {p : ℂ → ℂ} {a c d : ℂ} {m : ℕ}
    (hp : AnalyticAt ℂ p a) (hm : 0 < m)
    (hvanish : ∀ k : ℕ, 0 < k → k < m → iteratedDeriv k p a = 0)
    (hc : iteratedDeriv m p a / (m.factorial : ℂ) = c) (hc₀ : c ≠ 0)
    (hd : c * d ^ m = 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 R) ∧ h 0 = a ∧
      Set.InjOn h (Metric.ball 0 R) ∧ h '' Metric.ball 0 R ∈ 𝓝 a ∧
      (∀ k : Fin (2 * m),
        HasDerivAt (fun t : ℝ => h (t * exp (I * ((k : ℕ) : ℝ) * Real.pi / m)))
          (d * exp (I * ((k : ℕ) : ℝ) * Real.pi / m)) 0 ∧
        ∀ t ∈ Ico (0 : ℝ) R,
          p (h (t * exp (I * ((k : ℕ) : ℝ) * Real.pi / m))) =
            p a + (-1 : ℂ) ^ (k : ℕ) * (t : ℂ) ^ m) ∧
      ∀ z ∈ h '' Metric.ball (0 : ℂ) R, (p z - p a).im = 0 ↔
        ∃ k : Fin (2 * m), ∃ t ∈ Ico (0 : ℝ) R,
          z = h (t * exp (I * ((k : ℕ) : ℝ) * Real.pi / m)) := by
  sorry

end Complex
