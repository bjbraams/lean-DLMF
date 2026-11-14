/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# Analytic coordinates for a coalescing saddle pair

Olver, *Asymptotics and Special Functions*, Chapter 9, §11,
pp. 351–352, synopsis O-9.13. A cubic critical point is reduced analytically
with its parameter; the theorem is local and asserts no global contour deformation.
-/

@[expose] public noncomputable section
open Set
namespace Complex

/-- The parameter-dependent cubic normal form at an order-three critical point.
Olver, Chapter 9, §11, pp. 351–352. The actual inverse coordinate and its
nonzero derivative are included, so transformed analytic amplitudes remain regular. -/
theorem exists_analytic_cubic_saddle_coordinates {p : ℂ → ℂ → ℂ}
    (hp : AnalyticAt ℂ (fun v : ℂ × ℂ => p v.1 v.2) (0, 0))
    (hfirst : deriv (p 0) 0 = 0) (hsecond : iteratedDeriv 2 (p 0) 0 = 0)
    (hthird : iteratedDeriv 3 (p 0) 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → ℂ, ∃ ζ c : ℂ → ℂ,
      AnalyticOnNhd ℂ (fun v : ℂ × ℂ => T v.1 v.2)
        (Metric.ball 0 ε ×ˢ Metric.ball 0 ε) ∧
      AnalyticOnNhd ℂ ζ (Metric.ball 0 ε) ∧ AnalyticOnNhd ℂ c (Metric.ball 0 ε) ∧
      T 0 0 = 0 ∧ ζ 0 = 0 ∧ c 0 = p 0 0 ∧
      iteratedDeriv 3 (p 0) 0 * deriv (T 0) 0 ^ 3 = 2 ∧
      (∀ a ∈ Metric.ball 0 ε, ∀ w ∈ Metric.ball 0 ε, deriv (T a) w ≠ 0 ∧
        p a (T a w) = w ^ 3 / 3 - ζ a * w + c a) := by
  sorry

/-- Matched cubic saddle values give the mean and difference identities exactly.
Olver, Chapter 9, §11, pp. 351–352. -/
theorem cubic_saddle_values {p T : ℂ → ℂ} {ζ c v : ℂ} (hv : v ^ 2 = ζ)
    (hplus : p (T v) = v ^ 3 / 3 - ζ * v + c)
    (hminus : p (T (-v)) = (-v) ^ 3 / 3 - ζ * (-v) + c) :
    (p (T v) + p (T (-v))) / 2 = c ∧
      p (T (-v)) - p (T v) = 4 / 3 * v ^ 3 := by
  rw [hplus, hminus, ← hv]
  constructor <;> ring

/-- An analytic original amplitude times the inverse-coordinate Jacobian is
analytic across both saddles and their coalescence. Olver, Chapter 9, §11. -/
theorem analyticAt_cubic_transformed_amplitude {q T : ℂ → ℂ → ℂ} {a w : ℂ}
    (hq : AnalyticAt ℂ (fun v : ℂ × ℂ => q v.1 v.2) (a, T a w))
    (hT : AnalyticAt ℂ (fun v : ℂ × ℂ => T v.1 v.2) (a, w)) :
    AnalyticAt ℂ (fun v : ℂ × ℂ => q v.1 (T v.1 v.2) * deriv (T v.1) v.2) (a, w) := by
  sorry

end Complex
