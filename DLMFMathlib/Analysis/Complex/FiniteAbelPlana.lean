/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Order.Filter.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The finite-strip Abel–Plana identity

Olver, *Asymptotics and Special Functions*, Chapter 8, §§2–3,
pp. 289–292, synopsis O-8.05. Boundary continuity and interior holomorphy
are separate, and convergence of the vertical integral is an explicit hypothesis.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
namespace Complex

/-- The full finite-strip Abel–Plana identity with a symmetric ordinary vertical
limit at both endpoints. Olver, Chapter 8, §§2–3, pp. 289–292. No derivative extension to the
boundary and no absolute convergence of the vertical integral are assumed. -/
theorem sum_Icc_sub_endpoints_eq_integral_add_vertical_limit
    {f : ℂ → ℂ} {a n : ℤ} (han : a < n)
    (hc : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n})
    (hd : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hgrowth : ∀ ε > 0, ∃ Y : ℝ, ∀ z : ℂ,
      (a : ℝ) ≤ z.re → z.re ≤ n → Y ≤ |z.im| →
        ‖f z‖ ≤ ε * Real.exp (2 * Real.pi * |z.im|))
    {V : ℂ} (hv : Tendsto (fun p : ℝ × ℝ => ∫ y in p.1..p.2,
      (f (a + I * y) - f (a - I * y) - f (n + I * y) + f (n - I * y)) /
        (Real.exp (2 * Real.pi * y) - 1))
          (nhdsWithin (0 : ℝ) (Ioi 0) ×ˢ (atTop : Filter ℝ)) (nhds V)) :
    (∑ j ∈ Finset.Icc a n, f j) - (f a + f n) / 2 =
      (∫ x in (a : ℝ)..(n : ℝ), f x) + I * V := by
  sorry

end Complex
