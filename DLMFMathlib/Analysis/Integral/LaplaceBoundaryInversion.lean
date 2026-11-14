/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Laplace inversion on the line of absolute convergence

Olver, *Asymptotics and Special Functions*, Chapter 8, Theorem 11.1,
pp. 315–316, synopsis O-8.14. The inversion limit is symmetric and retains
jumps. The inner integral is the defining unilateral Laplace transform.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Complex

/-- Symmetric Laplace inversion averages finite one-sided differentiable traces.
Olver, Chapter 8, Theorem 11.1, pp. 315–316. The contour may lie on the
absolute-convergence boundary. `Function.update` records each one-sided value
without forcing the original point value to equal either trace. -/
theorem tendsto_laplace_vertical_integral_of_one_sided_derivatives
    {f : ℝ → ℂ} {σ c t : ℝ} (ht : 0 < t) (hc : σ ≤ c)
    (hi : IntegrableOn (fun u => Real.exp (-σ * u) • f u) (Ioi 0))
    {left right dleft dright : ℂ}
    (hl : HasDerivWithinAt (Function.update f t left) dleft (Iic t) t)
    (hr : HasDerivWithinAt (Function.update f t right) dright (Ici t) t) :
    Tendsto (fun T : ℝ => (2 * Real.pi : ℂ)⁻¹ * ∫ y in -T..T,
      exp (((c : ℂ) + I * y) * t) *
        (∫ u in Ioi (0 : ℝ), exp (-((c : ℂ) + I * y) * u) * f u)) atTop
      (𝓝 ((left + right) / 2)) := by
  sorry

end Complex
