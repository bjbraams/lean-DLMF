/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen

/-!
# The complex Liouville normal transformation

The analytic fourth-root amplitude and square-root phase give the exact residual
identity, with the perturbation written explicitly in the original coefficient
and its derivatives. Source: Olver, *Asymptotics and Special Functions*,
Chapter 10, §1, pp. 362–363.
-/

@[expose] public noncomputable section

open Set

namespace Complex

/-- The exact normal transformation for `w''=(u^2*f+g)w`. The phase derivative
is nonzero by the fourth-root normalization; a local inverse turns the displayed
perturbation into a function of the phase. Olver, Chapter 10, §1, pp. 362–363. -/
theorem liouville_normal_equation {D : Set ℂ} (hD : IsOpen D)
    {f g amplitude phase control : ℂ → ℂ}
    (hdata : IsComplexLiouvilleGreenData f g amplitude phase control D)
    (u : ℂ) {z : ℂ} (hz : z ∈ D) {W : ℂ → ℂ} (hW : AnalyticAt ℂ W (phase z)) :
    let w := fun t => amplitude t * W (phase t)
    let ψ := g z / f z + (4 * f z * deriv (deriv f) z - 5 * deriv f z ^ 2) /
      (16 * f z ^ 3)
    deriv (deriv w) z - (u ^ 2 * f z + g z) * w z = amplitude z ^ (-3 : ℤ) *
      (deriv (deriv W) (phase z) - (u ^ 2 + ψ) * W (phase z)) := by
  sorry

end Complex
