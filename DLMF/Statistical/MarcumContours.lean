/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.MarcumQ

/-!
# Vertical inversion contours for the Marcum functions

Temme, *Special Functions* (1996), Chapter 11, equations (11.67)–(11.69),
pages 300–301. The integrals use the upward vertical parametrization `c + it`;
its tangent `i` cancels the `i` in `2πi`. Principal powers are used, with their
positive normalization on the positive real axis.
-/

@[expose] public noncomputable section

open Complex MeasureTheory
open scoped Real

namespace DLMF.Statistical

/-- The vertical Marcum inversion kernel with the contour parameter derivative removed.
Temme (11.67)–(11.69), synopsis TEM-11-17. -/
def marcumVerticalKernel (μ x y c t : ℝ) : ℂ :=
  let s : ℂ := c + t * I
  exp (x / s + y * s) * s ^ (-(μ : ℂ)) / (1 - s)

/-- The defining principal-power inversion kernel. -/
theorem marcumVerticalKernel_def (μ x y c t : ℝ) :
    marcumVerticalKernel μ x y c t =
      exp (x / (c + t * I) + y * (c + t * I)) *
        (c + t * I) ^ (-(μ : ℂ)) / (1 - (c + t * I)) := rfl

/-- The vertical contours are absolutely integrable for positive order.
Temme (11.67)–(11.69), synopsis TEM-11-17. -/
theorem integrable_marcumVerticalKernel {μ x y c : ℝ} (hμ : 0 < μ)
    (hx : 0 < x) (hy : 0 < y) (hc : 0 < c) (hc1 : c ≠ 1) :
    Integrable (marcumVerticalKernel μ x y c) := by
  sorry

/-- The upward contour to the left of the pole represents the upper Marcum function.
Temme (11.67)–(11.69), synopsis TEM-11-17. -/
theorem marcumQ_eq_vertical_integral {μ x y c : ℝ} (hμ : 0 < μ)
    (hx : 0 < x) (hy : 0 < y) (hc : 0 < c) (hc1 : c < 1) :
    (marcumQ μ x y : ℂ) = exp (-(x : ℂ) - y) / (2 * π) *
      ∫ t : ℝ, marcumVerticalKernel μ x y c t := by
  sorry

/-- Moving the upward contour to the right of the pole represents minus the lower tail.
Temme (11.67)–(11.69), synopsis TEM-11-17. -/
theorem marcumP_eq_vertical_integral {μ x y c : ℝ} (hμ : 0 < μ)
    (hx : 0 < x) (hy : 0 < y) (hc : 1 < c) :
    (marcumP μ x y : ℂ) = -exp (-(x : ℂ) - y) / (2 * π) *
      ∫ t : ℝ, marcumVerticalKernel μ x y c t := by
  sorry

end DLMF.Statistical
