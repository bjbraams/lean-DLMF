/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Regularized

/-!
# Vertical inverse-Laplace contours for incomplete gamma ratios

Temme, *Special Functions* (1996), Chapter 11, equation (11.20), pages 282–283.
The upward vertical tangent cancels the factor `i` in `2πi`. The normalized
principal power of `1+s` has no cut on the lines with real part greater than `-1`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory
open scoped Real

namespace DLMF.Confluent

/-- The inverse-Laplace kernel `exp(zs)/(s(1+s)^a)` on `s=c+it`.
Temme (11.20), synopsis TEM-11-06. -/
def gammaInversionKernel (a z c t : ℝ) : ℂ :=
  let s : ℂ := c + t * I
  exp (z * s) / (s * (1 + s) ^ (a : ℂ))

/-- The defining principal-power inverse-Laplace kernel. -/
theorem gammaInversionKernel_def (a z c t : ℝ) :
    gammaInversionKernel a z c t =
      exp (z * (c + t * I)) / ((c + t * I) * (1 + (c + t * I)) ^ (a : ℂ)) := rfl

/-- Positive shape gives absolute integrability on every admissible vertical line.
Temme (11.20), synopsis TEM-11-06. -/
theorem integrable_gammaInversionKernel {a z c : ℝ} (ha : 0 < a)
    (hz : 0 < z) (hc : -1 < c) (hc0 : c ≠ 0) :
    Integrable (gammaInversionKernel a z c) := by
  sorry

/-- The right-hand inversion line represents the lower regularized gamma ratio.
Temme (11.20), synopsis TEM-11-06. -/
theorem regularizedGamma_eq_vertical_integral {a z c : ℝ} (ha : 0 < a)
    (hz : 0 < z) (hc : 0 < c) :
    regularizedGamma a z = (2 * π : ℂ)⁻¹ *
      ∫ t : ℝ, gammaInversionKernel a z c t := by
  sorry

/-- The line between `-1` and zero represents minus the upper gamma ratio.
Temme (11.20), synopsis TEM-11-06. -/
theorem regularizedIncompleteGammaQ_eq_vertical_integral {a z c : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hc : -1 < c) (hc0 : c < 0) :
    regularizedIncompleteGammaQ a z = -(2 * π : ℂ)⁻¹ *
      ∫ t : ℝ, gammaInversionKernel a z c t := by
  sorry

end DLMF.Confluent
