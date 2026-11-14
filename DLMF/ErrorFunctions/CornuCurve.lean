/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Arc length and curvature of the Cornu curve

Temme, *Special Functions* (1996), §7.4, (7.26), pp. 182–185,
synopsis TEM-07-11. The curve uses Temme's scaled Fresnel functions
`C₁,S₁`, not the DLMF argument convention.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Real
namespace DLMF.Confluent

/-- The Cornu curve in Temme's parameter, with Euclidean rather than supremum norm,
Temme (7.26), synopsis TEM-07-11. -/
def Real.cornuCurve (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(fresnelC1 t).re, (fresnelS1 t).re]

/-- The Fresnel coordinate formula for the Cornu curve, Temme (7.26). -/
theorem Real.cornuCurve_def (t : ℝ) : Real.cornuCurve t =
    WithLp.toLp 2 ![(fresnelC1 t).re, (fresnelS1 t).re] := rfl

/-- Constant speed in Temme's Cornu parameter, Temme (7.26), TEM-07-11. -/
theorem Real.norm_deriv_cornuCurve (t : ℝ) :
    ‖deriv Real.cornuCurve t‖ = Real.sqrt (2 / Real.pi) := by
  sorry

/-- Arc length of the initial Cornu segment, Temme (7.26), synopsis TEM-07-11. -/
theorem Real.integral_norm_deriv_cornuCurve {t : ℝ} (ht : 0 ≤ t) :
    (∫ s : ℝ in (0 : ℝ)..t, ‖deriv Real.cornuCurve s‖) =
      Real.sqrt (2 / Real.pi) * t := by
  sorry

/-- Curvature of the Cornu curve, hence curvature equals `π` times arc length,
Temme (7.26), pp. 182–185, synopsis TEM-07-11. -/
theorem Real.curvature_cornuCurve {t : ℝ} (ht : 0 ≤ t) :
    |(deriv Real.cornuCurve t) 0 * (iteratedDeriv 2 Real.cornuCurve t) 1 -
      (deriv Real.cornuCurve t) 1 * (iteratedDeriv 2 Real.cornuCurve t) 0| /
        ‖deriv Real.cornuCurve t‖ ^ 3 = Real.sqrt (2 * Real.pi) * t := by
  sorry

end DLMF.Confluent
