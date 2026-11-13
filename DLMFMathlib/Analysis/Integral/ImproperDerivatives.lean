/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Derivatives of improper tail integrals

An integrable function on a half-line has an improper tail integral. At an interior
continuity point its derivative is minus the integrand, by TauCeti's
`MeasureTheory.IntegrableOn.hasDerivAt_integral_Ioi`. The endpoint continuity result
below extends that API to the closed half-line.
-/

public section

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E} {a x : ℝ}
/-- An improper tail integral is continuous from within its closed half-line. -/
theorem IntegrableOn.continuousWithinAt_integral_Ioi (hf : IntegrableOn f (Ioi a))
    (hax : a ≤ x) (hfm : StronglyMeasurableAtFilter f (𝓝 x)) (hfx : ContinuousAt f x) :
    ContinuousWithinAt (fun y => ∫ t in Ioi y, f t) (Ici a) x := by
  have hi : IntervalIntegrable f volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hax]
    exact hf.mono_set Ioc_subset_Ioi_self
  have hc : ContinuousWithinAt
      (fun y => (∫ t in Ioi a, f t) - ∫ t in a..y, f t) (Ici a) x :=
    ((hasDerivAt_const x (∫ t in Ioi a, f t)).sub
    (intervalIntegral.integral_hasDerivAt_right hi hfm hfx)).continuousAt.continuousWithinAt
  apply hc.congr
  · intro y hy
    rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp (intervalIntegral.integral_Ioi_sub_Ioi hf hy)).symm
  · rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp (intervalIntegral.integral_Ioi_sub_Ioi hf hax)).symm
end MeasureTheory
