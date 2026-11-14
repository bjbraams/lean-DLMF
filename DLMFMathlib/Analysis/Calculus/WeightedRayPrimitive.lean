/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Regularity of weighted ray primitives

The integrable power `t^alpha`, `alpha>-1`, gives a removable primitive at the
ray's base point. Real derivatives may be passed under the integral at every
available order, and the differential identity gives one additional derivative
off the base point. The exponent `-1/2` is Olver's weighted primitive.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
Lemma 7.1, p. 410.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Real Topology

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The weighted radial primitive with real integrable exponent. Its value at
zero is the normalized weighted constant integral; values outside convergence
hypotheses use the totalized Bochner integral. Olver, Chapter 11, Lemma 7.1,
p. 410, generalized from exponent `-1/2` to every `alpha>-1`. -/
def weightedRayPrimitive (α : ℝ) (h : E → F) (x : E) : F :=
  ∫ t : ℝ in 0..1, t ^ α • h (t • x)

/-- The defining weighted unit-segment integral. -/
theorem weightedRayPrimitive_def (α : ℝ) (h : E → F) (x : E) :
    weightedRayPrimitive α h x = ∫ t : ℝ in 0..1, t ^ α • h (t • x) := rfl

variable [CompleteSpace F]

/-- Continuous data on a star-shaped domain give an integrable weighted kernel.
Olver, Chapter 11, Lemma 7.1, p. 410. -/
theorem intervalIntegrable_weightedRayPrimitive {α : ℝ} (hα : -1 < α)
    {h : E → F} {D : Set E} (hD : StarConvex ℝ 0 D) (hh : ContinuousOn h D)
    {x : E} (hx : x ∈ D) :
    IntervalIntegrable (fun t : ℝ => t ^ α • h (t • x)) volume 0 1 := by
  sorry

/-- The base-point value is `h(0)/(alpha+1)`, hence `2h(0)` for exponent `-1/2`.
Olver, Chapter 11, Lemma 7.1, p. 410. -/
theorem weightedRayPrimitive_zero {α : ℝ} (hα : -1 < α) (h : E → F) :
    weightedRayPrimitive α h 0 = (α + 1)⁻¹ • h 0 := by
  sorry

/-- The weighted primitive preserves all real differentiability orders available
at the base point as well as away from it. Olver, Chapter 11, Lemma 7.1, p. 410. -/
theorem contDiffOn_weightedRayPrimitive {α : ℝ} (hα : -1 < α)
    {h : ℝ → F} {D : Set ℝ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D)
    {n : ℕ∞} (hh : ContDiffOn ℝ n h D) :
    ContDiffOn ℝ n (weightedRayPrimitive α h) D := by
  sorry

/-- Every available derivative is the weighted integral with exponent `alpha+k`.
Olver, Chapter 11, Lemma 7.1, p. 410. -/
theorem iteratedDeriv_weightedRayPrimitive {α : ℝ} (hα : -1 < α)
    {h : ℝ → F} {D : Set ℝ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D)
    {n : ℕ∞} (hh : ContDiffOn ℝ n h D) {k : ℕ} (hk : (k : ℕ∞) ≤ n)
    {x : ℝ} (hx : x ∈ D) :
    iteratedDeriv k (weightedRayPrimitive α h) x =
      ∫ t : ℝ in 0..1, t ^ (α + k) • iteratedDeriv k h (t * x) := by
  sorry

/-- The Euler differential identity for continuous data, off the base point.
At exponent `-1/2` it is `2xI'+I=2h`. Olver, Chapter 11, Lemma 7.1, p. 410. -/
theorem weightedRayPrimitive_differential_equation {α : ℝ} (hα : -1 < α)
    {h : ℝ → F} {D : Set ℝ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D)
    (hh : ContinuousOn h D) {x : ℝ} (hx : x ∈ D) (hxzero : x ≠ 0) :
    x • deriv (weightedRayPrimitive α h) x +
      (α + 1) • weightedRayPrimitive α h x = h x := by
  sorry

/-- Away from the base point the primitive has one extra derivative, including
the case of merely continuous input data. Olver, Chapter 11, Lemma 7.1, p. 410. -/
theorem contDiffOn_weightedRayPrimitive_succ {α : ℝ} (hα : -1 < α)
    {h : ℝ → F} {D : Set ℝ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D)
    {n : ℕ} (hh : ContDiffOn ℝ n h D) :
    ContDiffOn ℝ (n + 1) (weightedRayPrimitive α h) (D \ {0}) := by
  sorry

/-- Analytic complex data give an analytic weighted primitive on an open
star-shaped domain, including zero. This is the analytic form used in turning-
point coefficient recursions. Olver, Chapter 11, §7, pp. 409–410. -/
theorem analyticOnNhd_weightedRayPrimitive {α : ℝ} (hα : -1 < α)
    {h : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D)
    (hh : AnalyticOnNhd ℂ h D) : AnalyticOnNhd ℂ (weightedRayPrimitive α h) D := by
  sorry

end MeasureTheory
