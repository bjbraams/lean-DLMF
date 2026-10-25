/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Straight-segment primitives on star-convex domains

For `h` holomorphic on an open set `U` that is star-convex about the origin, the normalized
segment integral `w ↦ w ∫₀¹ h(tw) dt` is a primitive of `h` on `U`. Mathlib supplies primitives
on discs (`DifferentiableOn.isExactOn_ball`) and on the whole plane; this file treats the
star-convex case by differentiating under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`) and applying the
fundamental theorem of calculus to `t ↦ t h(tz)`.

## Main results

* `Complex.starPrim_hasDerivAt`: the derivative of the segment primitive.
* `Complex.starPrim_differentiableOn`: the segment primitive is holomorphic on `U`.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory Filter Metric
open scoped Interval Topology

namespace Complex

/-- Points of the segment `[0,w]` stay in a set star-convex about `0`. -/
lemma starPrim_mem {U : Set ℂ} (hs : StarConvex ℝ 0 U) {w : ℂ} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) : (t:ℂ)*w ∈ U := by
  have := hs hw (a := 1-t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  simpa [Complex.real_smul] using this

/-- **Segment primitives on star-convex domains.** If `h` is holomorphic on an open set `U`
star-convex about `0`, then `w ↦ w ∫₀¹ h(tw) dt` has complex derivative `h z` at every `z ∈ U`. -/
theorem starPrim_hasDerivAt {U : Set ℂ} (hU : IsOpen U) (hs : StarConvex ℝ 0 U) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => w * ∫ t in (0:ℝ)..1, h (t*w)) (h z) z := by
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  set r' := r/2
  have hr' : 0 < r' := by positivity
  have hcb : closedBall z r' ⊆ U := (closedBall_subset_ball (by simp [r']; linarith)).trans hrU
  -- compact set swept by the segments
  set K : Set ℂ := (fun p : ℝ × ℂ => (p.1:ℂ)*p.2) '' (Icc (0:ℝ) 1 ×ˢ closedBall z r')
  have hKc : IsCompact K := (isCompact_Icc.prod (isCompact_closedBall z r')).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    exact starPrim_mem hs (hcb hw) ht
  have hd : DifferentiableOn ℂ (deriv h) U :=
    ((hh.analyticOnNhd hU).deriv).differentiableOn
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hd.continuousOn.mono hKU)
  have hdiffAt : ∀ v ∈ U, HasDerivAt h (deriv h v) v := fun v hv =>
    (hh.differentiableAt (hU.mem_nhds hv)).hasDerivAt
  have hseg : ∀ w ∈ closedBall z r', ∀ t ∈ Icc (0:ℝ) 1, (t:ℂ)*w ∈ U := fun w hw t ht =>
    starPrim_mem hs (hcb hw) ht
  have hcont : ∀ w ∈ closedBall z r', ContinuousOn (fun t : ℝ => h ((t:ℂ)*w)) (Icc 0 1) := by
    intro w hw
    exact hh.continuousOn.comp (by fun_prop) fun t ht => hseg w hw t ht
  have hIoc : Ι (0:ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w (t : ℝ) => h ((t:ℂ)*w)) (F' := fun w (t : ℝ) => (t:ℂ) * deriv h ((t:ℂ)*w))
    (bound := fun _ => C) (μ := volume) (a := 0) (b := 1) (x₀ := z)
    (ball_mem_nhds z hr')
    (by
      filter_upwards [ball_mem_nhds z hr'] with w hw
      exact ((hcont w (ball_subset_closedBall hw)).mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    ((hcont z (mem_closedBall_self hr'.le)).intervalIntegrable_of_Icc zero_le_one)
    ((ContinuousOn.mul (by fun_prop) (hd.continuousOn.comp (by fun_prop) fun t ht =>
      hseg z (mem_closedBall_self hr'.le) t ht)).mono hIoc |>.aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun t ht w hw => by
      have ht' := hIoc ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      have := hC ((t:ℂ)*w) ⟨⟨t, w⟩, ⟨ht', ball_subset_closedBall hw⟩, rfl⟩
      calc t * ‖deriv h ((t:ℂ)*w)‖ ≤ 1 * C :=
            mul_le_mul ht'.2 this (norm_nonneg _) zero_le_one
        _ = C := one_mul C)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht w hw => by
      have h1 : HasDerivAt (fun x : ℂ => (t:ℂ)*x) (t:ℂ) w := by
        simpa using (hasDerivAt_id w).const_mul (t:ℂ)
      have := (hdiffAt _ (hseg w (ball_subset_closedBall hw) t (hIoc ht))).comp w h1
      exact this.congr_deriv (mul_comm _ _))
  have hprod := (hasDerivAt_id z).mul key.2
  refine hprod.congr_deriv ?_
  -- identify the derivative by the fundamental theorem of calculus
  have hφ : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => (t:ℂ) * h ((t:ℂ)*z))
      (h ((t:ℂ)*z) + (t:ℂ) * (deriv h ((t:ℂ)*z) * z)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => h ((t:ℂ)*z)) (deriv h ((t:ℂ)*z) * z) t := by
      have := ((hdiffAt _ (hseg z (mem_closedBall_self hr'.le) t ht)).comp (t:ℂ)
        ((hasDerivAt_id (t:ℂ)).mul_const z)).comp_ofReal
      simpa using this
    have h0 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 := h0.mul h1
    convert h2 using 1; ring
  have hint : IntervalIntegrable (fun t : ℝ => h ((t:ℂ)*z) + (t:ℂ) * (deriv h ((t:ℂ)*z) * z)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    refine (hcont z (mem_closedBall_self hr'.le)).add (ContinuousOn.mul (by fun_prop) ?_)
    exact (hd.continuousOn.comp (by fun_prop) fun t ht => hseg z (mem_closedBall_self hr'.le) t ht).mul
      continuousOn_const
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ hint
  have hi1 : IntervalIntegrable (fun t : ℝ => h ((t:ℂ)*z)) volume 0 1 := (hcont z (mem_closedBall_self hr'.le)).intervalIntegrable_of_Icc zero_le_one
  have hi2 : IntervalIntegrable (fun t : ℝ => (t:ℂ) * (deriv h ((t:ℂ)*z) * z)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one (ContinuousOn.mul (by fun_prop) ?_)
    exact (hd.continuousOn.comp (by fun_prop) fun t ht => hseg z (mem_closedBall_self hr'.le) t ht).mul
      continuousOn_const
  rw [intervalIntegral.integral_add hi1 hi2] at hF
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, sub_zero] at hF
  rw [← hF]
  simp only [id, one_mul]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t; ring

/-- The segment primitive is holomorphic on the star-convex domain. -/
theorem starPrim_differentiableOn {U : Set ℂ} (hU : IsOpen U) (hs : StarConvex ℝ 0 U)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (fun w => w * ∫ t in (0:ℝ)..1, h (t*w)) U := fun _ hz =>
  (starPrim_hasDerivAt hU hs hh hz).differentiableAt.differentiableWithinAt

end Complex
