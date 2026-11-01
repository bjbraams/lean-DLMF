/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Anger and Weber functions (DLMF §11.10)

The Anger function `𝐉_ν(z) = π⁻¹ ∫₀^π cos(νθ - z sin θ) dθ` and the Weber function
`𝐄_ν(z) = π⁻¹ ∫₀^π sin(νθ - z sin θ) dθ` (DLMF 11.10.1–11.10.2), with their basic calculus.

## Main definitions

* `angerJ`, `weberE`: the Anger and Weber functions (DLMF 11.10.1–11.10.2).

## Main results

* `hasDerivAt_intervalIntegral_of_continuous`: differentiation under a compact integral.
* `angerJ_entire`, `angerJ_entire_order`, `weberE_entire`, `weberE_entire_order`: both functions
  are entire in the argument and in the order.
* `hasDerivAt_angerJ_shift`, `hasDerivAt_weberE_shift`: the derivatives DLMF 11.10.34–11.10.35.
* `angerJ_recurrence_aux`, `weberE_recurrence_aux`: the recurrences DLMF 11.10.32–11.10.33.
* `angerJ_double_integral`: DLMF 11.10.3.
* `angerJ_ode`, `weberE_ode`: the inhomogeneous Bessel equations DLMF 11.10.5–11.10.7.
* `angerJ_neg`, `weberE_neg`: DLMF 11.10.12.
* `anger_weber`, `weber_anger`: DLMF 11.10.13–11.10.14.

## Implementation notes

The series, the associated Anger–Weber function `𝐀_ν` and the relations with Bessel functions
are in `DLMF.Struve.AngerWeber.IntegralAndSeries`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology

namespace DLMF.Struve

/-- Anger function defined by the finite cosine integral `π⁻¹ ∫₀π cos (νθ-z sin θ) dθ`. -/
@[dlmf 11.10.E1]
def angerJ (ν z : ℂ) : ℂ :=
  1/π*∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ)

/-- Differentiation under the integral sign over a compact interval for a jointly continuous
integrand with jointly continuous complex derivative. -/
theorem hasDerivAt_intervalIntegral_of_continuous {F F' : ℂ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ z t, HasDerivAt (fun w => F w t) (F' z t) z) (a b : ℝ) (z₀ : ℂ) :
    HasDerivAt (fun z => ∫ t in a..b, F z t) (∫ t in a..b, F' z₀ t) z₀ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn
    hF'.continuousOn
  have hFc : ∀ z, Continuous (F z) := fun z => hF.comp (Continuous.prodMk_right z)
  have hF'c : ∀ z, Continuous (F' z) := fun z => hF'.comp (Continuous.prodMk_right z)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall fun z => (hFc z).aestronglyMeasurable)
    ((hFc z₀).intervalIntegrable _ _) (hF'c z₀).aestronglyMeasurable ?_ intervalIntegrable_const
    (Eventually.of_forall fun t _ z _ => hd z t)).2
  refine Eventually.of_forall fun t ht z hz => hC (z, t) ⟨Metric.ball_subset_closedBall hz, ?_⟩
  exact uIoc_subset_uIcc ht

/-- Derivative of the Anger function in its argument, as an integral. -/
theorem angerJ_hasDerivAt_arg (ν z : ℂ) :
    HasDerivAt (angerJ ν)
      (1/π*∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ)*Real.sin θ) z := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun z (θ : ℝ) => cos (ν*θ-z*Real.sin θ))
    (F' := fun z (θ : ℝ) => sin (ν*θ-z*Real.sin θ)*Real.sin θ) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π z).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((Real.sin t : ℂ))).const_sub (ν*t) |>.ccos
  convert this using 1
  ring

/-- Derivative of the Anger function in its order, as an integral. -/
theorem angerJ_hasDerivAt_order (ν z : ℂ) :
    HasDerivAt (fun ν => angerJ ν z)
      (1/π*∫ θ : ℝ in 0..π, -(sin (ν*θ-z*Real.sin θ)*θ)) ν := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun ν (θ : ℝ) => cos (ν*θ-z*Real.sin θ))
    (F' := fun ν (θ : ℝ) => -(sin (ν*θ-z*Real.sin θ)*θ)) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π ν).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((t : ℂ))).sub_const (z*Real.sin t) |>.ccos
  convert this using 1
  ring

/-- Entire dependence on the argument. -/
theorem angerJ_entire (ν : ℂ) :
    Differentiable ℂ (angerJ ν) := by
  exact fun z => (angerJ_hasDerivAt_arg ν z).differentiableAt

/-- Entire dependence on the order. -/
theorem angerJ_entire_order (z : ℂ) :
    Differentiable ℂ (fun ν => angerJ ν z) := by
  exact fun ν => (angerJ_hasDerivAt_order ν z).differentiableAt

/-- Weber function defined by the finite sine integral `π⁻¹ ∫₀π sin (νθ-z sin θ) dθ`. -/
@[dlmf 11.10.E2]
def weberE (ν z : ℂ) : ℂ :=
  1/π*∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ)

/-- Derivative of the Weber function in its argument, as an integral. -/
theorem weberE_hasDerivAt_arg (ν z : ℂ) :
    HasDerivAt (weberE ν)
      (1/π*∫ θ : ℝ in 0..π, -(cos (ν*θ-z*Real.sin θ)*Real.sin θ)) z := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun z (θ : ℝ) => sin (ν*θ-z*Real.sin θ))
    (F' := fun z (θ : ℝ) => -(cos (ν*θ-z*Real.sin θ)*Real.sin θ)) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π z).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((Real.sin t : ℂ))).const_sub (ν*t) |>.csin
  convert this using 1
  ring

/-- Derivative of the Weber function in its order, as an integral. -/
theorem weberE_hasDerivAt_order (ν z : ℂ) :
    HasDerivAt (fun ν => weberE ν z)
      (1/π*∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ)*θ) ν := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun ν (θ : ℝ) => sin (ν*θ-z*Real.sin θ))
    (F' := fun ν (θ : ℝ) => cos (ν*θ-z*Real.sin θ)*θ) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π ν).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((t : ℂ))).sub_const (z*Real.sin t) |>.csin
  convert this using 1
  ring

/-- Entire dependence on the argument. -/
theorem weberE_entire (ν : ℂ) :
    Differentiable ℂ (weberE ν) := by
  exact fun z => (weberE_hasDerivAt_arg ν z).differentiableAt

/-- Entire dependence on the order. -/
theorem weberE_entire_order (z : ℂ) :
    Differentiable ℂ (fun ν => weberE ν z) := by
  exact fun ν => (weberE_hasDerivAt_order ν z).differentiableAt

/-- Continuous functions are interval integrable on `[0, π]`. -/
theorem intervalIntegrable_zero_pi (f : ℝ → ℂ) (hf : Continuous f) :
    IntervalIntegrable f volume 0 π :=
  hf.intervalIntegrable _ _

/-- The complex number `π` is nonzero. -/
theorem pi_complex_ne_zero : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero

/-- Derivative of the Anger function via the shifted orders (DLMF 11.10.34). -/
theorem hasDerivAt_angerJ_shift (ν z : ℂ) :
    HasDerivAt (angerJ ν) ((angerJ (ν-1) z-angerJ (ν+1) z)/2) z := by
  convert angerJ_hasDerivAt_arg ν z using 1
  unfold angerJ
  rw [← mul_sub, mul_div_assoc, ← intervalIntegral.integral_sub
      (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop)),
    ← intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
    show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, cos_sub, cos_add,
    ← ofReal_sin]
  ring

/-- Derivative of the Weber function via the shifted orders (DLMF 11.10.35). -/
theorem hasDerivAt_weberE_shift (ν z : ℂ) :
    HasDerivAt (weberE ν) ((weberE (ν-1) z-weberE (ν+1) z)/2) z := by
  convert weberE_hasDerivAt_arg ν z using 1
  unfold weberE
  rw [← mul_sub, mul_div_assoc, ← intervalIntegral.integral_sub
      (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop)),
    ← intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
    show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, sin_sub, sin_add,
    ← ofReal_sin]
  ring

/-- Derivative of the phase `νθ - z sin θ` in `θ`. -/
theorem hasDerivAt_phase (ν z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ν*(t:ℂ)-z*Real.sin t) (ν-z*Real.cos t) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => ((Real.sin t : ℝ):ℂ)) (Real.cos t) t :=
    (Real.hasDerivAt_sin t).ofReal_comp
  convert (h1.const_mul ν).sub (h2.const_mul z) using 1
  ring

/-- The Anger recurrence (DLMF 11.10.32), proved by integration of `d/dθ sin(νθ - z sin θ)`. -/
lemma angerJ_recurrence_aux (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    angerJ (ν-1) z+angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν)) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => sin (ν*(t:ℂ)-z*Real.sin t))
    (f' := fun t : ℝ => cos (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t))
    (a := 0) (b := π) (fun t _ => (Complex.hasDerivAt_sin _).comp t (hasDerivAt_phase ν z t))
        (intervalIntegrable_zero_pi _ (by fun_prop))
  have e1 : (∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t)) =
      ν*(∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)) -
        z*∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)*Real.cos t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
          (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1; funext t; ring
  have e2 : angerJ (ν-1) z+angerJ (ν+1) z =
      1/π*(2*∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)*Real.cos t) := by
    unfold angerJ
    rw [← mul_add, ← intervalIntegral.integral_add
        (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
      show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, cos_sub, cos_add,
      ← ofReal_cos]
    ring
  simp only [Real.sin_pi, Real.sin_zero, ofReal_zero, mul_zero, sub_zero, sin_zero] at hftc
  rw [e1] at hftc
  rw [e2]
  unfold angerJ
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  rw [mul_comm (π:ℂ) ν]
  linear_combination (-1:ℂ)*hftc

/-- The Weber recurrence (DLMF 11.10.33), proved by integration of `d/dθ cos(νθ - z sin θ)`. -/
lemma weberE_recurrence_aux (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    weberE (ν-1) z+weberE (ν+1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν)) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -cos (ν*(t:ℂ)-z*Real.sin t))
    (f' := fun t : ℝ => sin (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t))
    (a := 0) (b := π) (fun t _ => by
      convert ((Complex.hasDerivAt_cos _).comp t (hasDerivAt_phase ν z t)).neg using 1
          <;> first | rfl | ring) (intervalIntegrable_zero_pi _ (by fun_prop))
  have e1 : (∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t)) =
      ν*(∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)) -
        z*∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)*Real.cos t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
          (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1; funext t; ring
  have e2 : weberE (ν-1) z+weberE (ν+1) z =
      1/π*(2*∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)*Real.cos t) := by
    unfold weberE
    rw [← mul_add, ← intervalIntegral.integral_add
        (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
      show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, sin_sub, sin_add,
      ← ofReal_cos]
    ring
  simp only [Real.sin_pi, Real.sin_zero, ofReal_zero, mul_zero, sub_zero, cos_zero] at hftc
  rw [e1] at hftc
  rw [e2]
  unfold weberE
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  rw [mul_comm (π:ℂ) ν]
  linear_combination (-1:ℂ)*hftc

/-- Identity under the stated parameter and domain assumptions: `(1/π*∫ θ : ℝ in 0..2*π, cos
(ν*θ-z*Real.sin θ)) = (1+cos (2*π*ν))*angerJ ν z+sin (2*π*ν)*weberE ν z`. -/
@[dlmf 11.10.E3]
theorem angerJ_double_integral (ν z : ℂ) :
    (1/π*∫ θ : ℝ in 0..2*π, cos (ν*θ-z*Real.sin θ))
        = (1+cos (2*π*ν))*angerJ ν z+sin (2*π*ν)*weberE ν z := by
  have hc : Continuous (fun θ : ℝ => cos (ν*θ-z*Real.sin θ)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => cos (ν*θ-z*Real.sin θ)) (a := 0) (b := π) (2*π)
  rw [show 2*π-π = π by ring, sub_zero] at this
  rw [← this]
  have e : (∫ x in (0:ℝ)..π, cos (ν*((2*π-x:ℝ):ℂ)-z*Real.sin (2*π-x))) =
      cos (2*π*ν)*(∫ x in (0:ℝ)..π, cos (ν*x-z*Real.sin x)) +
        sin (2*π*ν)*∫ x in (0:ℝ)..π, sin (ν*x-z*Real.sin x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
          (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Real.sin_two_pi_sub]
    rw [show ν*((2*π-θ:ℝ):ℂ)-z*((-Real.sin θ:ℝ):ℂ) = 2*π*ν-(ν*θ-z*Real.sin θ) by push_cast; ring,
      cos_sub]
  rw [e]; unfold angerJ weberE; ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (angerJ ν)
z+deriv (angerJ ν) z/z+(1-ν^2/z^2)*angerJ ν z = (z-ν)/(π*z^2)*sin (π*ν)`. -/
@[dlmf 11.10.E5, dlmf 11.10.E6]
theorem angerJ_ode (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    iteratedDeriv 2 (angerJ ν) z+deriv (angerJ ν) z/z+(1-ν^2/z^2)*angerJ ν z
        = (z-ν)/(π*z^2)*sin (π*ν) := by
  have hD : deriv (angerJ ν) = fun w => (angerJ (ν-1) w-angerJ (ν+1) w)/2 :=
    funext fun w => (hasDerivAt_angerJ_shift ν w).deriv
  have h2 : iteratedDeriv 2 (angerJ ν) z =
      ((angerJ (ν-1-1) z - angerJ ν z)/2 - (angerJ ν z - angerJ (ν+1+1) z)/2)/2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hD]
    have := ((hasDerivAt_angerJ_shift (ν-1) z).sub (hasDerivAt_angerJ_shift (ν+1) z)).div_const 2
    rw [sub_add_cancel, add_sub_cancel_right] at this
    exact this.deriv
  have r1 := angerJ_recurrence_aux (ν-1) hz
  have r2 := angerJ_recurrence_aux (ν+1) hz
  have r3 := angerJ_recurrence_aux ν hz
  rw [sub_add_cancel, show π*(ν-1) = π*ν-π by ring, sin_sub_pi] at r1
  rw [add_sub_cancel_right, show π*(ν+1) = π*ν+π by ring, sin_add_pi] at r2
  rw [h2, (hasDerivAt_angerJ_shift ν z).deriv]
  linear_combination (norm := skip) (1/4:ℂ)*r1 + (1/4:ℂ)*r2 + ν/(2*z)*r3
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (weberE ν)
z+deriv (weberE ν) z/z+(1-ν^2/z^2)*weberE ν z = -(z+ν+(z-ν)*cos (π*ν))/(π*z^2)`. -/
@[dlmf 11.10.E5, dlmf 11.10.E7]
theorem weberE_ode (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    iteratedDeriv 2 (weberE ν) z+deriv (weberE ν) z/z+(1-ν^2/z^2)*weberE ν z
        = -(z+ν+(z-ν)*cos (π*ν))/(π*z^2) := by
  have hD : deriv (weberE ν) = fun w => (weberE (ν-1) w-weberE (ν+1) w)/2 :=
    funext fun w => (hasDerivAt_weberE_shift ν w).deriv
  have h2 : iteratedDeriv 2 (weberE ν) z =
      ((weberE (ν-1-1) z - weberE ν z)/2 - (weberE ν z - weberE (ν+1+1) z)/2)/2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hD]
    have := ((hasDerivAt_weberE_shift (ν-1) z).sub (hasDerivAt_weberE_shift (ν+1) z)).div_const 2
    rw [sub_add_cancel, add_sub_cancel_right] at this
    exact this.deriv
  have r1 := weberE_recurrence_aux (ν-1) hz
  have r2 := weberE_recurrence_aux (ν+1) hz
  have r3 := weberE_recurrence_aux ν hz
  rw [sub_add_cancel, show π*(ν-1) = π*ν-π by ring, cos_sub_pi] at r1
  rw [add_sub_cancel_right, show π*(ν+1) = π*ν+π by ring, cos_add_pi] at r2
  rw [h2, (hasDerivAt_weberE_shift ν z).deriv]
  linear_combination (norm := skip) (1/4:ℂ)*r1 + (1/4:ℂ)*r2 + ν/(2*z)*r3
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `angerJ ν (-z) = angerJ (-ν) z`. -/
@[dlmf 11.10.E12]
theorem angerJ_neg (ν z : ℂ) :
    angerJ ν (-z) = angerJ (-ν) z := by
  unfold angerJ
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [show (-ν)*(θ:ℂ)-z*Real.sin θ=-(ν*θ-(-z)*Real.sin θ) by ring, cos_neg]

/-- Identity under the stated parameter and domain assumptions: `weberE ν (-z) = -weberE (-ν) z`. -/
@[dlmf 11.10.E12]
theorem weberE_neg (ν z : ℂ) :
    weberE ν (-z) = -weberE (-ν) z := by
  unfold weberE
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [show (-ν)*(θ:ℂ)-z*Real.sin θ=-(ν*θ-(-z)*Real.sin θ) by ring, sin_neg, neg_neg]

/-- Identity under the stated parameter and domain assumptions: `sin (π*ν)*angerJ ν z = cos
(π*ν)*weberE ν z-weberE (-ν) z`. -/
@[dlmf 11.10.E13]
theorem anger_weber (ν z : ℂ) :
    sin (π*ν)*angerJ ν z = cos (π*ν)*weberE ν z-weberE (-ν) z := by
  have h : weberE (-ν) z = cos (π*ν)*weberE ν z - sin (π*ν)*angerJ ν z := by
    unfold weberE angerJ
    have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => sin ((-ν)*θ-z*Real.sin θ)) (a := 0) (b := π) π
    simp only [sub_self, sub_zero] at this
    have key : (∫ θ : ℝ in 0..π, sin ((-ν)*θ-z*Real.sin θ)) =
        cos (π*ν)*(∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ))
            - sin (π*ν)*∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ) := by
      rw [← this, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub
            (intervalIntegrable_zero_pi _ (by fun_prop))
                (intervalIntegrable_zero_pi _ (by fun_prop))]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [Real.sin_pi_sub]
      rw [show (-ν)*((π-θ:ℝ):ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-π*ν by push_cast; ring, sin_sub]
      ring
    rw [key]; ring
  rw [h]; ring

/-- Identity under the stated parameter and domain assumptions: `sin (π*ν)*weberE ν z = angerJ
(-ν) z-cos (π*ν)*angerJ ν z`. -/
@[dlmf 11.10.E14]
theorem weber_anger (ν z : ℂ) :
    sin (π*ν)*weberE ν z = angerJ (-ν) z-cos (π*ν)*angerJ ν z := by
  have h : angerJ (-ν) z = cos (π*ν)*angerJ ν z + sin (π*ν)*weberE ν z := by
    unfold weberE angerJ
    have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => cos ((-ν)*θ-z*Real.sin θ)) (a := 0) (b := π) π
    simp only [sub_self, sub_zero] at this
    have key : (∫ θ : ℝ in 0..π, cos ((-ν)*θ-z*Real.sin θ)) =
        cos (π*ν)*(∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ))
            + sin (π*ν)*∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ) := by
      rw [← this, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add
            (intervalIntegrable_zero_pi _ (by fun_prop))
                (intervalIntegrable_zero_pi _ (by fun_prop))]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [Real.sin_pi_sub]
      rw [show (-ν)*((π-θ:ℝ):ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-π*ν by push_cast; ring, cos_sub]
      ring
    rw [key]; ring
  rw [h]; ring

end DLMF.Struve
