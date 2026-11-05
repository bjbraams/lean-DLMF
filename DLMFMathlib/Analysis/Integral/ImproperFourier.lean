/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.Improper

/-!
# Conditional Fourier integrals of powers

For `0 < Re s < 1`, the oscillatory integral of `t^(s-1) exp(-at)` converges when
`Re a = 0` and `a ≠ 0`. Integration by parts on the tail gives convergence without
an assumption of absolute integrability.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Complex

/-- Existence of the conditionally convergent Gamma Fourier integral. -/
theorem exists_tendsto_integral_cpow_mul_exp_of_re_eq_zero {s a : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (ha : a.re = 0) (ha0 : a ≠ 0) :
    ∃ L, Tendsto (fun X : ℝ => ∫ t in (0 : ℝ)..X,
      (t : ℂ) ^ (s - 1) * exp (-(a * t))) atTop (𝓝 L) := by
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-(a * t))
  let V : ℝ → ℂ := fun t => exp (-(a * t)) / (-a)
  let g : ℝ → ℂ := fun t => (s - 1) * (t : ℂ) ^ (s - 1 - 1) * V t
  have hVnorm (t : ℝ) : ‖V t‖ = 1 / ‖a‖ := by simp [V, norm_exp, ha]
  have hfi (b c : ℝ) : IntervalIntegrable f volume b c := by
    exact (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith : -1 < (s - 1).re))
      |>.mul_continuousOn (show ContinuousOn (fun t : ℝ => exp (-(a * t))) (uIcc b c) by
        fun_prop)
  have hderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (s - 1))
        ((s - 1) * (x : ℂ) ^ (s - 1 - 1)) x := by
    have h := ((hasDerivAt_id (x : ℂ)).cpow_const (c := s - 1)
      (by simpa using ofReal_mem_slitPlane.mpr hx)).comp_ofReal
    simpa using h
  have hVderiv (x : ℝ) : HasDerivAt V (exp (-(a * x))) x := by
    have h := (((hasDerivAt_id (x : ℂ)).const_mul (-a)).cexp.div_const (-a)).comp_ofReal
    convert h using 1 <;> simp only [V, neg_mul, id_eq, mul_one]
    field_simp
  have hgint : IntegrableOn g (Ioi 1) := by
    have hb : IntegrableOn (fun t : ℝ => (‖s - 1‖ / ‖a‖) * t ^ (s.re - 2)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine hb.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := lt_trans one_pos ht
      refine ContinuousAt.continuousWithinAt ?_
      exact (continuousAt_const.mul ((continuous_ofReal.continuousAt).cpow
        continuousAt_const (ofReal_mem_slitPlane.mpr ht0))).mul (by fun_prop)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      dsimp [g]
      rw [norm_mul, norm_mul, hVnorm, norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, one_re]
      ring_nf
      rfl
  have hibp (X : ℝ) (hX : 1 ≤ X) : ∫ t in (0 : ℝ)..X, f t =
      (∫ t in (0 : ℝ)..1, f t) + ((X : ℂ) ^ (s - 1) * V X -
        (1 : ℂ) ^ (s - 1) * V 1 - ∫ t in (1 : ℝ)..X, g t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 1) (hfi 1 X)]
    congr 1
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := X)
      (u := fun t : ℝ => (t : ℂ) ^ (s - 1))
      (u' := fun t => (s - 1) * (t : ℂ) ^ (s - 1 - 1)) (v := V)
      (v' := fun t => exp (-(a * t)))
      (fun t ht => hderiv t (by
        rw [uIcc_of_le hX] at ht; exact lt_of_lt_of_le one_pos ht.1))
      (fun t _ => hVderiv t) ?_ (by apply Continuous.intervalIntegrable; fun_prop)
    · simpa only [f, g, ofReal_one] using h
    · refine ContinuousOn.intervalIntegrable (fun t ht => ?_)
      rw [uIcc_of_le hX] at ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
      exact (continuousAt_const.mul ((continuous_ofReal.continuousAt).cpow
        continuousAt_const (ofReal_mem_slitPlane.mpr ht0))).continuousWithinAt
  have hbound : Tendsto (fun X : ℝ => (X : ℂ) ^ (s - 1) * V X) atTop (𝓝 0) := by
    have hr : Tendsto (fun X : ℝ => X ^ (s.re - 1) * (1 / ‖a‖)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := 1 - s.re) (by linarith)).mul_const (1 / ‖a‖)
      simpa only [neg_sub, zero_mul] using h
    refine squeeze_zero_norm' ?_ hr
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hX, hVnorm, sub_re, one_re]
  have hI := intervalIntegral_tendsto_integral_Ioi 1 hgint tendsto_id
  refine ⟨(∫ t in (0 : ℝ)..1, f t) +
    (0 - (1 : ℂ) ^ (s - 1) * V 1 - ∫ t in Ioi 1, g t), ?_⟩
  have h := (tendsto_const_nhds (x := ∫ t in (0 : ℝ)..1, f t)).add
    ((hbound.sub (tendsto_const_nhds (x := (1 : ℂ) ^ (s - 1) * V 1))).sub hI)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [hibp X hX]
  rfl

end Complex
