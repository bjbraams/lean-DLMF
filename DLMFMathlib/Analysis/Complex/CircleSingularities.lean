/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrable algebraic singularities on a circle

A boundary chord is at most twice the corresponding radial distance. Consequently an
algebraic singularity with exponent greater than minus one admits integrable angular
majorants, uniformly over concentric inner circles.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter Metric
open scoped Real Topology

namespace Complex

/-- A boundary chord is bounded by twice its inward radial counterpart. -/
theorem norm_circle_sub_le_two_mul_norm_radial_sub {r s : ℝ} {u w : ℂ}
    (hs : 0 ≤ s) (hsr : s ≤ r) (hu : ‖u‖ = 1) (hw : ‖w‖ = r) :
    ‖(r : ℂ) * u - w‖ ≤ 2 * ‖(s : ℂ) * u - w‖ := by
  have hr : 0 ≤ r := hs.trans hsr
  have hsu : ‖(s : ℂ) * u‖ = s := by
    rw [norm_mul, hu, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hdist : r - s ≤ ‖(s : ℂ) * u - w‖ := by
    have H := norm_sub_norm_le w ((s : ℂ) * u)
    rwa [hw, hsu, norm_sub_rev] at H
  have hdif : ‖(r : ℂ) * u - (s : ℂ) * u‖ = r - s := by
    rw [← sub_mul, norm_mul, hu, mul_one, ← ofReal_sub, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsr)]
  calc _ = ‖((r : ℂ) * u - (s : ℂ) * u) + ((s : ℂ) * u - w)‖ := by congr 1; ring
    _ ≤ ‖(r : ℂ) * u - (s : ℂ) * u‖ + ‖(s : ℂ) * u - w‖ := norm_add_le _ _
    _ ≤ _ := by rw [hdif]; linarith

/-- On an angular half-period the circular chord has a linear lower bound. -/
theorem norm_exp_mul_I_sub_exp_mul_I_ge {t v : ℝ} (h : |t - v| ≤ π) :
    (2 / π) * |t - v| ≤ ‖exp ((t : ℂ) * I) - exp ((v : ℂ) * I)‖ := by
  have he : exp ((t : ℂ) * I) - exp ((v : ℂ) * I) =
      exp ((v : ℂ) * I) * (exp (I * ((t - v : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have H := Real.mul_abs_le_abs_sin (x := (t - v) / 2) (by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  simp only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
  nlinarith

end Complex

namespace intervalIntegral

/-- Absolute powers of the distance to a real point are integrable on finite intervals. -/
theorem intervalIntegrable_norm_sub_rpow {p : ℝ} (hp : -1 < p) (v a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖t - v‖ ^ p) volume a b := by
  have H := (intervalIntegral.intervalIntegrable_cpow' (a := a - v) (b := b - v)
    (r := (p : ℂ)) (by simpa)).norm.comp_sub_right v
  simpa only [sub_add_cancel, norm_cpow_real, ← ofReal_sub, norm_real] using H

end intervalIntegral

namespace Complex

/-- A negative algebraic power of circular distance is locally integrable when its exponent
exceeds minus one. -/
theorem locallyIntegrable_norm_circle_sub_rpow {r p : ℝ} (hr : 0 < r)
    (hp : -1 < p) (hp0 : p ≤ 0) (w : ℂ) :
    LocallyIntegrable (fun t : ℝ => ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖ ^ p) := by
  intro v
  by_cases hv : (r : ℂ) * exp ((v : ℂ) * I) = w
  · let C : ℝ := (2 * r / π) ^ p
    have hC0 : 0 < 2 * r / π := by positivity
    have hbound (t : ℝ) (ht : t ∈ Icc (v - π) (v + π)) :
        ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖ ^ p ≤ C * ‖t - v‖ ^ p := by
      by_cases htv : t = v
      · subst t
        by_cases hp' : p = 0
        · simp [hp', C]
        · simp [hv, Real.zero_rpow hp']
      have hd : 0 < ‖t - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr htv)
      have hangle : |t - v| ≤ π := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have H := norm_exp_mul_I_sub_exp_mul_I_ge hangle
      have hnorm : ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖ =
          r * ‖exp ((t : ℂ) * I) - exp ((v : ℂ) * I)‖ := by
        rw [← hv, ← mul_sub, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hlow : (2 * r / π) * ‖t - v‖ ≤
          ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖ := by
        rw [hnorm, Real.norm_eq_abs]
        calc _ = r * ((2 / π) * |t - v|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left H hr.le
      have Hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hC0 hd) hlow hp0
      simpa only [Real.mul_rpow hC0.le (norm_nonneg _), C] using Hpow
    have hi : IntegrableOn (fun t : ℝ => C * ‖t - v‖ ^ p) (Icc (v - π) (v + π)) := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le
        (by linarith [Real.pi_pos] : v - π ≤ v + π)).mp
      exact (intervalIntegral.intervalIntegrable_norm_sub_rpow hp v _ _).const_mul C
    refine ⟨Icc (v - π) (v + π), Icc_mem_nhds (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]), hi.mono' ?_ ?_⟩
    · exact (by fun_prop : Measurable (fun t : ℝ =>
        ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖ ^ p)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hbound t ht
  · let U : Set ℝ := {t | (r : ℂ) * exp ((t : ℂ) * I) ≠ w}
    have hU : IsOpen U := isOpen_ne.preimage (by fun_prop)
    have hcont : ContinuousOn
        (fun t : ℝ => ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖ ^ p) U := by
      intro t ht
      have H : ContinuousAt (fun t : ℝ => ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖) t := by
        fun_prop
      exact (H.rpow_const (Or.inl (norm_ne_zero_iff.mpr
        (sub_ne_zero.mpr ht)))).continuousWithinAt
    have H := hcont.integrableAt_nhdsWithin (μ := volume) hU.measurableSet hv
    rwa [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hv)] at H

/-- Every finite circular arc has integrable algebraic distance singularities of order
strictly below one. -/
theorem intervalIntegrable_norm_circle_sub_rpow {r p : ℝ} (hr : 0 < r)
    (hp : -1 < p) (hp0 : p ≤ 0) (w : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖(r : ℂ) * exp ((t : ℂ) * I) - w‖ ^ p) volume a b := by
  rw [intervalIntegrable_iff']
  exact (locallyIntegrable_norm_circle_sub_rpow hr hp hp0 w).integrableOn_isCompact
    isCompact_uIcc

end Complex
