/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.RepeatedIntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform convergence of improper Fourier integrals

One integration by parts gives uniform convergence for frequencies bounded away from
zero when the amplitude vanishes at infinity and its derivative is integrable.
The tail estimate is uniform in all frequencies of absolute value at least one.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

namespace Complex

/-- Absolute Fourier tails are bounded by the absolute tail of the amplitude. -/
theorem norm_fourier_truncation_sub_integral_le {f : ℝ → ℂ} {a T : ℝ}
    (hf : IntegrableOn f (Ioi a)) (hT : a ≤ T) (x : ℝ) :
    ‖(∫ t in a..T, exp (I * x * t) * f t) -
      ∫ t in Ioi a, exp (I * x * t) * f t‖ ≤ ∫ t in Ioi T, ‖f t‖ := by
  have hn (t : ℝ) : ‖exp (I * x * t)‖ = 1 := by rw [norm_exp]; simp
  have hi : IntegrableOn (fun t : ℝ => exp (I * x * t) * f t) (Ioi a) := by
    refine hf.norm.mono'
      ((by fun_prop : Continuous fun t : ℝ => exp (I * x * t)).aestronglyMeasurable.mul
        hf.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, hn, one_mul]
  have hs := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hT))
  have he : (∫ t in a..T, exp (I * x * t) * f t) -
      ∫ t in Ioi a, exp (I * x * t) * f t =
      -(∫ t in Ioi T, exp (I * x * t) * f t) := by linear_combination hs
  rw [he, norm_neg]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change ‖exp (I * x * t) * f t‖ = ‖f t‖
  rw [norm_mul, hn, one_mul]

/-- A vanishing amplitude with an integrable continuous derivative has a uniformly
convergent improper Fourier integral for every real frequency of absolute value at least
one. The displayed limit is its integration-by-parts formula. -/
theorem tendstoUniformlyOn_integral_exp_mul_of_integrable_deriv
    {q q' : ℝ → ℂ} {a : ℝ}
    (hq : ContinuousOn q (Ici a)) (hq' : ContinuousOn q' (Ici a))
    (hd : ∀ t ∈ Ici a, HasDerivWithinAt q (q' t) (Ici a) t)
    (hzero : Tendsto q atTop (𝓝 0)) (hi : IntegrableOn q' (Ioi a)) :
    TendstoUniformlyOn (fun (T x : ℝ) => ∫ t in a..T, exp (I * x * t) * q t)
      (fun x : ℝ => -(exp (I * x * a) * q a +
        ∫ t in Ioi a, exp (I * x * t) * q' t) / (I * x)) atTop {x : ℝ | 1 ≤ |x|} := by
  have hlim : Tendsto (fun T : ℝ => ‖q T‖ + ∫ t in Ioi T, ‖q' t‖) atTop (𝓝 0) := by
    simpa using hzero.norm.add (tendsto_integral_Ioi_zero (f := fun t => ‖q' t‖) tendsto_id)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop a, hlim.eventually_lt_const hε] with T hT hsmall x hx
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  have hxc : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx0)
  have hb := intervalIntegral.integral_cexp_mul_eq_boundary_sub hT hxc
    (hq.mono Icc_subset_Ici_self) (hq'.mono Icc_subset_Ici_self)
    (fun t ht => (hd t ht.1).mono Icc_subset_Ici_self)
  have he : (∫ t in a..T, exp (I * x * t) * q t) -
      (-(exp (I * x * a) * q a + ∫ t in Ioi a, exp (I * x * t) * q' t) / (I * x)) =
      (exp (I * x * T) * q T - ((∫ t in a..T, exp (I * x * t) * q' t) -
        ∫ t in Ioi a, exp (I * x * t) * q' t)) / (I * x) := by
    rw [hb]
    ring
  rw [dist_comm, dist_eq_norm, he, norm_div, norm_mul, norm_I, one_mul,
    norm_real, Real.norm_eq_abs]
  apply lt_of_le_of_lt _ hsmall
  calc ‖exp (I * x * T) * q T - ((∫ t in a..T, exp (I * x * t) * q' t) -
        ∫ t in Ioi a, exp (I * x * t) * q' t)‖ / |x| ≤
      (‖q T‖ + ∫ t in Ioi T, ‖q' t‖) / |x| := by
        apply div_le_div_of_nonneg_right _ (abs_nonneg _)
        apply (norm_sub_le _ _).trans
        apply add_le_add
        · rw [norm_mul, norm_exp]
          simp
        · exact norm_fourier_truncation_sub_integral_le hi hT x
    _ ≤ _ := div_le_self (add_nonneg (norm_nonneg _)
      (integral_nonneg fun t => norm_nonneg _)) hx

end Complex
