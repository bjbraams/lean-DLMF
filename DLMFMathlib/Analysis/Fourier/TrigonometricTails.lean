/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Fourier.OscillatoryInversePowers
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Conditional trigonometric tails

The improper integral of `cos(κt)/t` converges for nonzero frequency, but `cos(t)/t`
is not absolutely integrable. Consequently the derivative of `sin(t)/t` is not
absolutely integrable, although all its improper Fourier integrals converge uniformly
for frequencies at least two.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

namespace Real

/-- The cosine integral tail is the real part of the continued oscillatory Mellin tail. -/
theorem tendsto_integral_cos_mul_div {κ : ℝ} (hκ : κ ≠ 0) :
    Tendsto (fun T : ℝ => ∫ t in (1 : ℝ)..T, cos (κ * t) / t) atTop
      (𝓝 (Complex.oscillatoryMellinTail κ 0).re) := by
  have h := Complex.tendsto_integral_oscillatoryMellinTail (w := 0) hκ (by norm_num)
  simp only [zero_sub, Complex.cpow_neg_one] at h
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  refine hre.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hi : IntervalIntegrable (fun t : ℝ => (t : ℂ)⁻¹ * Complex.exp (I * κ * t)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact ((continuous_ofReal.continuousOn.inv₀ fun t ht =>
      ofReal_ne_zero.mpr (by linarith [ht.1])).mul (by fun_prop))
  simp only [Function.comp_def]
  have hri : (∫ t in (1 : ℝ)..T, (t : ℂ)⁻¹ * Complex.exp (I * κ * t)).re =
      ∫ t in (1 : ℝ)..T, ((t : ℂ)⁻¹ * Complex.exp (I * κ * t)).re := by
    simpa using! (intervalIntegral.intervalIntegral_re hi).symm
  rw [hri]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  simp [Complex.exp_re, Complex.normSq_ofReal, div_eq_mul_inv, mul_comm, mul_assoc]

/-- The oscillatory inverse-power amplitude `cos(t)/t` is not absolutely integrable. -/
theorem not_integrableOn_cos_div : ¬ IntegrableOn (fun t : ℝ => cos t / t) (Ioi 1) := by
  intro hi
  have hi₂ : IntegrableOn (fun t : ℝ => cos t ^ 2 / t) (Ioi 1) := by
    refine hi.norm.mono'
      ((by fun_prop : Measurable fun t : ℝ => cos t ^ 2 / t).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_eq_abs, norm_eq_abs, abs_div, abs_div, abs_of_pos (zero_lt_one.trans ht),
      abs_of_nonneg (sq_nonneg _)]
    apply div_le_div_of_nonneg_right _ (zero_lt_one.trans ht).le
    nlinarith [abs_cos_le_one t, abs_nonneg (cos t), sq_abs (cos t)]
  have h₂ := (intervalIntegral_tendsto_integral_Ioi 1 hi₂ tendsto_id).const_mul (2 : ℝ)
  have hcos := tendsto_integral_cos_mul_div (κ := 2) (by norm_num)
  have hlim := h₂.sub hcos
  have hlog : Tendsto Real.log atTop
      (𝓝 (2 * (∫ t in Ioi (1 : ℝ), cos t ^ 2 / t) -
        (Complex.oscillatoryMellinTail 2 0).re)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hi₁ : IntervalIntegrable (fun t : ℝ => cos t ^ 2 / t) volume 1 T := by
      apply ContinuousOn.intervalIntegrable_of_Icc hT
      exact (Real.continuous_cos.pow 2).continuousOn.div continuous_id.continuousOn
        fun t ht => by linarith [ht.1]
    have hiCos : IntervalIntegrable (fun t : ℝ => cos (2 * t) / t) volume 1 T := by
      apply ContinuousOn.intervalIntegrable_of_Icc hT
      exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn.div
        continuous_id.continuousOn
        fun t ht => by linarith [ht.1]
    calc 2 * (∫ t in (1 : ℝ)..T, cos t ^ 2 / t) - ∫ t in (1 : ℝ)..T, cos (2 * t) / t =
        ∫ t in (1 : ℝ)..T, 2 * (cos t ^ 2 / t) - cos (2 * t) / t := by
          rw [intervalIntegral.integral_sub (hi₁.const_mul 2) hiCos,
            intervalIntegral.integral_const_mul]
      _ = ∫ t in (1 : ℝ)..T, 1 / t := by
        apply intervalIntegral.integral_congr
        intro t _
        change 2 * (cos t ^ 2 / t) - cos (2 * t) / t = 1 / t
        rw [Real.cos_two_mul]
        ring
      _ = Real.log T := by rw [integral_one_div_of_pos zero_lt_one
        (zero_lt_one.trans_le hT), div_one]
  exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_log_atTop _ hlog

/-- The derivative of `sin(t)/t` fails absolute integrability on the high tail. -/
theorem not_integrableOn_deriv_sin_div :
    ¬ IntegrableOn (deriv fun t : ℝ => sin t / t) (Ioi 1) := by
  intro hi
  have hiSin : IntegrableOn (fun t : ℝ => sin t / t ^ 2) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).mono'
      ((by fun_prop : Measurable fun t : ℝ => sin t / t ^ 2).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t),
      Real.rpow_neg (zero_lt_one.trans ht).le, Real.rpow_two]
    simpa only [one_div] using div_le_div_of_nonneg_right (abs_sin_le_one t) (sq_nonneg t)
  apply not_integrableOn_cos_div
  refine (hi.add hiSin).congr_fun (fun t ht => ?_) measurableSet_Ioi
  change deriv (fun t : ℝ => sin t / t) t + sin t / t ^ 2 = cos t / t
  have ht0 : t ≠ 0 := by linarith [show 1 < t from ht]
  have hd : HasDerivAt (fun t : ℝ => sin t / t) ((cos t * t - sin t) / t ^ 2) t := by
    simpa only [Pi.div_apply, id_eq, mul_one] using!
      (Real.hasDerivAt_sin t).div (hasDerivAt_id t) ht0
  rw [hd.deriv]
  field_simp
  ring

end Real

namespace Complex.FourierInversePowers

/-- The first derivative of the complex-valued `sin(t)/t` is not absolutely integrable,
although every derivative has a uniform improper Fourier limit on frequencies at least two. -/
theorem not_integrableOn_iteratedDerivWithin_one_sin_div :
    ¬ IntegrableOn (iteratedDerivWithin 1 (fun t : ℝ => Complex.sin t / t) (Ici 1))
      (Ioi 1) := by
  intro hi
  apply Real.not_integrableOn_deriv_sin_div
  refine IntegrableOn.congr_fun (Integrable.re hi) (fun t ht => ?_) measurableSet_Ioi
  have ht0 : t ≠ 0 := by linarith [show 1 < t from ht]
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
  have hd : HasDerivAt (fun x : ℝ => Complex.sin x / x)
      ((Complex.cos t * t - Complex.sin t) / (t : ℂ) ^ 2) t := by
    simpa only [Pi.div_apply, id_eq, mul_one] using!
      ((Complex.hasDerivAt_sin (t : ℂ)).div (hasDerivAt_id (t : ℂ)) htc).comp_ofReal
  have hdr : HasDerivAt (fun x : ℝ => Real.sin x / x)
      ((Real.cos t * t - Real.sin t) / t ^ 2) t := by
    simpa only [Pi.div_apply, id_eq, mul_one] using!
      (Real.hasDerivAt_sin t).div (hasDerivAt_id t) ht0
  have hw := hd.hasDerivWithinAt (s := Ici 1) |>.derivWithin
    (uniqueDiffOn_Ici (1 : ℝ) t (le_of_lt (show 1 < t from ht)))
  rw [show (1 : ℕ) = 0 + 1 by rfl, iteratedDerivWithin_succ,
    iteratedDerivWithin_zero, hw, hdr.deriv]
  simp only [id_eq, mul_one, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    ← Complex.ofReal_div, Complex.ofReal_re]
  rfl

end Complex.FourierInversePowers
