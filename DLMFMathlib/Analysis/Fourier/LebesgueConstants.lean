/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMFMathlib.Analysis.Asymptotics.PeriodicLogAverage
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
/-!
# The asymptotic growth of Lebesgue constants

The normalized absolute sine quotient has leading term `4 / π² * log n`. Periodic logarithmic
averaging evaluates the absolute-sine integral, and the analytic divided difference of the
reciprocal sinc function bounds the correction uniformly over all real frequencies.
Mathlib supplies analytic divided differences and logarithmic limits.

## Main results

* `Real.intervalIntegrable_abs_sin_div`: integrability at the removable singularity.
* `Real.isBigO_integral_abs_sin_div_sub_log`: logarithmic growth with bounded error.
* `Real.exists_bound_integral_abs_sin_div_sin_half_sub`: the uniform sine-quotient correction.
* `Real.isEquivalent_integral_abs_sin_div_sin_half`: the Lebesgue-constant asymptotic.
-/

public noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace Real
/-- The absolute-sine quotient is integrable over every finite real interval. -/
lemma intervalIntegrable_abs_sin_div (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => |sin t| / t) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ((by fun_prop : Measurable (fun t : ℝ => |sin t| / t)).aestronglyMeasurable) ?_
  filter_upwards with t
  simp only [norm_div, Real.norm_eq_abs, abs_abs]
  by_cases ht : t = 0
  · simp [ht]
  · exact (div_le_one (abs_pos.mpr ht)).mpr abs_sin_le_abs
/-- The integral of the absolute-sine quotient has logarithmic growth with bounded error. -/
lemma isBigO_integral_abs_sin_div_sub_log :
    (fun R : ℝ => (∫ t in (0 : ℝ)..R, |sin t| / t) - (2 / π) * log R) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  have hp : Function.Periodic (fun t : ℝ => |sin t|) π := by
    intro t
    dsimp only
    rw [sin_add_pi, abs_neg]
  have hc : Continuous (fun t : ℝ => |sin t|) := continuous_sin.abs
  have hmean : (∫ t in (0 : ℝ)..π, |sin t|) = 2 := by
    rw [intervalIntegral.integral_congr fun t ht => abs_of_nonneg
      (sin_nonneg_of_mem_Icc (by simpa only [uIcc_of_le pi_pos.le] using ht)), integral_sin]
    norm_num
  have h := hp.isBigO_integral_div_sub_mean_mul_log pi_pos (hc.intervalIntegrable 0 π)
  rw [hmean] at h
  have hconst : (fun _ : ℝ => ∫ t in (0 : ℝ)..1, |sin t| / t) =O[atTop]
      (fun _ => (1 : ℝ)) := isBigO_const_const _ one_ne_zero _
  have hs := hconst.add h
  have heq (R : ℝ) : (∫ t in (0 : ℝ)..1, |sin t| / t) +
      ((∫ t in (1 : ℝ)..R, |sin t| / t) - 2 / π * log R) =
      (∫ t in (0 : ℝ)..R, |sin t| / t) - 2 / π * log R := by
    rw [← add_sub_assoc, intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_abs_sin_div 0 1) (intervalIntegrable_abs_sin_div 1 R)]
  simpa only [heq] using hs
/-- The half-angle sine denominator differs from its linear approximation by a bounded
normalized integral, uniformly over all real frequencies. -/
lemma exists_bound_integral_abs_sin_div_sin_half_sub : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ,
    |(1 / π) * (∫ t in (0 : ℝ)..π, |sin (η * t)| / sin (t / 2)) -
      (2 / π) * (∫ t in (0 : ℝ)..π, |sin (η * t)| / t)| ≤ C := by
  let H : ℝ → ℝ := fun t => (sinc (t / 2))⁻¹
  have ha : AnalyticOnNhd ℝ H (Icc 0 π) := by
    intro t ht
    dsimp only [H]
    apply AnalyticAt.inv
    · have hdiv : AnalyticAt ℝ (fun u : ℝ => u / 2) t := analyticAt_id.div_const
      exact (analyticAt_sinc (t / 2)).comp_of_eq hdiv rfl
    · exact (sinc_pos (by rw [abs_of_nonneg (by linarith [ht.1])];
                          linarith [ht.2, pi_pos])).ne'
  have hd : ContinuousOn (dslope H 0) (Icc 0 π) := (ha.dslope 0).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  have hC0 : 0 ≤ C := (norm_nonneg (dslope H 0 0)).trans (hC 0 ⟨le_rfl, pi_pos.le⟩)
  refine ⟨2 * C, by positivity, fun η => ?_⟩
  let E : ℝ → ℝ := fun t => 2 * |sin (η * t)| * dslope H 0 t
  have hE : IntervalIntegrable E volume 0 π := by
    have hecont : ContinuousOn E (Icc 0 π) :=
      ((continuous_const.mul (continuous_sin.comp
        (continuous_const.mul continuous_id)).abs).continuousOn).mul hd
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le pi_pos.le] using hecont
  have hid (t : ℝ) (ht : t ∈ Ioc 0 π) :
      |sin (η * t)| / sin (t / 2) =
        2 * (|sin (η * t)| / t) + E t := by
    have ht0 : t ≠ 0 := ht.1.ne'
    have hs0 : sin (t / 2) ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, pi_pos])).ne'
    dsimp only [E]
    rw [dslope_of_ne H ht0, slope_def_field]
    simp only [H, zero_div, sinc_zero, inv_one, sub_zero, sinc_of_ne_zero
      (div_ne_zero ht0 two_ne_zero)]
    field_simp [ht0, hs0]
    ring_nf
  have href : IntervalIntegrable (fun t : ℝ => |sin (η * t)| / t) volume 0 π := by
    refine (intervalIntegrable_const (c := |η|)).mono_fun'
      ((by fun_prop : Measurable (fun t : ℝ => |sin (η * t)| / t)).aestronglyMeasurable) ?_
    filter_upwards with t
    simp only [norm_div, Real.norm_eq_abs, abs_abs]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_le_iff₀ (abs_pos.mpr ht)]
      simpa only [abs_mul] using (abs_sin_le_abs (x := η * t))
  have heq : (∫ t in (0 : ℝ)..π, |sin (η * t)| / sin (t / 2)) =
      2 * (∫ t in (0 : ℝ)..π, |sin (η * t)| / t) + ∫ t in (0 : ℝ)..π, E t := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (href.const_mul 2) hE]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    exact hid t (by simpa only [uIoc_of_le pi_pos.le] using ht)
  have hb : |∫ t in (0 : ℝ)..π, E t| ≤ (2 * C) * π := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..π, |E t| := intervalIntegral.abs_integral_le_integral_abs pi_pos.le
      _ ≤ ∫ _t in (0 : ℝ)..π, 2 * C := by
        apply intervalIntegral.integral_mono_on pi_pos.le hE.abs intervalIntegrable_const
        intro t ht
        dsimp only [E]
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_abs]
        have hs := abs_sin_le_one (η * t)
        have hh : |dslope H 0 t| ≤ C := hC t ht
        nlinarith [abs_nonneg (sin (η * t)), abs_nonneg (dslope H 0 t)]
      _ = _ := by
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        ring
  rw [heq]
  have hi : 1 / π * (2 * (∫ t in (0 : ℝ)..π, |sin (η * t)| / t) +
      ∫ t in (0 : ℝ)..π, E t) - 2 / π * (∫ t in (0 : ℝ)..π,
      |sin (η * t)| / t) = (∫ t in (0 : ℝ)..π, E t) / π := by ring
  rw [hi, abs_div, abs_of_pos pi_pos]
  exact (div_le_iff₀ pi_pos).mpr (by nlinarith [hb])
/-- The normalized absolute sine quotient is asymptotic to `4 / π² * log n`. -/
lemma isEquivalent_integral_abs_sin_div_sin_half :
    (fun N : ℕ => (1 / π) * ∫ t in (0 : ℝ)..π,
      |sin ((N + 1 / 2) * t)| / sin (t / 2)) ~[atTop]
      (fun N : ℕ => 4 / π ^ 2 * log N) := by
  let L : ℕ → ℝ := fun N => (1 / π) * ∫ t in (0 : ℝ)..π,
    |sin ((N + 1 / 2) * t)| / sin (t / 2)
  let R : ℕ → ℝ := fun N => ((N : ℝ) + 1 / 2) * π
  let A : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, |sin t| / t
  have hR : Tendsto R atTop atTop := by
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const pi_pos
  have hscale (N : ℕ) : (∫ t in (0 : ℝ)..π, |sin ((N + 1 / 2) * t)| / t) = A (R N) := by
    have hη : (N : ℝ) + 1 / 2 ≠ 0 := by positivity
    have heq : (fun t : ℝ => |sin (((N : ℝ) + 1 / 2) * t)| / t) =
        (fun t : ℝ => ((N : ℝ) + 1 / 2) *
          (|sin (((N : ℝ) + 1 / 2) * t)| / (((N : ℝ) + 1 / 2) * t))) := by
      funext t
      field_simp
    rw [heq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun t : ℝ => |sin t| / t) hη]
    dsimp only [A, R]
    simp only [mul_zero, smul_eq_mul]
    field_simp
  have h1 : (fun N => L N - 2 / π * A (R N)) =O[atTop] (fun _ => (1 : ℝ)) := by
    obtain ⟨C, _, hC⟩ := exists_bound_integral_abs_sin_div_sin_half_sub
    apply IsBigO.of_bound C
    filter_upwards with N
    simpa only [Real.norm_eq_abs, abs_one, mul_one, L, ← hscale] using hC ((N : ℝ) + 1 / 2)
  have h2 : (fun N => A (R N) - 2 / π * log (R N)) =O[atTop] (fun _ => (1 : ℝ)) :=
    isBigO_integral_abs_sin_div_sub_log.comp_tendsto hR
  have h3 : Tendsto (fun N : ℕ => log (R N) - log N) atTop (𝓝 (log π)) := by
    have h := ((tendsto_log_comp_add_sub_log (1 / 2)).comp
      tendsto_natCast_atTop_atTop).add_const (log π)
    simp only [zero_add] at h
    convert h using 1
    funext N
    dsimp only [R, Function.comp_apply]
    rw [log_mul (by positivity : (N : ℝ) + 1 / 2 ≠ 0) pi_ne_zero]
    ring_nf
  have hsum := (h1.add (h2.const_mul_left (2 / π))).add
    ((h3.isBigO_one ℝ).const_mul_left (4 / π ^ 2))
  have hfinal : (fun N => L N - 4 / π ^ 2 * log N) =O[atTop] (fun _ => (1 : ℝ)) := by
    convert hsum using 1
    funext N
    field_simp
    ring
  have hlog : Tendsto (fun N : ℕ => log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlo : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun N : ℕ => log N) := by
    apply (isLittleO_one_left_iff ℝ).mpr
    simpa only [Real.norm_eq_abs, Function.comp_def] using tendsto_abs_atTop_atTop.comp hlog
  have hsmall := hfinal.trans_isLittleO hlo
  have hsmall' := hsmall.const_mul_right (by positivity : (4 / π ^ 2 : ℝ) ≠ 0)
  exact hsmall'.isEquivalent

end Real
