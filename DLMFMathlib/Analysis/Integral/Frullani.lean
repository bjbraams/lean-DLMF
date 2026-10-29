/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complex exponential Frullani integrals

For parameters in the open right half-plane, integrate the exponential along the segment
between the parameters and apply Fubini. This proves absolute convergence as well as the
principal-logarithm evaluation, retaining complex parameters.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set

namespace Complex

/-- A segment between right-half-plane points remains a positive distance from
the imaginary axis. -/
lemma re_segment_ge_min (a b : ℂ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    min a.re b.re ≤ (b + u * (a - b)).re := by
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sub_re]
  nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr (min_le_left a.re b.re)),
    mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr (min_le_right a.re b.re))]

/-- Integrating an exponential over the parameter segment removes the apparent
singularity of the exponential difference divided by the integration variable. -/
lemma integral_segment_exp_neg_mul (a b : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (∫ u in (0 : ℝ)..1, (a - b) * cexp (-(b + u * (a - b)) * t)) =
      (cexp (-b * t) - cexp (-a * t)) / t := by
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => cexp (-(b + v * (a - b)) * t))
      (-(t : ℂ) * ((a - b) * cexp (-(b + u * (a - b)) * t))) u := by
    have hl : HasDerivAt (fun v : ℝ => b + v * (a - b)) (a - b) u := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (a - b)).const_add b
    convert (hl.neg.mul_const (t : ℂ)).cexp using 1
    simp only [Pi.neg_apply]
    ring
  have hi : IntervalIntegrable (fun u : ℝ =>
      (a - b) * cexp (-(b + u * (a - b)) * t)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hi.const_mul (-(t : ℂ)))
  rw [intervalIntegral.integral_const_mul] at h
  simp only [ofReal_one, ofReal_zero, zero_mul, one_mul, add_zero, add_sub_cancel] at h
  apply (eq_div_iff (ofReal_ne_zero.mpr ht)).mpr
  linear_combination -h

/-- The two-variable exponential kernel is integrable over a finite parameter
segment and the positive half-line. -/
lemma integrable_segment_exp_neg_mul {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Integrable (fun p : ℝ × ℝ => (a - b) * cexp (-(b + p.1 * (a - b)) * p.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  have hm : 0 < min a.re b.re := lt_min ha hb
  have hbase := (integrable_const ‖a - b‖ (μ := μ)).mul_prod
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) 0)
  refine hbase.mono' (by fun_prop : Continuous (fun p : ℝ × ℝ =>
    (a - b) * cexp (-(b + p.1 * (a - b)) * p.2))).aestronglyMeasurable ?_
  change ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Ioi (0 : ℝ)))), _
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
  rw [norm_mul, norm_exp]
  have hmin := re_segment_ge_min a b ⟨hp.1.1.le, hp.1.2⟩
  have ht : 0 < p.2 := hp.2
  simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The integral of the reciprocal along a segment in the right half-plane is
the difference of the principal logarithms of the endpoints. -/
lemma integral_segment_inv {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ u in (0 : ℝ)..1, (a - b) / (b + u * (a - b))) = log a - log b := by
  have hp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : 0 < (b + u * (a - b)).re :=
    (lt_min ha hb).trans_le (re_segment_ge_min a b hu)
  have hd (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v : ℝ => log (b + v * (a - b)))
        ((a - b) / (b + u * (a - b))) u := by
    have hl : HasDerivAt (fun v : ℝ => b + v * (a - b)) (a - b) u := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (a - b)).const_add b
    exact hl.clog_real (mem_slitPlane_iff.mpr (Or.inl (hp u (by simpa using hu))))
  have hi : IntervalIntegrable (fun u : ℝ => (a - b) / (b + u * (a - b))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact (continuousAt_const.div (by fun_prop)
      (fun hz => by simpa [hz] using hp u (by simpa using hu))).continuousWithinAt
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

/-- An exponential difference divided by the variable is absolutely integrable
when both exponential parameters lie in the right half-plane. -/
theorem integrableOn_exp_sub_exp_div {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (cexp (-b * t) - cexp (-a * t)) / t) (Ioi 0) := by
  have h := (integrable_segment_exp_neg_mul ha hb).integral_prod_right
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_segment_exp_neg_mul a b ht.ne'

/-- Complex exponential Frullani's formula in the right half-plane, expressed as
a difference of principal logarithms. -/
theorem integral_exp_sub_exp_div_eq_log_sub {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t in Ioi (0 : ℝ), (cexp (-b * t) - cexp (-a * t)) / t) = log a - log b := by
  have heq : (∫ t in Ioi (0 : ℝ), (cexp (-b * t) - cexp (-a * t)) / t) =
      ∫ t in Ioi (0 : ℝ), ∫ u in Ioc (0 : ℝ) 1,
        (a - b) * cexp (-(b + u * (a - b)) * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (integral_segment_exp_neg_mul a b ht.ne').symm
  rw [heq, ← integral_integral_swap (integrable_segment_exp_neg_mul ha hb)]
  have hinner : (∫ u in Ioc (0 : ℝ) 1, ∫ t in Ioi (0 : ℝ),
      (a - b) * cexp (-(b + u * (a - b)) * t)) =
      ∫ u in Ioc (0 : ℝ) 1, (a - b) / (b + u * (a - b)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    have hp : 0 < (b + u * (a - b)).re :=
      (lt_min ha hb).trans_le (re_segment_ge_min a b ⟨hu.1.le, hu.2⟩)
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hp) 0]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg]
    ring
  rw [hinner, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_segment_inv ha hb

/-- Division of two right-half-plane points subtracts their principal logarithms;
the difference of their arguments stays strictly between `-π` and `π`. -/
theorem log_div_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    log (a / b) = log a - log b := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hargA := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hargB := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
  have he : cexp (log a - log b) = a / b := by rw [exp_sub, exp_log ha0, exp_log hb0]
  rw [← he, log_exp]
  · simp only [sub_im, log_im]
    linarith [hargA.1, hargB.2]
  · simp only [sub_im, log_im]
    linarith [hargA.2, hargB.1]

/-- Complex exponential Frullani's formula with the principal logarithm of the
ratio, valid for arbitrary right-half-plane parameters. -/
theorem integral_exp_sub_exp_div {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t in Ioi (0 : ℝ), (cexp (-b * t) - cexp (-a * t)) / t) = log (a / b) := by
  rw [integral_exp_sub_exp_div_eq_log_sub ha hb, log_div_of_re_pos ha hb]

/-- The principal logarithm factors `1-z²` into `1-z` and `1+z` whenever both
linear factors avoid the branch cut. Their imaginary parts have opposite signs. -/
theorem log_one_sub_sq {z : ℂ} (hm : 1 - z ∈ slitPlane) (hp : 1 + z ∈ slitPlane) :
    log (1 - z ^ 2) = log (1 - z) + log (1 + z) := by
  rw [show (1 : ℂ) - z ^ 2 = (1 - z) * (1 + z) by ring]
  apply Complex.log_mul (slitPlane_ne_zero hm) (slitPlane_ne_zero hp)
  rcases lt_trichotomy z.im 0 with hi | hi | hi
  · have hneg : arg (1 + z) < 0 := arg_neg_iff.mpr (by simpa using hi)
    have hpos : 0 ≤ arg (1 - z) := arg_nonneg_iff.mpr (by simp; linarith)
    exact ⟨by linarith [neg_pi_lt_arg (1 + z)], by linarith [arg_le_pi (1 - z)]⟩
  · have hmre : 0 < (1 - z).re := by
      rcases mem_slitPlane_iff.mp hm with h | h
      · exact h
      · simp [hi] at h
    have hpre : 0 < (1 + z).re := by
      rcases mem_slitPlane_iff.mp hp with h | h
      · exact h
      · simp [hi] at h
    rw [arg_eq_zero_iff.mpr ⟨hmre.le, by simp [hi]⟩,
      arg_eq_zero_iff.mpr ⟨hpre.le, by simp [hi]⟩]
    simp [Real.pi_pos, Real.pi_nonneg]
  · have hneg : arg (1 - z) < 0 := arg_neg_iff.mpr (by simp; linarith)
    have hpos : 0 ≤ arg (1 + z) := arg_nonneg_iff.mpr (by simpa using hi.le)
    exact ⟨by linarith [neg_pi_lt_arg (1 - z)], by linarith [arg_le_pi (1 + z)]⟩

end Complex
