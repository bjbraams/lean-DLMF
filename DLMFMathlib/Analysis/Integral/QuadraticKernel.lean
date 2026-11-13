/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Quadratic resolvents and logarithmic kernels

Quadratic denominators with parameters in the right half-plane have no real zeros.
Polynomial decay gives absolute integrability of their weighted reciprocals.
Integrating along a radial parameter segment yields `log (1+a²/t²)` and supplies
an absolutely integrable representation for exchanging Fourier integrals.

## Main results

* `Complex.sq_add_sq_ne_zero`: nonvanishing of the quadratic denominator.
* `Complex.integrableOn_pow_div_sq_add_sq_pow`: polynomially weighted resolvent integrability.
* `Complex.integral_quadratic_log_kernel`: its parameter integral is a principal logarithm.
* `Complex.integrable_quadratic_log_kernel`: absolute integrability on the product.
* `Complex.integrableOn_log_one_add_sq_div_sq_mul_cos`: integrability of the cosine pairing.
-/

public noncomputable section

open Complex MeasureTheory Filter Set
open scoped Real Topology Nat

namespace Complex

/-- `a² + ξ² ≠ 0` for real `ξ` when `ℜa > 0`. -/
lemma sq_add_sq_ne_zero {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) : a ^ 2 + (ξ : ℂ) ^ 2 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im] at hre him
  have hq : a.im = 0 := by nlinarith
  rw [hq] at hre
  nlinarith

/-- A lower bound `‖a² + ξ²‖ ≥ ξ²/2` for `ξ ≥ 2‖a‖`. -/
lemma norm_sq_add_sq_ge {a : ℂ} {ξ : ℝ} (hξ : 2 * ‖a‖ ≤ ξ) :
    ξ ^ 2 / 2 ≤ ‖a ^ 2 + (ξ : ℂ) ^ 2‖ := by
  have h1 : ‖(ξ : ℂ) ^ 2‖ - ‖a ^ 2‖ ≤ ‖a ^ 2 + (ξ : ℂ) ^ 2‖ := by
    have := norm_sub_norm_le ((ξ : ℂ) ^ 2) (-(a ^ 2))
    simpa [sub_neg_eq_add, add_comm] using this
  rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h1
  have : 0 ≤ ‖a‖ := norm_nonneg a
  nlinarith

/-- Integrability on `(0, ∞)` of `ξ ↦ ξ^k/(a² + ξ²)^m` when `k + 1 < 2m`. -/
lemma integrableOn_pow_div_sq_add_sq_pow {a : ℂ} (ha : 0 < a.re) (k m : ℕ)
    (hkm : k + 2 ≤ 2 * m) :
    IntegrableOn (fun ξ : ℝ => (ξ : ℂ) ^ k / (a ^ 2 + (ξ : ℂ) ^ 2) ^ m) (Ioi 0) := by
  have hcont : Continuous fun ξ : ℝ => (ξ : ℂ) ^ k / (a ^ 2 + (ξ : ℂ) ^ 2) ^ m :=
    Continuous.div (by fun_prop) (by fun_prop) fun ξ => pow_ne_zero _ (sq_add_sq_ne_zero ha ξ)
  refine IntegrableOn.mono_set (t := Ici 0) ?_ Ioi_subset_Ici_self
  refine LocallyIntegrableOn.integrableOn_of_isBigO_atTop
    ((hcont.locallyIntegrable (μ := volume)).locallyIntegrableOn (Ici 0))
    (g := fun ξ : ℝ => ξ ^ (-2 : ℝ)) ?_
    (integrableAtFilter_rpow_atTop_iff.2 (by norm_num))
  refine Asymptotics.IsBigO.of_bound (2 ^ m) ?_
  filter_upwards [eventually_ge_atTop (max (2 * ‖a‖) 1)] with ξ hξ
  have hξ1 : 1 ≤ ξ := le_of_max_le_right hξ
  have hξ0 : 0 < ξ := by linarith
  have hb := norm_sq_add_sq_ge (le_of_max_le_left hξ)
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ0,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hξ0 _), Real.rpow_neg hξ0.le,
    Real.rpow_two, div_le_iff₀ (pow_pos (lt_of_lt_of_le (by positivity) hb) _)]
  calc ξ ^ k ≤ ξ ^ (2 * m - 2) := pow_le_pow_right₀ hξ1 (by omega)
    _ = 2 ^ m * (ξ ^ 2)⁻¹ * (ξ ^ 2 / 2) ^ m := by
        rw [div_pow, ← pow_mul]
        obtain ⟨j, hj⟩ : ∃ j, 2 * m = j + 2 := ⟨2 * m - 2, by omega⟩
        rw [hj, Nat.add_sub_cancel, pow_add]
        field_simp
    _ ≤ 2 ^ m * (ξ ^ 2)⁻¹ * ‖a ^ 2 + (ξ : ℂ) ^ 2‖ ^ m := by
        gcongr

/-- A quadratic denominator with a parameter in the right half-plane avoids the logarithmic cut. -/
lemma sq_add_mul_sq_mem_slitPlane {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    (a * r) ^ 2 + (t : ℂ) ^ 2 ∈ slitPlane := by
  by_cases har : a.im = 0 ∨ r = 0
  · left
    rcases har with har | hr
    · simp only [add_re, sq, mul_re, mul_im, ofReal_re, ofReal_im, mul_zero, sub_zero,
        zero_add, har, zero_mul]
      nlinarith [sq_nonneg (a.re * r)]
    · simp only [hr, ofReal_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
      simp only [sq, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      positivity
  · right
    push Not at har
    simp only [sq, add_im, mul_im, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
      zero_add, zero_mul, add_zero]
    have he : a.re * r * (a.im * r) + a.im * r * (a.re * r) =
        2 * a.re * a.im * r ^ 2 := by ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha.ne') har.1)
      (pow_ne_zero 2 har.2)

/-- Integrating the quadratic resolvent along a radial segment gives a principal logarithm. -/
lemma integral_quadratic_log_kernel {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    (∫ r : ℝ in 0..1, 2 * a ^ 2 * r / ((a * r) ^ 2 + t ^ 2)) =
      Complex.log (1 + a ^ 2 / t ^ 2) := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => Complex.log ((a * r) ^ 2 + t ^ 2))
      (2 * a ^ 2 * r / ((a * r) ^ 2 + t ^ 2)) r := by
    have hp := ((((hasDerivAt_id r).ofReal_comp.const_mul a).pow 2).add_const ((t : ℂ) ^ 2))
    simp only [id_eq, Pi.pow_apply, ofReal_one, mul_one] at hp
    have hp' : HasDerivAt (fun r : ℝ => (a * r) ^ 2 + t ^ 2) (2 * a ^ 2 * r) r :=
      hp.congr_deriv (by ring)
    exact hp'.clog_real (sq_add_mul_sq_mem_slitPlane ha ht r)
  have hc : Continuous (fun r : ℝ => 2 * a ^ 2 * r / ((a * r) ^ 2 + t ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro r
    exact slitPlane_ne_zero (sq_add_mul_sq_mem_slitPlane ha ht r)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (hc.intervalIntegrable _ _)]
  norm_num only [ofReal_one, ofReal_zero, mul_one, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_add]
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have he : 1 + a ^ 2 / (t : ℂ) ^ 2 = (((t ^ 2)⁻¹ : ℝ) : ℂ) * (a ^ 2 + t ^ 2) := by
    push_cast
    field_simp [ht0]
    ring
  rw [he, Complex.log_ofReal_mul (inv_pos.mpr (sq_pos_of_pos ht)) (sq_add_sq_ne_zero ha t),
    Real.log_inv, Complex.ofReal_neg, ← Complex.ofReal_pow,
    ← Complex.ofReal_log (sq_nonneg t)]
  push_cast
  ring

/-- The radial logarithm kernel is absolutely integrable on the product of the segment and ray. -/
lemma integrable_quadratic_log_kernel {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun p : ℝ × ℝ => 2 * a ^ 2 * p.1 / ((a * p.1) ^ 2 + p.2 ^ 2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let G : ℝ → ℂ := fun t => 2 * a ^ 2 / (a ^ 2 + t ^ 2)
  have hiG : IntegrableOn G (Ioi 0) := by
    have h := (integrableOn_pow_div_sq_add_sq_pow ha 0 1 (by norm_num)).const_mul (2 * a ^ 2)
    simpa only [IntegrableOn, G, pow_zero, pow_one, mul_one_div] using h
  have hscale {r : ℝ} (hr : 0 < r) (t : ℝ) :
      2 * a ^ 2 * r / ((a * r) ^ 2 + t ^ 2) = (r : ℂ)⁻¹ * G (r⁻¹ * t) := by
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    dsimp only [G]
    push_cast
    field_simp [hr0]
  have hrow {r : ℝ} (hr : 0 < r) :
      IntegrableOn (fun t : ℝ => 2 * a ^ 2 * r / ((a * r) ^ 2 + t ^ 2)) (Ioi 0) := by
    simp_rw [hscale hr]
    exact ((integrableOn_Ioi_comp_mul_left_iff G 0 (inv_pos.mpr hr)).mpr
      (by simpa using hiG)).const_mul _
  have hnorm {r : ℝ} (hr : 0 < r) :
      (∫ t : ℝ in Ioi 0, ‖2 * a ^ 2 * r / ((a * r) ^ 2 + t ^ 2)‖) =
        ∫ t : ℝ in Ioi 0, ‖G t‖ := by
    simp_rw [hscale hr, norm_mul]
    rw [integral_const_mul, integral_comp_mul_left_Ioi (fun t : ℝ => ‖G t‖) 0 (inv_pos.mpr hr)]
    simp only [mul_zero, smul_eq_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr.le, inv_inv]
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  apply (integrable_prod_iff (show Measurable (fun p : ℝ × ℝ =>
    2 * a ^ 2 * p.1 / ((a * p.1) ^ 2 + p.2 ^ 2)) from by fun_prop).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hrow hr.1
  · refine (integrable_const (∫ t : ℝ in Ioi 0, ‖G t‖)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hnorm hr.1).symm

/-- The logarithmic quadratic kernel times a cosine is absolutely integrable on the positive ray. -/
lemma integrableOn_log_one_add_sq_div_sq_mul_cos {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.log (1 + a ^ 2 / t ^ 2) *
      (Real.cos (x * t) : ℂ)) (Ioi 0) := by
  let F : ℝ × ℝ → ℂ := fun p => (2 * a ^ 2 * p.1 / ((a * p.1) ^ 2 + p.2 ^ 2)) *
    (Real.cos (x * p.2) : ℂ)
  have hF : Integrable F ((volume.restrict (Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_quadratic_log_kernel ha).norm.mono' (by fun_prop) ?_
    exact Eventually.of_forall fun p => by
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
  refine hF.integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  dsimp only [F]
  rw [integral_mul_const, ← intervalIntegral.integral_of_le zero_le_one,
    integral_quadratic_log_kernel ha ht]

end Complex
