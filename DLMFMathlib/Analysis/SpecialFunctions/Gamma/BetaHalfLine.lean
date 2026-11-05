/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Euler's beta integral on the positive half-line

The change of variables `u = t / (1 + t)` gives the complex half-line beta integral.
The real integrability criterion comes from Tau Ceti's second beta integral.
-/

@[expose] public noncomputable section

open MeasureTheory intervalIntegral
open scoped Real

namespace Complex

/-- Euler's second beta integral, including the totalized nonintegrable cases. -/
theorem integral_cpow_div_one_add_cpow (a b : ℂ) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b) =
      betaIntegral a b := by
  -- The substitution `u = t / (1 + t)` maps `(0, ∞)` onto `(0, 1)`.
  set f : ℝ → ℝ := fun t => t / (1 + t) with hf
  set f' : ℝ → ℝ := fun t => 1 / (1 + t) ^ 2 with hf'
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Set.Ioi 0) t := by
    intro t ht
    have h1 : 1 + t ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp ht])
    have hd : HasDerivAt f (f' t) t := by
      convert (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) h1 using 1
      · rfl
      · simp only [hf', id]
        ring
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 1 + x ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hx])
    have hy' : 1 + y ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hy])
    simp only [hf] at hxy
    field_simp at hxy
    linarith
  have himage : f '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : 0 < t := ht
      refine ⟨by positivity, ?_⟩
      rw [hf, div_lt_one (by linarith)]
      linarith
    · rintro ⟨h0, h1⟩
      refine ⟨u / (1 - u), div_pos h0 (by linarith), ?_⟩
      have : 1 - u ≠ 0 := ne_of_gt (by linarith)
      simp only [hf]
      field_simp
      ring
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1))
  rw [himage] at key
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have ht1 : 0 < 1 + t := by linarith
  have hft : 0 < f t := by simp only [hf]; positivity
  have hcpow (x : ℝ) (hx : 0 < x) (s : ℂ) :
      (x : ℂ) ^ s = Complex.exp (Real.log x * s) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hlogf : Real.log (f t) = Real.log t - Real.log (1 + t) := by
    simp only [hf]
    exact Real.log_div ht0.ne' ht1.ne'
  have h1f : 1 - f t = (1 + t)⁻¹ := by
    simp only [hf]
    field_simp
    ring
  have habs : |f' t| = Real.exp (-2 * Real.log (1 + t)) := by
    rw [abs_of_pos (by simp only [hf']; positivity),
      show -2 * Real.log (1 + t) = -(Real.log (1 + t) + Real.log (1 + t)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log ht1]
    simp only [hf']
    ring
  have e2 : (1 + (t : ℂ)) ^ (a + b) = Complex.exp (Real.log (1 + t) * (a + b)) := by
    rw [← hcpow _ ht1]
    push_cast
    rfl
  have e4 : (1 - ((f t : ℝ) : ℂ)) ^ (b - 1) = Complex.exp (-Real.log (1 + t) * (b - 1)) := by
    rw [show (1 - ((f t : ℝ) : ℂ)) = ((1 - f t : ℝ) : ℂ) by push_cast; rfl,
      hcpow _ (by rw [h1f]; positivity), h1f, Real.log_inv]
    push_cast
    rfl
  rw [hcpow _ ht0, e2, hcpow _ hft, e4, habs, Complex.real_smul, Complex.ofReal_exp, hlogf,
    ← Complex.exp_sub, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Absolute convergence of the complex second beta integral in its defining domain. -/
theorem integrableOn_cpow_div_one_add_cpow {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b))
      (Set.Ioi 0) := by
  have h := (TauCeti.integrableOn_rpow_mul_one_add_rpow_iff (a := a.re) (b := b.re) ha).mpr hb
  refine h.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos ht0,
    show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [sub_re, one_re, add_re]
  rw [Real.rpow_neg (by linarith : 0 ≤ 1 + t), div_eq_mul_inv]

end Complex
