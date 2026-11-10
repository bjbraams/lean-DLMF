/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra
public import Mathlib.Analysis.MellinTransform

/-!
# Cubic Laplace moments and Mellin transforms

The substitution `u = t³` expresses the moments of `exp(-a t³)` through the Gamma function
when `Re a > 0`. These formulas give absolute Mellin convergence and a uniform bound on
vertical lines, as well as the corresponding formulas for the ordinary exponential kernel.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology

namespace Complex.CubicLaplace
/-- The cubic Laplace moment is a scaled Gamma integral for `Re s > -1`, `Re a > 0`. -/
theorem integral_cpow_mul_exp_neg_mul_cube {s a : ℂ} (hs : -1 < s.re) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ s * exp (-(a * (t : ℂ) ^ 3))) =
      Gamma ((s + 1) / 3) * a ^ (-((s + 1) / 3)) / 3 := by
  have hG := integral_cpow_mul_cexp_neg_mul_Ioi (s := (s + 1) / 3)
    (z := a) (by simp only [div_ofNat_re, add_re, one_re]; linarith) ha
  have hp := integral_comp_rpow_Ioi_of_pos
    (g := fun u : ℝ => (u : ℂ) ^ ((s + 1) / 3 - 1) * exp (-(a * u)))
    (p := (3 : ℝ)) (by norm_num)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      ((3 : ℝ) * t ^ ((3 : ℝ) - 1)) •
        (((t ^ (3 : ℝ) : ℝ) : ℂ) ^ ((s + 1) / 3 - 1) *
          exp (-(a * ((t ^ (3 : ℝ) : ℝ) : ℂ)))) =
      3 * ((t : ℂ) ^ s * exp (-(a * (t : ℂ) ^ 3))) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hc : ((t ^ (3 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (3 : ℂ) := by
      exact ofReal_cpow ht.le 3
    have hc2 : ((t ^ ((3 : ℝ) - 1) : ℝ) : ℂ) = (t : ℂ) ^ (2 : ℂ) := by
      norm_num
    have hi : (log (t : ℂ) * (3 : ℂ)).im = 0 := by
      simp [mul_im, log_im, arg_ofReal_of_nonneg ht.le]
    simp only [Complex.real_smul, ofReal_mul, ofReal_ofNat, hc, hc2]
    rw [← cpow_mul _ (by rw [hi]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hi]; exact Real.pi_pos.le)]
    have he : (3 : ℂ) * ((s + 1) / 3 - 1) = s - 2 := by ring
    rw [he]
    rw [← cpow_natCast]
    calc _ = 3 * (((t : ℂ) ^ (2 : ℂ) * (t : ℂ) ^ (s - 2)) *
        exp (-(a * (t : ℂ) ^ (3 : ℂ)))) := by ring
      _ = _ := by
        rw [← cpow_add _ _ ht0, show (2 : ℂ) + (s - 2) = s by ring]
        norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul, hG] at hp
  linear_combination (1 / 3 : ℂ) * hp


/-- Absolute integrability of cubic Laplace moments for `Re s > -1`, `Re a > 0`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_cube {s a : ℂ} (hs : -1 < s.re) (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ s * exp (-(a * (t : ℂ) ^ 3))) (Ioi 0) := by
  have hr := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 3) (s := s.re)
    (b := a.re) hs (by norm_num) ha
  refine hr.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  have ht3 : t ^ (3 : ℝ) = t ^ (3 : ℕ) := Real.rpow_natCast t 3
  rw [ht3]
  rw [show (t : ℂ) ^ 3 = ((t ^ 3 : ℝ) : ℂ) by norm_cast]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  simp only [neg_mul, le_refl]

/-- The Mellin transform of a cubic exponential on the right half-plane. -/
theorem mellin_exp_neg_mul_cube {v a : ℂ} (hv : 0 < v.re) (ha : 0 < a.re) :
    mellin (fun t : ℝ => exp (-(a * (t : ℂ) ^ 3))) v =
      Gamma (v / 3) * a ^ (-(v / 3)) / 3 := by
  rw [mellin]
  simp only [smul_eq_mul]
  rw [integral_cpow_mul_exp_neg_mul_cube
    (by simp only [sub_re, one_re]; linarith) ha, sub_add_cancel]

/-- The cubic exponential has an absolutely convergent Mellin transform for `Re v > 0`. -/
theorem mellinConvergent_exp_neg_mul_cube {v a : ℂ} (hv : 0 < v.re) (ha : 0 < a.re) :
    MellinConvergent (fun t : ℝ => exp (-(a * (t : ℂ) ^ 3))) v := by
  simpa only [MellinConvergent, smul_eq_mul] using
    integrableOn_cpow_mul_exp_neg_mul_cube (s := v - 1) (by simp only [sub_re, one_re]; linarith) ha

/-- The exponential kernel has an absolutely convergent Mellin transform for `Re v > 0`. -/
theorem mellinConvergent_exp_neg_mul {v q : ℂ} (hv : 0 < v.re) (hq : 0 < q.re) :
    MellinConvergent (fun t : ℝ => exp (-(q * t))) v := by
  simpa only [MellinConvergent, smul_eq_mul] using integrableOn_cpow_mul_exp_neg_mul hv hq

/-- The Mellin transform of an exponentially damped kernel is a scaled Gamma function. -/
theorem mellin_exp_neg_mul {v q : ℂ} (hv : 0 < v.re) (hq : 0 < q.re) :
    mellin (fun t : ℝ => exp (-(q * t))) v = Gamma v * q ^ (-v) := by
  simpa only [mellin, smul_eq_mul] using integral_cpow_mul_cexp_neg_mul_Ioi hv hq

/-- The Mellin transform of a cubic exponential is uniformly bounded on each vertical line. -/
theorem norm_mellin_exp_neg_mul_cube_le (p y : ℝ) (a : ℂ) :
    ‖mellin (fun t : ℝ => exp (-(a * (t : ℂ) ^ 3))) ((p : ℂ) + y * I)‖ ≤
      ∫ t : ℝ in Ioi 0, t ^ (p - 1) * Real.exp (-(a.re * t ^ 3)) := by
  rw [mellin]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [smul_eq_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  rw [show (t : ℂ) ^ 3 = ((t ^ 3 : ℝ) : ℂ) by norm_cast]
  simp only [sub_re, add_re, ofReal_re, ofReal_im, mul_re, I_re, I_im, mul_zero, zero_mul,
    sub_zero, add_zero, one_re, neg_re]


end Complex.CubicLaplace
