/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.HermiteKernel

/-!
# Lerch's Hermite representation in the initial half-plane

For negative real logarithmic arguments and orders with positive real part, the
Gamma–Laplace interchanges express Lerch's integral as its elementary endpoint term,
its ray integral and the Hermite correction.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.Zeta.LerchHermite

/-- Lerch's Hermite identity for a negative real logarithmic argument in the Gamma
half-plane of orders. -/
theorem lerchPhi_exp_eq_of_real_pos_order {a s : ℂ} (ha : 0 < a.re) (hs : 0 < s.re)
    {r : ℝ} (hr : r < 0) :
    lerchPhi (exp (r : ℂ)) s a = a ^ (-s) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel s a r x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel s a r y := by
  let C : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-(a * t))
  let B : ℝ → ℂ := fun t => C t * (DLMF.Gamma.binetBeta (t - r) : ℂ)
  let P : ℝ → ℂ := fun t => C t / (t - r)
  have hC : IntegrableOn C (Ioi 0) := integrableOn_cpow_mul_exp_neg_mul hs ha
  have hP : IntegrableOn P (Ioi 0) := by
    refine (hC.norm.div_const (-r)).mono'
      ((show Measurable P by dsimp [P, C]; fun_prop).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hu : 0 < t - r := by linarith
    change ‖C t / ((t : ℂ) - r)‖ ≤ ‖C t‖ / (-r)
    rw [norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith)
  have hB : IntegrableOn B (Ioi 0) := by
    have h := (integrable_doubleKernel ha hs hr).integral_prod_left.const_mul (2 : ℂ)
    refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
    change 2 * (∫ y in Ioi (0 : ℝ), doubleKernel s a r t y) = B t
    rw [integral_doubleKernel_second hr ht]
    dsimp [B, C]
    ring
  have hpoint (t : ℝ) (ht : t ∈ Ioi 0) :
      C t / (1 - exp ((r : ℂ) - t)) = B t + C t / 2 + P t := by
    have ht0 : 0 < t := ht
    have hu : 0 < t - r := by linarith
    have h := congrArg (fun x : ℝ => (x : ℂ))
      (DLMF.Gamma.binetKernel_eq_binetBeta hu)
    rw [DLMF.Gamma.binetKernel] at h
    push_cast at h
    rw [neg_sub] at h
    dsimp [B, P]
    linear_combination C t * h
  have hGamma := Gamma_ne_zero_of_re_pos hs
  have hz : exp (r : ℂ) ∈ slitOne := Or.inr (by
    rw [exp_ofReal_re]
    exact Real.exp_lt_one_iff.mpr hr)
  obtain ⟨F, hF⟩ := exists_isLerchContinuation s a
  have hPhi := hF.eq_lerchInt hs ha hz
  rw [← lerchPhi_eq_of_isLerchContinuation hF hz] at hPhi
  have hPhiGamma : Gamma s * lerchPhi (exp (r : ℂ)) s a =
      ∫ t in Ioi (0 : ℝ), C t / (1 - exp ((r : ℂ) - t)) := by
    rw [hPhi, ← mul_assoc, mul_inv_cancel₀ hGamma, one_mul, lerchIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← exp_add, show (r : ℂ) + -(t : ℂ) = (r : ℂ) - t by ring]
  have hsplit : (∫ t in Ioi (0 : ℝ), B t + C t / 2 + P t) =
      (∫ t in Ioi (0 : ℝ), B t) + (∫ t in Ioi (0 : ℝ), C t) / 2 +
        ∫ t in Ioi (0 : ℝ), P t := by
    have h1 := integral_add (hB.add (hC.div_const 2)) hP
    have h2 := integral_add hB (hC.div_const 2)
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2, integral_div]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, hsplit,
    show (∫ t in Ioi (0 : ℝ), C t) = Gamma s * a ^ (-s) from
      integral_cpow_mul_cexp_neg_mul_Ioi hs ha] at hPhiGamma
  have hK := gamma_mul_integral_kernel_of_real ha hs hr
  change Gamma s * (∫ y in Ioi (0 : ℝ), kernel s a r y) = (∫ t in Ioi (0 : ℝ), B t) / 2 at hK
  have hR := gamma_mul_integral_rayKernel_of_real ha hs hr
  change Gamma s * (∫ x in Ioi (0 : ℝ), rayKernel s a r x) = ∫ t in Ioi (0 : ℝ), P t at hR
  apply mul_left_cancel₀ hGamma
  linear_combination hPhiGamma - 2 * hK - hR

end DLMF.Zeta.LerchHermite
