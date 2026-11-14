/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Basic.Real.Sign
public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.Analysis.Fourier.ExpNegAbs
import TauCeti.Analysis.SpecialFunctions.Exp.Oscillation
import DLMFMathlib.Analysis.Fourier.Pairing
import DLMFMathlib.Analysis.Integral.HilbertRegularization
import Mathlib.Tactic

/-!
# The sign function and Fourier principal values

Exponential damping makes the sign function integrable. Its Fourier transform is a
conjugate-Poisson kernel, so Fourier pairing and dominated convergence identify the
Fourier transform of sign with the Hilbert principal value.

The proofs use TauCeti's two-sided exponential integral and exponential-product API
(`integral_exp_mul_I_mul_exp_neg_mul_abs`, `integrable_exp_neg_mul_abs`, and
`exp_mul_I_mul_ofReal_exp_mul`) and Mathlib's half-line complex exponential integrals.
Fourier pairing and principal-value regularization come from the corresponding
`DLMFMathlib` support modules. No upstream proof bodies are copied.

* `Real.fourierInv_sign_mul_exp_neg_mul_abs`: the damped Fourier integral.
* `Real.integral_sign_mul_fourierInv_eq_integral_symmetric_div`: the principal-value pairing.
-/

public noncomputable section

open MeasureTheory Set Complex Filter
open scoped FourierTransform Topology

namespace Real

/-- The Abel-regularized sign function has a rational oscillatory integral. -/
lemma integral_exp_mul_I_mul_sign_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ, Complex.exp ((b : ℂ) * x * I) *
      ((Real.sign x : ℂ) * (Real.exp (-(a * |x|)) : ℂ))) =
        2 * I * b / ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
  let G : ℝ → ℂ := fun x => Complex.exp ((b : ℂ) * x * I) * (Real.exp (-(a * |x|)) : ℂ)
  have hG : Integrable G := TauCeti.integrable_exp_mul_I_mul_exp_neg_mul_abs ha b
  have hgi : Integrable ((Ioi (0 : ℝ)).indicator G) := hG.indicator measurableSet_Ioi
  have he : (fun x : ℝ => Complex.exp ((b : ℂ) * x * I) *
      ((Real.sign x : ℂ) * (Real.exp (-(a * |x|)) : ℂ))) =ᵐ[volume]
      (fun x => 2 * (Ioi (0 : ℝ)).indicator G x - G x) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
    rcases hx.lt_or_gt with hx | hx
    · simp [G, Real.sign_of_neg hx, not_lt.mpr hx.le]
    · simp [G, hx, Real.sign_of_pos hx, mul_assoc]
      ring
  rw [integral_congr_ae he, integral_sub (hgi.const_mul 2) hG,
    integral_const_mul, integral_indicator measurableSet_Ioi]
  have hp : EqOn G (fun x : ℝ => Complex.exp ((-(a : ℂ) + b * I) * x)) (Ioi 0) := by
    intro x hx
    dsimp [G]
    rw [abs_of_pos hx, show -(a * x) = -a * x by ring]
    simpa only [ofReal_neg] using TauCeti.exp_mul_I_mul_ofReal_exp_mul b (-a) x
  rw [setIntegral_congr_fun measurableSet_Ioi hp,
    integral_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr ha),
    TauCeti.integral_exp_mul_I_mul_exp_neg_mul_abs ha b]
  have hne : -(a : ℂ) + b * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [add_re, neg_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, zero_re] at hh
    linarith
  have hden : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < a ^ 2 + b ^ 2 by positivity))
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp [hne, hden]
  linear_combination -((b : ℂ) ^ 2) * Complex.I_sq
/-- Exponential damping makes the sign function integrable at every positive rate. -/
lemma integrable_sign_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (Real.sign x : ℂ) * (Real.exp (-(a * |x|)) : ℂ)) := by
  refine ((TauCeti.integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) ?_ ?_
  · have hm : Measurable (fun x : ℝ => (Real.sign x : ℂ)) := by
      have hs : Measurable Real.sign := by
        unfold Real.sign
        exact measurable_const.ite measurableSet_Iio
          (measurable_const.ite measurableSet_Ioi measurable_const)
      exact Complex.continuous_ofReal.measurable.comp hs
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rcases Real.sign_apply_eq x with hx | hx | hx <;> simp [hx]

/-- The inverse Fourier transform of the exponentially damped sign function. -/
lemma fourierInv_sign_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕⁻ (fun x : ℝ => (Real.sign x : ℂ) * (Real.exp (-(a * |x|)) : ℂ)) ξ =
      2 * I * (2 * Real.pi * ξ) / ((a : ℂ) ^ 2 + ((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) := by
  rw [Real.fourierInv_eq']
  have h := integral_exp_mul_I_mul_sign_mul_exp_neg_mul_abs ha (2 * Real.pi * ξ)
  convert h using 1
  · congr 1
    funext x
    simp only [smul_eq_mul, Real.inner_apply]
    congr 2
    push_cast
    ring
  · push_cast
    ring

/-- Damping at rate `2πa` produces the conjugate-Poisson kernel in Fourier variables. -/
lemma fourierInv_sign_mul_exp_neg_two_pi_mul_abs {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕⁻ (fun x : ℝ => (Real.sign x : ℂ) *
      (Real.exp (-(2 * Real.pi * a * |x|)) : ℂ)) ξ =
      (I / (Real.pi : ℂ)) * ((ξ / (ξ ^ 2 + a ^ 2) : ℝ) : ℂ) := by
  rw [fourierInv_sign_mul_exp_neg_mul_abs (by positivity : 0 < 2 * Real.pi * a)]
  have hden : (ξ : ℂ) ^ 2 + (a : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < ξ ^ 2 + a ^ 2 by positivity))
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hden, hpi]
  linear_combination (ξ : ℂ) * (mul_inv_cancel₀ hden)

/-- Pairing the inverse Fourier integral with the sign function gives the Hilbert principal value.
Continuity and differentiability at zero provide local cancellation; absolute integrability
is required for both the function and its inverse Fourier transform. -/
lemma integral_sign_mul_fourierInv_eq_integral_symmetric_div {f : ℝ → ℂ}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hi : Integrable f)
    (hF : Integrable (𝓕⁻ f)) :
    (∫ x : ℝ, (Real.sign x : ℂ) * 𝓕⁻ f x) =
      (I / (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ), (f t - f (-t)) / (t : ℂ) := by
  let R (a x : ℝ) : ℂ := (Real.sign x : ℂ) *
    (Real.exp (-(2 * Real.pi * a * |x|)) : ℂ)
  have hm : Measurable (fun x : ℝ => (Real.sign x : ℂ)) := by
    have hs : Measurable Real.sign := by
      unfold Real.sign
      exact measurable_const.ite measurableSet_Iio
        (measurable_const.ite measurableSet_Ioi measurable_const)
    exact Complex.continuous_ofReal.measurable.comp hs
  have hlim : Filter.Tendsto (fun a : ℝ => ∫ x : ℝ, R a x * 𝓕⁻ f x) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ, (Real.sign x : ℂ) * 𝓕⁻ f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖𝓕⁻ f x‖)
    · exact Eventually.of_forall fun a =>
        (hm.aestronglyMeasurable.mul (by fun_prop)).mul hF.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      exact Eventually.of_forall fun x => by
        have hsign : |Real.sign x| ≤ 1 := by
          rcases Real.sign_apply_eq x with hx | hx | hx <;> simp [hx]
        have hexp : Real.exp (-(2 * Real.pi * a * |x|)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
        dsimp only [R]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        have hb := mul_le_mul hsign hexp (Real.exp_pos _).le zero_le_one
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (𝓕⁻ f x))
    · exact hF.norm
    · exact Eventually.of_forall fun x => by
        have ha0 : Filter.Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
        have hexp : Filter.Tendsto (fun a : ℝ => Real.exp (-(2 * Real.pi * a * |x|)))
            (𝓝[>] 0) (𝓝 1) := by
          have hneg : Filter.Tendsto (fun a : ℝ => -(2 * Real.pi * a * |x|))
              (𝓝[>] 0) (𝓝 0) := by
            simpa only [mul_zero, zero_mul, neg_zero] using
              ((ha0.const_mul (2 * Real.pi)).mul_const |x|).neg
          simpa only [Function.comp_def, Real.exp_zero] using
            (Real.continuous_exp.tendsto 0).comp hneg
        simpa only [Function.comp_def, R, ofReal_one, mul_one] using
          (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto 1).comp hexp)).mul_const
            (𝓕⁻ f x)
  have hp (a : ℝ) (ha : 0 < a) : (∫ x : ℝ, R a x * 𝓕⁻ f x) =
      (I / (Real.pi : ℂ)) * ∫ t : ℝ, ((t / (t ^ 2 + a ^ 2) : ℝ) : ℂ) * f t := by
    rw [← Real.integral_fourierInv_mul_eq_flip
      (integrable_sign_mul_exp_neg_mul_abs (by positivity : 0 < 2 * Real.pi * a)) hi]
    simp_rw [fourierInv_sign_mul_exp_neg_two_pi_mul_abs ha]
    rw [← integral_const_mul]
    congr 1
    funext x
    exact mul_assoc _ _ _
  have hr := (tendsto_integral_conjugatePoissonKernel hc hd hi).const_mul (I / (Real.pi : ℂ))
  have hreg : Filter.Tendsto (fun a : ℝ => ∫ x : ℝ, R a x * 𝓕⁻ f x) (𝓝[>] 0)
      (𝓝 ((I / (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ), (f t - f (-t)) / (t : ℂ))) := by
    refine hr.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    exact (hp a ha).symm
  exact tendsto_nhds_unique hlim hreg

end Real
