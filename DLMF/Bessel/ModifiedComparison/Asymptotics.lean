/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.ModifiedComparison
public import DLMF.Bessel.Asymptotics
public import DLMF.Bessel.SturmZeros
public import DLMFMathlib.Analysis.ODE.RecessiveUniqueness
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Normalized recessive modified-Bessel comparisons

Hankel's expansion and the positive-axis expansion of `I_ν` give the exponential
normalizations of `sqrt(x) K_ν(μx)` and `sqrt(x) I_ν(μx)`, together with their derivatives.
The derivative weight of the comparison Green kernel tends to zero at infinity.

For an integrable perturbation of the modified-Bessel normal form, a decaying solution
with the recessive normalization has relative error bounded by the exponential of the
remaining variation, provided the total-variation bound is less than one. Uniqueness
identifies this solution with the one constructed by the Liouville–Green comparison API.
These estimates support DLMF §14.15.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology
@[expose] public noncomputable section
namespace DLMF.Bessel.ModifiedComparison

/-- The positive-axis exponential normalization of `K_ν`, for every complex order. -/
lemma tendsto_sqrt_mul_exp_mul_besselK (ν : ℂ) :
    Tendsto (fun x : ℝ => (Real.sqrt x : ℂ) * exp x * besselK ν x) atTop
      (𝓝 ((Real.sqrt π / Real.sqrt 2 : ℝ) : ℂ)) := by
  have ho := besselK_ray_isBigO ν (c := 1) (by simp) (α := 0)
    (by simp; positivity) (by norm_num)
  simp only [one_mul] at ho
  have hm := (isBigO_refl (fun x : ℝ => Real.sqrt x) atTop).mul ho.norm_left
  have ht : Tendsto (fun x : ℝ => Real.sqrt x * x ^ (-(3/2) : ℝ)) atTop
      (𝓝 0) := by
    have hh : (fun x : ℝ => Real.sqrt x * x ^ (-(3/2) : ℝ)) =ᶠ[atTop]
        fun x => x⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      norm_num [Real.rpow_neg_one]
    exact tendsto_inv_atTop_zero.congr' hh.symm
  have hzero : Tendsto (fun x : ℝ => (Real.sqrt x : ℂ) *
      (exp x * besselK ν x - (2 * (x : ℂ)) ^ (-(1/2 : ℂ)) * Real.sqrt π)) atTop
      (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hm.trans_tendsto ht using 1
    funext x
    rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  have heq : (fun x : ℝ => (Real.sqrt x : ℂ) *
      (exp x * besselK ν x - (2 * (x : ℂ)) ^ (-(1/2 : ℂ)) * Real.sqrt π)) =ᶠ[atTop]
      fun x => (Real.sqrt x : ℂ) * exp x * besselK ν x -
        ((Real.sqrt π / Real.sqrt 2 : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [show 2 * (x : ℂ) = ((2*x : ℝ) : ℂ) by push_cast; ring,
      show (-(1/2 : ℂ)) = ((-(1/2):ℝ):ℂ) by norm_num,
      ← ofReal_cpow (by positivity : (0:ℝ) ≤ 2*x),
      Real.rpow_neg (by positivity : (0:ℝ) ≤ 2*x), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    field_simp [(Real.sqrt_pos.mpr hx).ne',
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne']
  exact (tendsto_sub_nhds_zero_iff.mp (hzero.congr' heq))

/-- The positive-axis exponential normalization of `I_ν` for nonnegative real order. -/
lemma tendsto_sqrt_mul_exp_neg_mul_besselI {ν : ℝ} (hν : 0 ≤ ν) :
    Tendsto (fun x : ℝ => (Real.sqrt x : ℂ) * exp (-x) * besselI ν x) atTop
      (𝓝 (((Real.sqrt (2*π))⁻¹ : ℝ) : ℂ)) := by
  have hn : ∀ k : ℕ, 1 + 2 * (ν:ℂ) ≠ -k := by
    intro k hk
    have hr := congrArg re hk
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have he := (IsEquivalent.refl (u := fun x : ℝ => (Real.sqrt x : ℂ) * exp (-x))
    (l := atTop)).mul (besselI_isEquivalent hn)
  apply IsEquivalent.tendsto_const
  refine he.congr_right ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Pi.mul_apply, Function.const_apply]
  rw [show 2*π*x = (2*π)*x by ring, Real.sqrt_mul (by positivity : 0 ≤ 2*π)]
  rw [ofReal_div, ofReal_exp, ofReal_mul, ← mul_div_assoc,
    show (Real.sqrt x:ℂ)*exp (-(x:ℂ))*exp x = Real.sqrt x by
      rw [mul_assoc, ← exp_add]; simp]
  field_simp [(Real.sqrt_pos.mpr hx).ne',
    (Real.sqrt_pos.mpr (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)).ne']
  rw [ofReal_div, ofReal_one]
  field_simp [(Real.sqrt_pos.mpr (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)).ne']

/-- The scaled recessive comparison function has its fixed exponential normalization. -/
lemma tendsto_exp_mul_recessive (ν : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun x : ℝ => exp ((μ:ℂ)*x) * recessive ν μ x) atTop
      (𝓝 (((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ)) : ℂ)) := by
  have h := ((tendsto_sqrt_mul_exp_mul_besselK ν).comp
    (tendsto_id.const_mul_atTop hμ)).div_const (Real.sqrt μ : ℂ)
  simp only [Function.comp_apply, id_eq, ← ofReal_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [recessive, ofReal_mul]
  rw [Real.sqrt_mul hμ.le, ofReal_mul]
  field_simp [(Real.sqrt_pos.mpr hμ).ne']

/-- The scaled dominant comparison function has its fixed exponential normalization. -/
lemma tendsto_exp_neg_mul_dominant {ν μ : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ) :
    Tendsto (fun x : ℝ => exp (-((μ:ℂ)*x)) * dominant ν μ x) atTop
      (𝓝 (((Real.sqrt (2*π))⁻¹ / Real.sqrt μ : ℝ) : ℂ)) := by
  have h := ((tendsto_sqrt_mul_exp_neg_mul_besselI hν).comp
    (tendsto_id.const_mul_atTop hμ)).div_const (Real.sqrt μ : ℂ)
  simp only [Function.comp_apply, id_eq, ← ofReal_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [dominant, ofReal_mul]
  rw [Real.sqrt_mul hμ.le, ofReal_mul]
  field_simp [(Real.sqrt_pos.mpr hμ).ne']

/-- The scaled recessive derivative is expressed by the adjacent-order recurrence. -/
lemma recessiveDerivative_eq {ν μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) :
    recessiveDerivative ν μ x = ((ν + 1/2 : ℝ):ℂ) / x * recessive ν μ x -
      μ * recessive (ν+1) μ x := by
  have hz : (μ:ℂ)*x ∈ slitPlane := Or.inl (by simp; positivity)
  rw [recessiveDerivative, (hasDerivAt_besselK ν hz).deriv]
  simp only [recessive, ofReal_add, ofReal_one]
  have hsq : (Real.sqrt x:ℂ)^2 = x := by rw [← ofReal_pow, Real.sq_sqrt hx.le]
  have hs : (Real.sqrt x:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  push_cast
  field_simp [hs, ofReal_ne_zero.mpr hμ.ne', ofReal_ne_zero.mpr hx.ne']
  linear_combination -1 * (besselK ν ((μ:ℂ)*x)) * hsq

/-- The scaled dominant derivative is expressed by the adjacent-order recurrence. -/
lemma dominantDerivative_eq {ν μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) :
    dominantDerivative ν μ x = ((ν + 1/2 : ℝ):ℂ) / x * dominant ν μ x +
      μ * dominant (ν+1) μ x := by
  have hz : (μ:ℂ)*x ∈ slitPlane := Or.inl (by simp; positivity)
  rw [dominantDerivative, (hasDerivAt_besselI (ν := (ν:ℂ)) hz).deriv]
  simp only [dominant, ofReal_add, ofReal_one]
  have hsq : (Real.sqrt x:ℂ)^2 = x := by rw [← ofReal_pow, Real.sq_sqrt hx.le]
  have hs : (Real.sqrt x:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  push_cast
  field_simp [hs, ofReal_ne_zero.mpr hμ.ne', ofReal_ne_zero.mpr hx.ne']
  linear_combination -1 * (besselI ν ((μ:ℂ)*x)) * hsq

/-- The recessive derivative has exponential normalization `-μ` times that of the function. -/
lemma tendsto_exp_mul_recessiveDerivative (ν : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun x : ℝ => exp ((μ:ℂ)*x) * recessiveDerivative ν μ x) atTop
      (𝓝 (-(μ:ℂ) * ((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ):ℂ))) := by
  have hc : Tendsto (fun x : ℝ => ((ν+1/2:ℝ):ℂ) / x) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ofReal_inv, ofReal_zero, mul_zero, div_eq_mul_inv] using
      ((continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul ((ν+1/2:ℝ):ℂ)
  have h := (hc.mul (tendsto_exp_mul_recessive ν hμ)).sub
    ((tendsto_exp_mul_recessive (ν+1) hμ).const_mul (μ:ℂ))
  simp only [zero_mul, zero_sub, neg_mul] at h ⊢
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [recessiveDerivative_eq hμ hx]
  ring

/-- The dominant derivative has exponential normalization `μ` times that of the function. -/
lemma tendsto_exp_neg_mul_dominantDerivative {ν μ : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ) :
    Tendsto (fun x : ℝ => exp (-((μ:ℂ)*x)) * dominantDerivative ν μ x) atTop
      (𝓝 ((μ:ℂ) * (((Real.sqrt (2*π))⁻¹ / Real.sqrt μ : ℝ):ℂ))) := by
  have hc : Tendsto (fun x : ℝ => ((ν+1/2:ℝ):ℂ) / x) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ofReal_inv, ofReal_zero, mul_zero, div_eq_mul_inv] using
      ((continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul ((ν+1/2:ℝ):ℂ)
  have h := (hc.mul (tendsto_exp_neg_mul_dominant hν hμ)).add
    ((tendsto_exp_neg_mul_dominant (by linarith : 0 ≤ ν+1) hμ).const_mul (μ:ℂ))
  simp only [zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [dominantDerivative_eq hμ hx]
  ring


/-- The scaled recessive comparison function tends to zero on the positive axis. -/
lemma tendsto_recessive_zero (ν : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (recessive ν μ) atTop (𝓝 0) := by
  have hExp : Tendsto (fun x : ℝ => exp (-((μ:ℂ)*x))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hμ))).ofReal :
        Tendsto (fun x : ℝ => (Real.exp (-(μ*x)) : ℂ)) atTop (𝓝 (0:ℂ)))
    simpa only [Function.comp_apply, id_eq, ofReal_exp, ofReal_neg, ofReal_mul,
      ofReal_zero] using h
  have h := hExp.mul (tendsto_exp_mul_recessive ν hμ)
  simp only [zero_mul] at h
  convert h using 1
  funext x
  rw [← mul_assoc, ← exp_add]
  simp

/-- The first derivative of the recessive comparison function tends to zero. -/
lemma tendsto_recessiveDerivative_zero (ν : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (recessiveDerivative ν μ) atTop (𝓝 0) := by
  have hExp : Tendsto (fun x : ℝ => exp (-((μ:ℂ)*x))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hμ))).ofReal :
        Tendsto (fun x : ℝ => (Real.exp (-(μ*x)) : ℂ)) atTop (𝓝 (0:ℂ)))
    simpa only [Function.comp_apply, id_eq, ofReal_exp, ofReal_neg, ofReal_mul,
      ofReal_zero] using h
  have h := hExp.mul (tendsto_exp_mul_recessiveDerivative ν hμ)
  simp only [zero_mul] at h
  convert h using 1
  funext x
  rw [← mul_assoc, ← exp_add]
  simp

/-- The derivative envelope of the comparison Green kernel tends to zero at infinity. -/
lemma tendsto_derivativeWeight_zero {ν μ : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ) :
    Tendsto (derivativeWeight ν μ) atTop (𝓝 0) := by
  have hc : (((Real.sqrt (2*π))⁻¹ / Real.sqrt μ : ℝ):ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (div_ne_zero (inv_ne_zero
      (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<2*π)).ne')
      (Real.sqrt_pos.mpr hμ).ne')
  have h := (tendsto_exp_mul_recessiveDerivative ν hμ).norm.add
    ((tendsto_exp_neg_mul_dominantDerivative hν hμ).norm.mul
      ((tendsto_exp_mul_recessive ν hμ).norm.div
        (tendsto_exp_neg_mul_dominant hν hμ).norm (norm_ne_zero_iff.mpr hc)))
  have hExp : Tendsto (fun x : ℝ => exp (-((μ:ℂ)*x))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hμ))).ofReal :
        Tendsto (fun x : ℝ => (Real.exp (-(μ*x)) : ℂ)) atTop (𝓝 (0:ℂ)))
    simpa only [Function.comp_apply, id_eq, ofReal_exp, ofReal_neg, ofReal_mul,
      ofReal_zero] using h
  have hmul := hExp.norm.mul h
  simp only [norm_zero, zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hD := (norm_dominant_pos hν hμ hx).ne'
  simp only [Pi.div_apply, derivativeWeight, norm_mul, norm_exp, mul_re, ofReal_re,
    ofReal_im, mul_zero, sub_zero, neg_re] at *
  rw [Real.exp_neg]
  field_simp [hD, (Real.exp_pos (μ*x)).ne']

/-- A normalized decaying solution of the perturbed modified-Bessel equation has relative
error at most `exp((∫_x^∞ ‖ψ‖)/μ) - 1`, when the total-variation bound is less than one. -/
lemma norm_div_recessive_sub_one_le {ν μ : ℝ} (hν : 0 ≤ ν) (hμ : 0 < μ)
    {ψ : ℝ → ℂ} (hψc : ContinuousOn ψ (Ioi 0)) (hψi : IntegrableOn ψ (Ioi 0))
    (hsmall : Real.exp ((∫ t in Ioi 0, ‖ψ t‖) / μ) - 1 < 1)
    {f f' : ℝ → ℂ}
    (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 < x → HasDerivAt f'
      ((((μ ^ 2 + (ν ^ 2 - 1 / 4) / x ^ 2 : ℝ):ℂ) + ψ x) * f x) x)
    (hf0 : Tendsto f atTop (𝓝 0)) (hf'0 : Tendsto f' atTop (𝓝 0))
    (hfn : Tendsto (fun x : ℝ => exp ((μ:ℂ)*x) * f x) atTop
      (𝓝 (((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ)) : ℂ)))
    {x : ℝ} (hx : 0 < x) :
    ‖f x / recessive ν μ x - 1‖ ≤ Real.exp ((∫ t in Ioi x, ‖ψ t‖) / μ) - 1 := by
  obtain ⟨η,η',hη⟩ := exists_solution hν hμ hψc hψi
  let E : ℝ → ℝ := fun x => Real.exp ((∫ t in Ioi x, ‖ψ t‖) / μ) - 1
  have hEt : Tendsto E atTop (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ => ∫ t in Ioi x, ‖ψ t‖) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero tendsto_id
    have hd : Tendsto (fun x : ℝ => (∫ t in Ioi x, ‖ψ t‖) / μ) atTop (𝓝 0) := by
      simpa only [zero_div] using ht.div_const μ
    simpa only [Function.comp_apply, E, Real.exp_zero, sub_self] using
      ((Real.continuous_exp.tendsto 0).comp hd).sub_const 1
  have hbound (x : ℝ) (hx : 0 < x) : ‖η x‖ ≤ ‖recessive ν μ x‖ * E x := (hη x hx).2.2.1
  have hbound' (x : ℝ) (hx : 0 < x) : ‖η' x‖ ≤ derivativeWeight ν μ x * E x :=
    (hη x hx).2.2.2
  have hη0 : Tendsto η atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using (tendsto_recessive_zero ν hμ).norm.mul hEt)
    filter_upwards [eventually_gt_atTop 0] with x hx using hbound x hx
  have hη'0 : Tendsto η' atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using (tendsto_derivativeWeight_zero hν hμ).mul hEt)
    filter_upwards [eventually_gt_atTop 0] with x hx using hbound' x hx
  have hηn : Tendsto (fun x : ℝ => exp ((μ:ℂ)*x) * η x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using (tendsto_exp_mul_recessive ν hμ).norm.mul hEt)
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg _)
  have hyn : Tendsto (fun x : ℝ => exp ((μ:ℂ)*x) * (recessive ν μ x + η x)) atTop
      (𝓝 (((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ)) : ℂ)) := by
    simpa only [mul_add, add_zero] using (tendsto_exp_mul_recessive ν hμ).add hηn
  have hEsmall (x : ℝ) (hx : 0 < x) : E x < 1 := by
    have hle : (∫ t in Ioi x, ‖ψ t‖) ≤ ∫ t in Ioi 0, ‖ψ t‖ :=
      setIntegral_mono_set hψi.norm (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall fun _ h => hx.trans h)
    exact lt_of_le_of_lt (sub_le_sub_right (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right hle hμ.le)) 1) hsmall
  have hyne (x : ℝ) (hx : 0 < x) : recessive ν μ x + η x ≠ 0 := by
    intro he
    have he' : η x = -recessive ν μ x := by linear_combination he
    have heq : ‖η x‖ = ‖recessive ν μ x‖ := by rw [he', norm_neg]
    have hlt := mul_lt_mul_of_pos_left (hEsmall x hx) (norm_recessive_pos (ν := ν) hμ hx)
    rw [mul_one] at hlt
    linarith [hbound x hx]
  have hc : (((Real.sqrt π / Real.sqrt 2 / Real.sqrt μ : ℝ)) : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (div_ne_zero
      (div_ne_zero (Real.sqrt_pos.mpr Real.pi_pos).ne'
        (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne')
      (Real.sqrt_pos.mpr hμ).ne')
  have hr : Tendsto (fun x : ℝ => f x / (recessive ν μ x + η x)) atTop (𝓝 1) := by
    have hh := hfn.div hyn hc
    rw [div_self hc] at hh
    refine hh.congr' (Eventually.of_forall fun x => ?_)
    simp only [Pi.div_apply]
    exact mul_div_mul_left _ _ (exp_ne_zero _)
  have heq := LiouvilleGreen.eqOn_of_tendsto_zero_of_tendsto_div_one
    (fun x hx => (hη x hx).1) (fun x hx => (hη x hx).2.1) hf hf'
    (by simpa using (tendsto_recessive_zero ν hμ).add hη0)
    (by simpa using (tendsto_recessiveDerivative_zero ν hμ).add hη'0)
    hf0 hf'0 hyne hr
  rw [heq hx]
  change ‖(recessive ν μ x + η x) / recessive ν μ x - 1‖ ≤ E x
  have hR := (norm_recessive_pos (ν := ν) hμ hx).ne'
  have hR' : recessive ν μ x ≠ 0 := norm_ne_zero_iff.mp hR
  rw [show (recessive ν μ x + η x) / recessive ν μ x - 1 = η x / recessive ν μ x by
    field_simp [hR']; ring, norm_div]
  exact (div_le_iff₀ (norm_recessive_pos (ν := ν) hμ hx)).mpr (by
    simpa only [mul_comm] using hbound x hx)

end DLMF.Bessel.ModifiedComparison
