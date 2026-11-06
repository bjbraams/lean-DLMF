/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicContinuation
public import DLMF.Gamma.Polygamma
public import DLMF.IncompleteGamma.SpecialValues
public import DLMF.ExpIntegrals.AnalyticProperties

/-!
# The integer base of Lerch's logarithmic expansion

At order one the ray integral is the complementary exponential integral `Ein` minus
its principal logarithm and Euler constant. Removing the logarithmic singularity gives
a holomorphic function on `|Im w| < 2π` that vanishes at zero. Its derivative is the
order-zero regularization, providing the base of the positive integer recurrence.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory DLMF.Confluent DLMF.Hypergeometric
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- The holomorphic order-one logarithmic remainder, normalized to vanish at zero. -/
def integerBase (a w : ℂ) : ℂ :=
  exp (a * w) * (a⁻¹ / 2 + 2 * ∫ x in Ioi (0 : ℝ), LerchHermite.kernel 1 a w x) +
    expIntegralEin (-a * w) - log a + digamma a

/-- On negative real logarithms the integer base is Lerch's function with its logarithmic
order-one singularity removed. -/
theorem integerBase_eq_of_real {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : r < 0) :
    integerBase a r = exp (a * r) * lerchPhi (exp (r : ℂ)) 1 a -
      (digamma 1 - digamma a - log (-r : ℂ)) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hc : 0 < -r := neg_pos.mpr hr
  have hc0 : (-r : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hRay := exp_mul_integral_rayKernel_eq_upperIncompleteGamma ha 1 hr
  simp only [sub_self, cpow_zero, one_mul, upperIncompleteGamma_zero_E1] at hRay
  have hLog : log ((-r : ℂ) * a) = log (-r : ℂ) + log a := by
    simpa only [ofReal_neg, ofReal_log hc.le] using log_ofReal_mul hc ha0
  rw [expIntE1_eq_Ein_complex (mul_ne_zero hc0 ha0), hLog,
    show (-r : ℂ) * a = -a * (r : ℂ) by ring] at hRay
  rw [integerBase, LerchHermite.lerchPhi_exp_eq_of_real ha hr 1, digamma_one]
  simp only [cpow_neg_one]
  linear_combination -hRay

/-- The Binet correction as a Laplace integral on the right half-plane. -/
private def binetLaplace (a : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), exp (-(a * t)) * (DLMF.Gamma.binetBeta t : ℂ)

/-- The exponential majorant makes the Binet Laplace integral holomorphic in its parameter. -/
private lemma differentiableOn_binetLaplace :
    DifferentiableOn ℂ binetLaplace {a : ℂ | 0 < a.re} := by
  refine differentiableOn_integral_Ioi_of_locally_dominated
    (isOpen_lt continuous_const continuous_re) 0 ?_ ?_ ?_
  · intro a _
    exact (((by fun_prop : Continuous fun t : ℝ => exp (-(a * t))).continuousOn).mul
      (continuous_ofReal.comp_continuousOn DLMF.Gamma.continuousOn_binetBeta)).aestronglyMeasurable
        measurableSet_Ioi
  · exact Eventually.of_forall fun t =>
      (by fun_prop : Differentiable ℂ (fun a : ℂ => exp (-(a * t)) *
        (DLMF.Gamma.binetBeta t : ℂ))).differentiableOn
  · intro a ha
    change 0 < a.re at ha
    let δ := a.re / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let g := fun t : ℝ => (1 / 2 : ℝ) * Real.exp (-δ * t)
    have hg : IntegrableOn g (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).const_mul (1 / 2 : ℝ)
    refine ⟨Metric.ball a δ, Metric.ball_mem_nhds a hδ, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht u hu
    have hdist : ‖u - a‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hre : δ ≤ u.re := by
      have habs := abs_re_le_norm (u - a)
      rw [sub_re] at habs
      have hneg := neg_le_abs (u.re - a.re)
      dsimp [δ] at *
      linarith
    have hExp : Real.exp (-u.re * t) ≤ Real.exp (-δ * t) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.le])
    simp only [norm_mul, norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (DLMF.Gamma.binetBeta_nonneg ht)]
    have hLe := mul_le_mul hExp (DLMF.Gamma.binetBeta_le_half ht)
      (DLMF.Gamma.binetBeta_nonneg ht) (by positivity)
    simpa only [g, neg_mul, mul_neg, mul_comm] using hLe

/-- The real Binet formula identifies the Laplace correction on the positive axis. -/
private lemma binetLaplace_eq_of_real {x : ℝ} (hx : 0 < x) :
    binetLaplace x = log (x : ℂ) - (x : ℂ)⁻¹ / 2 - digamma x := by
  have heq : (fun t : ℝ => exp (-((x : ℂ) * t)) * (DLMF.Gamma.binetBeta t : ℂ)) =
      fun t => ((Real.exp (-x * t) * DLMF.Gamma.binetBeta t : ℝ) : ℂ) := by
    funext t
    push_cast
    simp only [neg_mul]
  rw [binetLaplace, heq, integral_complex_ofReal, DLMF.Gamma.digamma_ofReal hx,
    ← ofReal_log hx.le]
  have H := congrArg (fun y : ℝ => (y : ℂ))
    (DLMF.Gamma.digamma_eq_log_sub_binetBeta hx)
  push_cast at H
  have hfrac : 1 / (2 * (x : ℂ)) = (x : ℂ)⁻¹ / 2 := by
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  rw [hfrac] at H
  linear_combination H

/-- Analytic continuation of real Binet to the right half-plane. -/
private lemma binetLaplace_eq {a : ℂ} (ha : 0 < a.re) :
    binetLaplace a = log a - a⁻¹ / 2 - digamma a := by
  have hU : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const continuous_re
  have hf := differentiableOn_binetLaplace.analyticOnNhd hU
  have hdiff : DifferentiableOn ℂ (fun v : ℂ => log v - v⁻¹ / 2 - digamma v)
      {v : ℂ | 0 < v.re} := by
    intro v hv
    change 0 < v.re at hv
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv
    have hnat : ∀ n : ℕ, v ≠ -(n : ℂ) := by
      intro n hn
      have H := congrArg re hn
      simp only [neg_re, natCast_re] at H
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (((differentiableAt_log (Or.inl hv)).sub
      ((differentiableAt_inv hv0).div_const 2)).sub
        (DLMF.Gamma.analyticAt_digamma hnat).differentiableAt).differentiableWithinAt
  refine hf.eqOn_of_preconnected_of_frequently_eq (hdiff.analyticOnNhd hU)
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (z₀ := 1) (by norm_num) ?_ ha
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1,
      binetLaplace x = log (x : ℂ) - (x : ℂ)⁻¹ / 2 - digamma x := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with x hx
    exact binetLaplace_eq_of_real hx
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] (1 : ℂ)) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by simpa using hx
  exact ht.frequently hev.frequently

/-- Binet's digamma formula is the zero-argument value of the order-one Hermite correction.
-/
theorem integral_kernel_one_zero_eq_digamma {a : ℂ} (ha : 0 < a.re) :
    a⁻¹ / 2 + 2 * (∫ x in Ioi (0 : ℝ), LerchHermite.kernel 1 a 0 x) =
      log a - digamma a := by
  have H := HermiteIntegral.gamma_mul_integral_kernel (s := 1) ha (by norm_num)
  simp only [Gamma_one, one_mul, sub_self, cpow_zero] at H
  have hker : (fun x : ℝ => LerchHermite.kernel 1 a 0 x) = HermiteIntegral.kernel 1 a := by
    funext x
    simp only [LerchHermite.kernel, HermiteIntegral.kernel, mul_zero, sub_zero]
  rw [← hker] at H
  change (∫ x in Ioi (0 : ℝ), LerchHermite.kernel 1 a 0 x) = binetLaplace a / 2 at H
  have hL := binetLaplace_eq ha
  linear_combination 2 * H + hL

/-- The order-one regularization is normalized to zero at the logarithmic origin. -/
theorem integerBase_zero {a : ℂ} (ha : 0 < a.re) : integerBase a 0 = 0 := by
  rw [integerBase, mul_zero, exp_zero, one_mul, integral_kernel_one_zero_eq_digamma ha]
  simp only [mul_zero]
  have hEin : expIntegralEin 0 = 0 := by simp [expIntegralEin]
  rw [hEin]
  ring

/-- The zero-order endpoint is the removable exponential difference quotient. -/
private lemma mul_endpoint_zero_order {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ 0) :
    w * endpoint 0 a w = exp (a * w) - 1 := by
  have hn : ∀ n : ℕ, (1 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have H := congrArg re h
    simp only [one_re, neg_re, natCast_re] at H
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have H := lowerIncompleteGamma_nat_succ_expPartialSum 0
    (z := -a * w) (mul_ne_zero (neg_ne_zero.mpr ha) hw)
  simp only [Nat.cast_zero, zero_add] at H
  rw [lowerIncompleteGamma_eq_regularized hn] at H
  norm_num only [Gamma_one, cpow_one, one_mul, Nat.factorial_zero, Nat.cast_one,
    show (1 : ℂ) + 1 = 2 by norm_num, Elementary.expPartialSum,
    Finset.range_one, Finset.sum_singleton, pow_zero, div_one, mul_one] at H
  simp only [neg_mul, neg_neg] at H
  simp only [endpoint, sub_zero, cpow_one, Gamma_one, mul_one]
  linear_combination -H

/-- The entire complementary exponential integral has unit derivative at the origin. -/
private lemma hasDerivAt_Ein_zero : HasDerivAt expIntegralEin 1 0 := by
  let F := fun z : ℂ => 1 - exp (-z)
  have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
  have hF0 : F 0 = 0 := by simp [F]
  have heq : expIntegralEin = DLMF.Core.primitive (dslope F 0) := by
    funext z
    rw [expIntegralEin_segment_integral, DLMF.Core.primitive_dslope_zero hF0]
  have hD : HasDerivAt F 1 0 := by
    have H := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub
      (((hasDerivAt_id (0 : ℂ)).neg).cexp)
    convert H using 1 <;> (try funext z) <;>
      simp only [F, Pi.sub_apply, Pi.neg_apply, id_eq, neg_zero, exp_zero,
        mul_neg, mul_one, zero_sub, neg_neg]
  have H := DLMF.Core.hasDerivAt_primitive (differentiable_dslope_entire hF 0) 0
  rw [← heq, dslope_same, hD.deriv] at H
  exact H

/-- The derivative of the entire exponential-integral correction is the negative endpoint,
including its removable value at zero. -/
private lemma hasDerivAt_Ein_neg_mul {a w : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun v : ℂ => expIntegralEin (-a * v)) (-endpoint 0 a w) w := by
  by_cases hw : w = 0
  · subst w
    have H := hasDerivAt_Ein_zero.comp_of_eq (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_mul (-a)) (by simp)
    have hs : ∀ n : ℕ, (0 : ℂ) ≠ (n : ℂ) + 1 := by
      intro n h
      have H := congrArg re h
      simp only [zero_re, add_re, natCast_re, one_re] at H
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [endpoint_zero hs]
    simpa only [sub_zero, cpow_one, div_one, one_mul, mul_one,
      Function.comp_def, id_eq] using H
  · have H := (hasDerivAt_expIntegralEin_complex
      (mul_ne_zero (neg_ne_zero.mpr ha) hw)).comp w ((hasDerivAt_id w).const_mul (-a))
    have he : endpoint 0 a w = (exp (a * w) - 1) / w :=
      (eq_div_iff hw).mpr (by linear_combination mul_endpoint_zero_order ha hw)
    convert H using 1
    · funext v
      rfl
    · rw [he]
      simp only [neg_mul, neg_neg, mul_one]
      field_simp
      ring

/-- Differentiation of the integer base lowers its order to the holomorphic zero-order
regularization throughout the Hermite strip. -/
theorem hasDerivAt_integerBase {a w : ℂ} (ha : 0 < a.re) (hw : |w.im| < 2 * π) :
    HasDerivAt (integerBase a) (regularized 0 a w) w := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hI := hasDerivAt_integral_kernel ha hw (1 : ℂ)
  simp only [sub_self] at hI
  have H := (((((hasDerivAt_id w).const_mul a).cexp).mul
    ((hI.const_mul 2).const_add (a⁻¹ / 2))).add
      (hasDerivAt_Ein_neg_mul (w := w) ha0)).sub_const (log a) |>.add_const (digamma a)
  simp only [id_eq] at H
  convert H using 1
  · rfl
  · rw [regularized]
    simp only [neg_zero, cpow_zero]
    field_simp
    ring

/-- The integer base is holomorphic on the open logarithmic strip. -/
theorem analyticOnNhd_integerBase {a : ℂ} (ha : 0 < a.re) :
    AnalyticOnNhd ℂ (integerBase a) {w : ℂ | |w.im| < 2 * π} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
  intro w hw
  exact (hasDerivAt_integerBase ha hw).differentiableAt.differentiableWithinAt

/-- The integer base agrees with Lerch's function on the principal logarithmic slit strip.
-/
theorem integerBase_eq {a w : ℂ} (ha : 0 < a.re) (hw : |w.im| < 2 * π)
    (hw' : -w ∈ slitPlane) :
    integerBase a w = exp (a * w) * lerchPhi (exp w) 1 a -
      (digamma 1 - digamma a - log (-w)) := by
  let S : Set ℂ := {v : ℂ | -(2 * π) < v.im ∧ v.im < 2 * π}
  let U : Set ℂ := S ∩ (-slitPlane)
  have hS : IsOpen S :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hU : IsOpen U := hS.inter isOpen_slitPlane.neg
  have hSc : Convex ℝ S :=
    (convex_halfSpace_im_gt (-(2 * π))).inter (convex_halfSpace_im_lt (2 * π))
  have hm : (-1 : ℂ) ∈ S := by
    change -(2 * π) < (-1 : ℂ).im ∧ (-1 : ℂ).im < 2 * π
    simp only [neg_im, one_im, neg_zero]
    constructor <;> nlinarith [Real.pi_pos]
  have hmU : (-1 : ℂ) ∈ U := ⟨hm, by simp⟩
  have hstar : StarConvex ℝ (-1 : ℂ) U :=
    (hSc.starConvex hm).inter starConvex_one_slitPlane.neg
  have hf : AnalyticOnNhd ℂ (integerBase a) U :=
    (analyticOnNhd_integerBase ha).mono fun v hv => abs_lt.mpr hv.1
  have hg : DifferentiableOn ℂ (fun v => exp (a * v) * lerchPhi (exp v) 1 a -
      (digamma 1 - digamma a - log (-v))) U := by
    intro v hv
    have hv' : -v ∈ slitPlane := by simpa using hv.2
    have hPhi := (analyticOnNhd_lerchPhi (lerchParamAdmissible_of_re_pos ha 1) _
      (exp_mem_slitOne (abs_lt.mpr hv.1) hv')).differentiableAt
    have hLog := (differentiableAt_log hv').comp v differentiableAt_id.neg
    exact (((by fun_prop : DifferentiableAt ℂ (fun t : ℂ => exp (a * t)) v).mul
      (hPhi.comp v differentiableAt_id.cexp)).sub
        ((differentiableAt_const (digamma 1 - digamma a)).sub hLog)).differentiableWithinAt
  refine hf.eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    (hstar.isPathConnected hmU).isConnected.isPreconnected hmU ?_ ⟨abs_lt.mp hw, by simpa⟩
  have hev : ∀ᶠ r : ℝ in 𝓝[≠] (-1),
      integerBase a r = exp (a * r) * lerchPhi (exp (r : ℂ)) 1 a -
        (digamma 1 - digamma a - log (-(r : ℂ))) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))]
      with r hr
    exact integerBase_eq_of_real ha hr
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (-1)) (𝓝[≠] ((-1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun r hr => Complex.ofReal_injective.ne hr)
  simpa only [ofReal_neg, ofReal_one] using
    (ht.frequently (p := fun v : ℂ => integerBase a v =
      exp (a * v) * lerchPhi (exp v) 1 a -
        (digamma 1 - digamma a - log (-v))) hev.frequently)

end DLMF.Zeta.LerchLogarithmic
