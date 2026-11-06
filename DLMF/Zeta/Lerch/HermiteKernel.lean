/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.LerchProperties
public import DLMF.Gamma.IntegralRepresentations.DigammaAndBinet
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.RightHalfPlane
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.BoseEinstein
public import DLMFMathlib.Analysis.Integral.LaplaceSine

/-!
# The Hermite kernel for Lerch's transcendent

For `Re a > 0`, the kernel in DLMF 25.14.6 is expressed as a difference of principal powers
of `a ± ix`, multiplied by exponential factors in the logarithmic argument. This form makes
its holomorphic dependence on the order and logarithmic argument explicit. Gamma and
Bose–Einstein sine transforms give its integral representation in the initial half-plane.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.Zeta.LerchHermite

/-- The principal-branch Hermite correction kernel for complex order `s`, logarithmic
argument `w`, `Re a > 0` and positive real integration variable. -/
def kernel (s a w : ℂ) (x : ℝ) : ℂ :=
  sin (s * arctan (x / a) - x * w) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) /
    (Real.exp (2 * π * x) - 1 : ℝ)

/-- For `Re a > 0`, the ray kernel with principal powers is integrable
when `Re w < 0`, and also when `Re w = 0` and `Re s > 1`. -/
def rayKernel (s a w : ℂ) (x : ℝ) : ℂ := exp (w * x) * (a + x) ^ (-s)

/-- Principal powers express the Hermite kernel without an arctangent. -/
theorem kernel_eq_cpow {a : ℂ} (ha : 0 < a.re) (s w : ℂ) (x : ℝ) :
    kernel s a w x =
      (exp (-(I * x * w)) * (a - x * I) ^ (-s) -
        exp (I * x * w) * (a + x * I) ^ (-s)) /
        (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := by
  have hsplit : sin (s * arctan (x / a) - x * w) /
      (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) =
      (sin (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)) * cos (x * w) -
      (cos (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)) * sin (x * w) := by
    rw [sin_sub]
    ring
  unfold kernel
  rw [hsplit, sin_mul_arctan_div_cpow ha, cos_mul_arctan_div_cpow ha, sin, cos]
  have hn : exp (-((x : ℂ) * w) * I) = exp (-(I * x * w)) := by congr 1; ring
  have hp : exp (((x : ℂ) * w) * I) = exp (I * x * w) := by congr 1; ring
  rw [hn, hp]
  congr 1
  field_simp
  simp only [I_sq]
  ring

/-- The Hermite kernel is continuous away from its lower endpoint. -/
theorem continuousOn_kernel {a : ℂ} (ha : 0 < a.re) (s w : ℂ) :
    ContinuousOn (kernel s a w) (Ioi 0) := by
  have hp : Continuous (fun x : ℝ => (a + x * I) ^ (-s)) :=
    Continuous.cpow (by fun_prop) continuous_const (fun x => Or.inl (by simpa using ha))
  have hm : Continuous (fun x : ℝ => (a - x * I) ^ (-s)) :=
    Continuous.cpow (by fun_prop) continuous_const (fun x => Or.inl (by simpa using ha))
  have heq : kernel s a w = fun x : ℝ =>
      (exp (-(I * x * w)) * (a - x * I) ^ (-s) -
        exp (I * x * w) * (a + x * I) ^ (-s)) /
        (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := funext (kernel_eq_cpow ha s w)
  rw [heq]
  refine ContinuousOn.div (((Continuous.mul (by fun_prop) hm).sub
    (Continuous.mul (by fun_prop) hp)).div_const (2 * I)).continuousOn (by fun_prop) ?_
  intro x hx
  have hx0 : 0 < x := hx
  exact_mod_cast (sub_pos.mpr (Real.one_lt_exp_iff.mpr
    (by positivity : (0 : ℝ) < 2 * π * x))).ne'

/-- For each real integration variable, the Hermite kernel is entire in the order. -/
theorem differentiable_kernel_order {a : ℂ} (ha : 0 < a.re) (w : ℂ) (x : ℝ) :
    Differentiable ℂ (fun s => kernel s a w x) := by
  have hp : a + x * I ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hm : a - x * I ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have heq : (fun s => kernel s a w x) = fun s =>
      (exp (-(I * x * w)) * (a - x * I) ^ (-s) -
        exp (I * x * w) * (a + x * I) ^ (-s)) /
        (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := funext fun s => kernel_eq_cpow ha s w x
  rw [heq]
  exact ((((differentiable_id.neg.const_cpow (Or.inl hm)).const_mul _).sub
    ((differentiable_id.neg.const_cpow (Or.inl hp)).const_mul _)).div_const _).div_const _

/-- For each real integration variable, the kernel is entire in the logarithmic argument. -/
theorem differentiable_kernel_argument {a : ℂ} (ha : 0 < a.re) (s : ℂ) (x : ℝ) :
    Differentiable ℂ (fun w => kernel s a w x) := by
  have heq : (fun w => kernel s a w x) = fun w =>
      (exp (-(I * x * w)) * (a - x * I) ^ (-s) -
        exp (I * x * w) * (a + x * I) ^ (-s)) /
        (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := funext fun w => kernel_eq_cpow ha s w x
  rw [heq]
  fun_prop

/-- The double sine-transform kernel for a real negative logarithmic argument. -/
def doubleKernel (s a : ℂ) (r t y : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * exp (-(a * t)) * sin (((t : ℂ) - r) * y) /
    (Real.exp (2 * π * y) - 1 : ℝ)

/-- The shifted double sine transform is absolutely convergent in the Gamma half-plane. -/
theorem integrable_doubleKernel {a s : ℂ} (ha : 0 < a.re) (hs : 0 < s.re)
    {r : ℝ} (hr : r < 0) :
    Integrable (Function.uncurry (doubleKernel s a r))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hT1 := integrableOn_rpow_mul_exp_neg_mul (r := s.re) (by linarith) ha
  have hT0 := integrableOn_rpow_mul_exp_neg_mul (r := s.re - 1) (by linarith) ha
  have hT := hT1.add (hT0.const_mul (-r))
  have hY : IntegrableOn (fun y : ℝ => y / (Real.exp (2 * π * y) - 1)) (Ioi 0) := by
    simpa only [pow_zero, mul_one] using
      Real.integrableOn_mul_one_add_pow_div_exp_two_pi_sub_one 0
  refine (hT.mul_prod hY).mono' (Measurable.aestronglyMeasurable (by
    change Measurable (fun p : ℝ × ℝ => doubleKernel s a r p.1 p.2)
    unfold doubleKernel
    fun_prop)) ?_
  have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))), p ∈ Ioi 0 ×ˢ Ioi 0 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  filter_upwards [hmem] with p hp
  obtain ⟨t, y⟩ := p
  have ht : 0 < t := hp.1
  have hy : 0 < y := hp.2
  have hE : 0 < Real.exp (2 * π * y) - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hsin : ‖sin (((t : ℂ) - r) * y)‖ ≤ (t - r) * y := by
    rw [show ((t : ℂ) - r) * y = (((t - r) * y : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_sin, norm_real, Real.norm_eq_abs]
    have h := Real.abs_sin_le_abs (x := (t - r) * y)
    rwa [abs_of_pos (mul_pos (by linarith : 0 < t - r) hy)] at h
  change ‖doubleKernel s a r t y‖ ≤ _
  rw [doubleKernel, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
    norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE,
    show (-(a * t)).re = -a.re * t by simp, sub_re, one_re]
  calc
    _ ≤ t ^ (s.re - 1) * Real.exp (-a.re * t) * ((t - r) * y) /
        (Real.exp (2 * π * y) - 1) := by gcongr
    _ = _ := by
      dsimp [Function.uncurry]
      rw [show s.re = (s.re - 1) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
      ring

/-- The Gamma transform of the shifted sine gives the Hermite kernel. -/
theorem integral_doubleKernel_first {a s : ℂ} (ha : 0 < a.re) (hs : 0 < s.re)
    (r y : ℝ) :
    (∫ t in Ioi (0 : ℝ), doubleKernel s a r t y) = Gamma s * kernel s a r y := by
  let C : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-(a * t))
  have hS := integral_cpow_mul_cexp_neg_mul_mul_sin_Ioi ha hs y
  have hC := integral_cpow_mul_cexp_neg_mul_mul_cos_Ioi ha hs y
  have heq : (fun t : ℝ => doubleKernel s a r t y) = fun t : ℝ =>
      ((C t * sin ((y : ℂ) * t)) * cos ((y : ℂ) * r) -
        (C t * cos ((y : ℂ) * t)) * sin ((y : ℂ) * r)) /
        (Real.exp (2 * π * y) - 1 : ℝ) := by
    funext t
    dsimp [doubleKernel, C]
    rw [show ((t : ℂ) - r) * y = (y : ℂ) * t - y * r by ring, sin_sub]
    ring
  rw [heq, integral_div, integral_sub (hS.1.mul_const _) (hC.1.mul_const _),
    integral_mul_const, integral_mul_const]
  change ((_ * _) - (_ * _)) / _ = _
  rw [show (∫ t in Ioi (0 : ℝ), C t * sin ((y : ℂ) * t)) =
      Gamma s * sin (s * arctan (y / a)) / (a ^ 2 + (y : ℂ) ^ 2) ^ (s / 2) from hS.2,
    show (∫ t in Ioi (0 : ℝ), C t * cos ((y : ℂ) * t)) =
      Gamma s * cos (s * arctan (y / a)) / (a ^ 2 + (y : ℂ) ^ 2) ^ (s / 2) from hC.2,
    kernel, sin_sub]
  ring

/-- The Bose–Einstein sine transform gives Binet's regularized kernel. -/
theorem integral_doubleKernel_second {a s : ℂ} {r : ℝ} (hr : r < 0) {t : ℝ} (ht : 0 < t) :
    (∫ y in Ioi (0 : ℝ), doubleKernel s a r t y) =
      ((t : ℂ) ^ (s - 1) * exp (-(a * t))) * (DLMF.Gamma.binetBeta (t - r) : ℂ) / 2 := by
  have hu : 0 < t - r := by linarith
  have hBose : (∫ y in Ioi (0 : ℝ), Real.sin ((t - r) * y) /
      (Real.exp (2 * π * y) - 1)) = DLMF.Gamma.binetBeta (t - r) / 2 := by
    have h := (Real.integral_sin_div_exp_two_pi_sub_one hu).2
    rw [DLMF.Gamma.binetBeta]
    linarith
  have heq : (fun y : ℝ => doubleKernel s a r t y) = fun y : ℝ =>
      ((t : ℂ) ^ (s - 1) * exp (-(a * t))) *
      ((Real.sin ((t - r) * y) / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
    funext y
    dsimp [doubleKernel]
    rw [show ((t : ℂ) - r) * y = (((t - r) * y : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_sin, ofReal_div]
    ring
  rw [heq, integral_const_mul, integral_complex_ofReal, hBose, ofReal_div, ofReal_ofNat]
  ring

/-- Interchanging the two sine transforms expresses the correction integral in Binet form. -/
theorem gamma_mul_integral_kernel_of_real {a s : ℂ} (ha : 0 < a.re) (hs : 0 < s.re)
    {r : ℝ} (hr : r < 0) :
    Gamma s * (∫ y in Ioi (0 : ℝ), kernel s a r y) =
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(a * t)) *
        (DLMF.Gamma.binetBeta (t - r) : ℂ)) / 2 := by
  have h := integral_integral_swap (integrable_doubleKernel ha hs hr)
  change (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), doubleKernel s a r t y) =
    ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), doubleKernel s a r t y at h
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => integral_doubleKernel_second hr ht),
    integral_div, setIntegral_congr_fun measurableSet_Ioi (fun y _ =>
      integral_doubleKernel_first ha hs r y), integral_const_mul] at h
  exact h.symm

/-- A second Gamma–Laplace interchange evaluates the ray term for a negative real
logarithmic argument. -/
theorem gamma_mul_integral_rayKernel_of_real {a s : ℂ} (ha : 0 < a.re) (hs : 0 < s.re)
    {r : ℝ} (hr : r < 0) :
    Gamma s * (∫ x in Ioi (0 : ℝ), rayKernel s a r x) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(a * t)) / (t - r) := by
  let F : ℝ → ℝ → ℂ := fun t x =>
    ((t : ℂ) ^ (s - 1) * exp (-(a * t))) * exp (((r : ℂ) - t) * x)
  have hT := integrableOn_rpow_mul_exp_neg_mul (r := s.re - 1) (by linarith) ha
  have hX := integrableOn_exp_mul_Ioi hr 0
  have hF : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (hT.mul_prod hX).mono' (Measurable.aestronglyMeasurable (by
      change Measurable (fun p : ℝ × ℝ => F p.1 p.2)
      dsimp [F]
      fun_prop)) ?_
    have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))), p ∈ Ioi 0 ×ˢ Ioi 0 := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hmem] with p hp
    obtain ⟨t, x⟩ := p
    have ht : 0 < t := hp.1
    have hx : 0 < x := hp.2
    change ‖F t x‖ ≤ _
    dsimp only [F]
    rw [norm_mul, norm_mul, norm_exp, norm_exp, norm_cpow_eq_rpow_re_of_pos ht,
      show (-(a * t)).re = -a.re * t by simp,
      show (((r : ℂ) - t) * x).re = (r - t) * x by simp, sub_re, one_re]
    simp only [neg_mul]
    change t ^ (s.re - 1) * Real.exp (-(a.re * t)) * Real.exp ((r - t) * x) ≤
      (t ^ (s.re - 1) * Real.exp (-(a.re * t))) * Real.exp (r * x)
    gcongr
    nlinarith
  have hfirst (x : ℝ) (hx : x ∈ Ioi 0) :
      (∫ t in Ioi (0 : ℝ), F t x) = Gamma s * rayKernel s a r x := by
    have heq : (fun t : ℝ => F t x) = fun t : ℝ => exp ((r : ℂ) * x) *
        ((t : ℂ) ^ (s - 1) * exp (-((a + x) * t))) := by
      funext t
      dsimp [F]
      rw [show ((r : ℂ) - t) * x = (r : ℂ) * x + -((x : ℂ) * t) by ring,
        exp_add, show -((a + x) * t) = -(a * t) + -((x : ℂ) * t) by ring, exp_add]
      ring
    rw [heq, integral_const_mul, integral_cpow_mul_cexp_neg_mul_Ioi hs (by
      simp only [add_re, ofReal_re]
      have hx0 : 0 < x := hx
      linarith), rayKernel]
    ring
  have hsecond (t : ℝ) (ht : t ∈ Ioi 0) :
      (∫ x in Ioi (0 : ℝ), F t x) =
        (t : ℂ) ^ (s - 1) * exp (-(a * t)) / (t - r) := by
    have ht0 : 0 < t := ht
    have hu : 0 < t - r := by linarith
    have hI : (∫ x in Ioi (0 : ℝ), exp (((r : ℂ) - t) * x)) = 1 / (t - r : ℂ) := by
      have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := 1) (z := (t - r : ℝ))
        (by norm_num) (by simpa using hu)
      simp only [sub_self, cpow_zero, one_mul, Gamma_one, cpow_neg_one] at h
      convert h using 1
      · congr 1
        funext x
        congr 1
        push_cast
        ring
      · push_cast
        simp only [one_div]
    dsimp only [F]
    rw [integral_const_mul, hI]
    ring
  have h := integral_integral_swap hF
  change (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F t x) =
    ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F t x at h
  rw [setIntegral_congr_fun measurableSet_Ioi hsecond,
    setIntegral_congr_fun measurableSet_Ioi hfirst, integral_const_mul] at h
  exact h.symm

end DLMF.Zeta.LerchHermite
