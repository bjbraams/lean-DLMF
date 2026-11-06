/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.LerchProperties
public import DLMF.Gamma.MellinBarnes
public import DLMFMathlib.Analysis.Fourier.HorizontalStrip
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.RightHalfPlane
public import DLMFMathlib.Analysis.Complex.IdentityTheoremStrip

/-!
# Mellin–Barnes representation of Lerch's transcendent

The contour in DLMF 25.14.8 lies between `max(-Re a, -1)` and zero. The reflected Gamma
product decays at rate `π` along that line. Polynomial bounds for the remaining principal
power give absolute convergence and holomorphy in the order and logarithmic argument.
Mellin inversion first gives the formula in a half-plane of orders; analytic continuation
then covers every complex order and the principal slit plane of arguments.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology

namespace DLMF.Zeta.LerchBarnes

/-- The vertical Barnes kernel without its argument-dependent exponential factor. -/
def kernel (s a : ℂ) (σ y : ℝ) : ℂ :=
  Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I)) *
    (a + ((σ : ℂ) + y * I)) ^ (-s)

/-- The normalized Barnes integral as a function of the logarithm of its argument. -/
def value (s a : ℂ) (σ : ℝ) (w : ℂ) : ℂ :=
  1 / (2 * π) * ∫ y : ℝ, kernel s a σ y * exp (((σ : ℂ) + I * y) * w)

/-- The Barnes kernel is continuous along every admissible line. -/
theorem continuous_kernel {a : ℂ} {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0)
    (haσ : 0 < a.re + σ) (s : ℂ) : Continuous (kernel s a σ) := by
  have hg1 : Continuous (fun y : ℝ => Gamma (1 + ((σ : ℂ) + y * I))) :=
    continuous_iff_continuousAt.mpr fun y =>
      (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  have hg2 : Continuous (fun y : ℝ => Gamma (-((σ : ℂ) + y * I))) :=
    continuous_iff_continuousAt.mpr fun y =>
      (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  have hp : Continuous (fun y : ℝ => (a + ((σ : ℂ) + y * I)) ^ (-s)) :=
    Continuous.cpow (by fun_prop) continuous_const (fun y =>
      Or.inl (by simpa using haσ))
  exact (hg1.mul hg2).mul hp

/-- Bounded orders give a common polynomial times exponential bound for the kernel. -/
theorem exists_bound_kernel {a : ℂ} {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0)
    (haσ : 0 < a.re + σ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ s : ℂ, ‖s‖ ≤ M → ∀ y : ℝ,
      ‖kernel s a σ y‖ ≤ C * (1 + |y|) ^ N * Real.exp (-(π * |y|)) := by
  obtain ⟨Cg, hCg, hg⟩ := DLMF.Gamma.exists_norm_Gamma_one_add_mul_Gamma_neg_le hσ0 hσ1
  obtain ⟨Cp, hCp, N, hp⟩ := exists_bound_cpow_add_mul_I
    (a := a + (σ : ℂ)) (by simpa using haσ) hM
  refine ⟨Cg * Cp, mul_pos hCg hCp, N, fun s hs y => ?_⟩
  have hpow := hp (-s) (by simpa using hs) y
  have he : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
  rw [kernel, norm_mul, he]
  calc
    _ ≤ (Cg * Real.exp (-(π * |y|))) * (Cp * (1 + |y|) ^ N) := by
      exact mul_le_mul (hg y) hpow (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The Barnes kernel is entire in its order along an admissible line. -/
theorem differentiable_kernel_order {a : ℂ} {σ : ℝ} (haσ : 0 < a.re + σ) (y : ℝ) :
    Differentiable ℂ (fun s => kernel s a σ y) := by
  have hn : a + ((σ : ℂ) + y * I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

/-- For fixed order the integral is holomorphic in the strip of logarithmic arguments. -/
theorem differentiableOn_value {a : ℂ} {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0)
    (haσ : 0 < a.re + σ) (s : ℂ) :
    DifferentiableOn ℂ (value s a σ) {w : ℂ | |w.im| < π} := by
  obtain ⟨C, _, N, hb⟩ := exists_bound_kernel hσ0 hσ1 haσ (norm_nonneg s)
  exact (differentiableOn_integral_mul_exp_of_exp_decay
    (continuous_kernel hσ0 hσ1 haσ s).aestronglyMeasurable
    (fun y => hb s le_rfl y) σ).const_mul _

/-- For each logarithmic argument in the open strip, the integral is entire in its order. -/
theorem differentiable_value_order {a w : ℂ} {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0)
    (haσ : 0 < a.re + σ) (hw : |w.im| < π) :
    Differentiable ℂ (fun s => value s a σ w) := by
  unfold value
  apply Differentiable.const_mul
  rw [← differentiableOn_univ]
  refine differentiableOn_integral_of_locally_dominated isOpen_univ ?_ ?_ ?_
  · intro s _
    exact (continuous_kernel hσ0 hσ1 haσ s).aestronglyMeasurable.mul
      (Continuous.aestronglyMeasurable (by fun_prop))
  · exact Eventually.of_forall fun y =>
      ((differentiable_kernel_order haσ y).mul_const _).differentiableOn
  · intro s _
    obtain ⟨C, hC, N, hb⟩ := exists_bound_kernel hσ0 hσ1 haσ
      (M := ‖s‖ + 1) (by positivity)
    refine ⟨Metric.ball s 1, Metric.ball_mem_nhds s one_pos,
      fun y => C * Real.exp (|σ| * |w.re|) *
        ((1 + |y|) ^ N * Real.exp (-((π - |w.im|) * |y|))),
      (Real.integrable_one_add_abs_pow_mul_exp_neg (sub_pos.mpr hw) N).const_mul _, ?_⟩
    refine Eventually.of_forall fun y t ht => ?_
    have ht' : ‖t‖ ≤ ‖s‖ + 1 := by
      have hdist : ‖t - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht
      have htri := norm_add_le (t - s) s
      rw [sub_add_cancel] at htri
      linarith
    exact norm_mul_exp_le_of_exp_decay hC.le (fun y => hb t ht' y) σ le_rfl le_rfl y

/-- The Gamma–Laplace kernel used to interchange Mellin inversion and the Lerch integral. -/
def doubleKernel (s a : ℂ) (σ r x y : ℝ) : ℂ :=
  (Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I))) *
    exp (((σ : ℂ) + y * I) * (r - x)) *
    ((x : ℂ) ^ (s - 1) * exp (-(a * x)))

/-- The two integrations in the initial half-plane are absolutely convergent. -/
theorem integrable_doubleKernel {s a : ℂ} {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0)
    (haσ : 0 < a.re + σ) (hs : 0 < s.re) (r : ℝ) :
    Integrable (Function.uncurry (doubleKernel s a σ r))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨C, hC, hG⟩ := DLMF.Gamma.exists_norm_Gamma_one_add_mul_Gamma_neg_le hσ0 hσ1
  have hx := integrableOn_rpow_mul_exp_neg (σ := s.re) hs haσ
  have hy := TauCeti.integrable_exp_neg_mul_abs Real.pi_pos
  have hGamma : Continuous (fun y : ℝ =>
      Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I))) := by
    refine Continuous.mul ?_ ?_
    · exact continuous_iff_continuousAt.mpr fun y =>
        (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact continuous_iff_continuousAt.mpr fun y =>
        (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  have hGm := hGamma.measurable
  refine ((hx.mul_prod hy).const_mul (C * Real.exp (σ * r))).mono'
    (Measurable.aestronglyMeasurable (by
      change Measurable (fun p : ℝ × ℝ => doubleKernel s a σ r p.1 p.2)
      unfold doubleKernel
      fun_prop)) ?_
  have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod volume), 0 < p.1 := by
    have he : ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)) =
        (volume.prod (volume : Measure ℝ)).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
      simpa only [Measure.restrict_univ] using
        (Measure.prod_restrict (μ := volume) (ν := (volume : Measure ℝ))
          (Ioi (0 : ℝ)) (univ : Set ℝ))
    rw [he]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
    exact hp.1
  filter_upwards [hmem] with p hp
  obtain ⟨x, y⟩ := p
  change 0 < x at hp
  change ‖doubleKernel s a σ r x y‖ ≤ _
  rw [doubleKernel, norm_mul, norm_mul,
    norm_mul ((x : ℂ) ^ (s - 1)) (exp (-(a * x))), norm_exp, norm_exp,
    norm_cpow_eq_rpow_re_of_pos hp]
  have he1 : (((σ : ℂ) + y * I) * (r - x)).re = σ * (r - x) := by simp
  have he2 : (-(a * x)).re = -a.re * x := by simp
  rw [he1, he2, sub_re, one_re]
  calc
    _ ≤ (C * Real.exp (-(π * |y|))) * Real.exp (σ * (r - x)) *
        (x ^ (s.re - 1) * Real.exp (-a.re * x)) := by gcongr; exact hG y
    _ = _ := by
      dsimp [Function.uncurry]
      rw [show σ * (r - x) = σ * r + -(σ * x) by ring, Real.exp_add,
        show -((a.re + σ) * x) = -(a.re * x) + -(σ * x) by ring, Real.exp_add]
      ring

/-- Integrating the Laplace variable first recovers the complex power in the Barnes kernel. -/
theorem integral_doubleKernel_first {s a : ℂ} {σ : ℝ} (haσ : 0 < a.re + σ)
    (hs : 0 < s.re) (r y : ℝ) :
    (∫ x in Ioi (0 : ℝ), doubleKernel s a σ r x y) =
      Gamma s * (kernel s a σ y * exp (((σ : ℂ) + I * y) * r)) := by
  have heq : (fun x : ℝ => doubleKernel s a σ r x y) = fun x : ℝ =>
      (Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I)) *
        exp (((σ : ℂ) + y * I) * r)) *
      ((x : ℂ) ^ (s - 1) * exp (-((a + ((σ : ℂ) + y * I)) * x))) := by
    funext x
    dsimp [doubleKernel]
    rw [show ((σ : ℂ) + y * I) * ((r : ℂ) - x) =
      ((σ : ℂ) + y * I) * r + -(((σ : ℂ) + y * I) * x) by ring,
      exp_add, show -((a + ((σ : ℂ) + y * I)) * x) =
      -(a * x) + -(((σ : ℂ) + y * I) * x) by ring, exp_add]
    ring
  rw [heq, integral_const_mul, integral_cpow_mul_cexp_neg_mul_Ioi hs (by simpa using haσ)]
  unfold kernel
  rw [mul_comm I (y : ℂ)]
  ring

/-- Mellin inversion evaluates the Gamma product against a real exponential argument. -/
theorem integral_Gamma_mul_exp {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0) (u : ℝ) :
    (∫ y : ℝ, (Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I))) *
      exp (((σ : ℂ) + y * I) * u)) = (2 * π) / (1 + Real.exp u) := by
  have h := DLMF.Gamma.Gamma_mul_one_add_cpow_neg_barnes (a := 1) hσ1
    (by simp; linarith) (Real.exp_pos u)
  have heq : (fun y : ℝ => Gamma (-((σ : ℂ) + I * y)) * Gamma (1 + σ + I * y) *
      (Real.exp u : ℂ) ^ ((σ : ℂ) + I * y)) =
      fun y : ℝ => (Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I))) *
        exp (((σ : ℂ) + y * I) * u) := by
    funext y
    rw [ofReal_cpow_eq_exp_mul_log (Real.exp_pos u), Real.log_exp]
    simp only [mul_comm I (y : ℂ), add_assoc]
    ring
  simp only [Gamma_one, one_mul, cpow_neg_one, Complex.ofReal_add, Complex.ofReal_one] at h
  rw [heq] at h
  have hP : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  calc
    _ = (2 * π) * (1 / (2 * π) * ∫ y : ℝ,
        (Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I))) *
          exp (((σ : ℂ) + y * I) * u)) := by
      rw [one_div, ← mul_assoc, mul_inv_cancel₀ hP, one_mul]
    _ = (2 * π) * (1 + (Real.exp u : ℂ))⁻¹ := by rw [← h]
    _ = _ := by ring

/-- Integrating the Barnes variable first gives the geometric denominator in Lerch's integral. -/
theorem integral_doubleKernel_second {s a : ℂ} {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0)
    (r x : ℝ) :
    (∫ y : ℝ, doubleKernel s a σ r x y) =
      (2 * π) * ((x : ℂ) ^ (s - 1) * exp (-(a * x)) /
        (1 + (Real.exp (r - x) : ℂ))) := by
  have heq : (fun y : ℝ => doubleKernel s a σ r x y) = fun y : ℝ =>
      ((x : ℂ) ^ (s - 1) * exp (-(a * x))) *
      ((Gamma (1 + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I))) *
        exp (((σ : ℂ) + y * I) * (r - x))) := by
    funext y
    dsimp [doubleKernel]
    ring
  rw [heq, integral_const_mul]
  have hi := integral_Gamma_mul_exp hσ0 hσ1 (r - x)
  simp only [Complex.ofReal_sub] at hi
  rw [hi]
  ring

/-- The Barnes integral is Lerch's integral when the order has positive real part. -/
theorem lerchPhi_neg_exp_eq_value_of_re_pos {s a : ℂ} {σ : ℝ}
    (hσ0 : -1 < σ) (hσ1 : σ < 0) (haσ : 0 < a.re + σ) (hs : 0 < s.re) (r : ℝ) :
    lerchPhi (-exp (r : ℂ)) s a = value s a σ r := by
  have ha : 0 < a.re := by linarith
  have hz : -exp (r : ℂ) ∈ slitOne := Or.inr (by
    simp only [neg_re, exp_ofReal_re]
    linarith [Real.exp_pos r])
  obtain ⟨F, hF⟩ := exists_isLerchContinuation s a
  have hPhi := hF.eq_lerchInt hs ha hz
  rw [← lerchPhi_eq_of_isLerchContinuation hF hz] at hPhi
  have hden (x : ℝ) : 1 - -exp (r : ℂ) * exp (-(x : ℂ)) =
      1 + (Real.exp (r - x) : ℂ) := by
    rw [neg_mul, sub_neg_eq_add, ← exp_add,
      show (r : ℂ) + -(x : ℂ) = ((r - x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hPhi' : lerchPhi (-exp (r : ℂ)) s a = (Gamma s)⁻¹ *
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * exp (-(a * x)) /
        (1 + (Real.exp (r - x) : ℂ)) := by
    rw [hPhi, lerchIntegral]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by rw [hden]
  have hswap := integral_integral_swap (integrable_doubleKernel hσ0 hσ1 haσ hs r)
  change (∫ x in Ioi (0 : ℝ), ∫ y : ℝ, doubleKernel s a σ r x y) =
    ∫ y : ℝ, ∫ x in Ioi (0 : ℝ), doubleKernel s a σ r x y at hswap
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ =>
      integral_doubleKernel_second hσ0 hσ1 r x), integral_const_mul] at hswap
  rw [integral_congr_ae (Eventually.of_forall fun y =>
      integral_doubleKernel_first haσ hs r y), integral_const_mul] at hswap
  rw [hPhi', value]
  have hP : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  have hGamma := Gamma_ne_zero_of_re_pos hs
  apply (mul_left_cancel₀ (mul_ne_zero hP hGamma))
  field_simp [hP, hGamma]
  exact hswap

/-- Analytic continuation in the order gives the Barnes representation on the negative
unit interval, with its argument written exponentially. -/
theorem lerchPhi_neg_exp_eq_value_of_neg {a : ℂ} {σ : ℝ}
    (hσ0 : -1 < σ) (hσ1 : σ < 0) (haσ : 0 < a.re + σ) {r : ℝ} (hr : r < 0) (s : ℂ) :
    lerchPhi (-exp (r : ℂ)) s a = value s a σ r := by
  have ha : 0 < a.re := by linarith
  have hz : ‖-exp (r : ℂ)‖ < 1 := by
    simpa only [norm_neg, norm_exp, ofReal_re] using Real.exp_lt_one_iff.mpr hr
  have hleft := differentiable_lerchPhi_order_of_norm_lt_one ha hz
  have hright := differentiable_value_order hσ0 hσ1 haσ
    (w := (r : ℂ)) (by simpa using Real.pi_pos)
  have hf := hleft.differentiableOn.analyticOnNhd isOpen_univ
  have hg := hright.differentiableOn.analyticOnNhd isOpen_univ
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ
    (z₀ := 1) (mem_univ _) ?_ (mem_univ s)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with t ht
  exact lerchPhi_neg_exp_eq_value_of_re_pos hσ0 hσ1 haσ ht r

/-- Exponentials whose imaginary part stays between `-π` and `π` avoid the negative ray. -/
theorem exp_mem_slitPlane_of_abs_im_lt {w : ℂ} (hw : |w.im| < π) :
    exp w ∈ slitPlane := by
  by_cases him : w.im = 0
  · left
    rw [exp_re, him, Real.cos_zero, mul_one]
    exact Real.exp_pos _
  · right
    rw [exp_im]
    apply mul_ne_zero (Real.exp_ne_zero _)
    intro h
    exact him ((Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp hw).1 (abs_lt.mp hw).2).mp h)

/-- The negated exponential avoids the principal Lerch cut throughout the logarithmic strip. -/
theorem neg_exp_mem_slitOne {w : ℂ} (hw : |w.im| < π) : -exp w ∈ slitOne := by
  rcases exp_mem_slitPlane_of_abs_im_lt hw with h | h
  · right
    simp only [neg_re]
    linarith
  · left
    simpa only [neg_im, neg_ne_zero] using h

/-- The Barnes representation holds throughout the strip of principal logarithmic arguments. -/
theorem lerchPhi_neg_exp_eq_value {a : ℂ} {σ : ℝ}
    (hσ0 : -1 < σ) (hσ1 : σ < 0) (haσ : 0 < a.re + σ) (s : ℂ) {w : ℂ}
    (hw : |w.im| < π) : lerchPhi (-exp w) s a = value s a σ w := by
  have ha : 0 < a.re := by linarith
  refine eqOn_horizontalStrip_of_eq_ofReal_neg Real.pi_pos
    (f := fun w => lerchPhi (-exp w) s a) (g := value s a σ) ?_
    (differentiableOn_value hσ0 hσ1 haσ s) ?_ hw
  · intro v hv
    exact ((analyticOnNhd_lerchPhi (lerchParamAdmissible_of_re_pos ha s) _
      (neg_exp_mem_slitOne hv)).differentiableAt.comp v
      differentiableAt_id.cexp.neg).differentiableWithinAt
  · intro r hr
    exact lerchPhi_neg_exp_eq_value_of_neg hσ0 hσ1 haσ hr s

/-- The Barnes integral with principal powers equals Lerch's transcendent on the slit plane. -/
theorem lerchPhi_neg_eq_integral {z s a : ℂ} (hz : z ∈ slitPlane) {σ : ℝ}
    (hσ0 : -1 < σ) (hσ1 : σ < 0) (haσ : 0 < a.re + σ) :
    lerchPhi (-z) s a = 1 / (2 * π) * ∫ y : ℝ,
      Gamma (1 + (σ + y * I)) * Gamma (-(σ + y * I)) * z ^ (σ + y * I) /
        (a + (σ + y * I)) ^ s := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hw : |(Complex.log z).im| < π := by
    rw [log_im, abs_lt]
    exact ⟨neg_pi_lt_arg z, (arg_le_pi z).lt_of_ne (slitPlane_arg_ne_pi hz)⟩
  have h := lerchPhi_neg_exp_eq_value hσ0 hσ1 haσ s hw
  rw [exp_log hz0] at h
  rw [h, value]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [kernel, cpow_neg, cpow_def_of_ne_zero hz0]
    rw [show ((σ : ℂ) + I * y) * Complex.log z =
      Complex.log z * ((σ : ℂ) + y * I) by ring]
    ring

end DLMF.Zeta.LerchBarnes
