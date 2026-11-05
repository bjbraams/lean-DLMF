/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz
public import DLMF.Gamma.IntegralRepresentations.DigammaAndBinet
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.BoseEinstein
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.RightHalfPlane
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.Integral.LaplaceSine

/-!
# Hermite's integral for the Hurwitz zeta function

The integral kernel in DLMF 25.11.29 uses principal powers and the principal arctangent.
For `Re a > 0` it is integrable on the positive half-line and its integral is entire in the
order parameter. Polynomial bounds uniform on compact sets of orders justify continuation
from the half-plane of absolute convergence.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.Zeta.HermiteIntegral

/-- The principal-branch kernel in Hermite's formula, for complex order `s`, parameter
`Re a > 0` and real integration variable `x > 0`. -/
def kernel (s a : ℂ) (x : ℝ) : ℂ :=
  sin (s * arctan (x / a)) /
    (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) / (Real.exp (2 * π * x) - 1 : ℝ)

/-- Expressing the kernel in powers makes its entire dependence on the order explicit. -/
theorem kernel_eq_cpow {a : ℂ} (ha : 0 < a.re) (s : ℂ) (x : ℝ) :
    kernel s a x = ((a - x * I) ^ (-s) - (a + x * I) ^ (-s)) /
      (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := by
  rw [kernel, sin_mul_arctan_div_cpow ha]

/-- The integrand is continuous away from the lower endpoint. -/
theorem continuousOn_kernel {a : ℂ} (ha : 0 < a.re) (s : ℂ) :
    ContinuousOn (kernel s a) (Ioi 0) := by
  have hp : Continuous (fun x : ℝ => (a + x * I) ^ (-s)) :=
    Continuous.cpow (by fun_prop) continuous_const (fun x => by
      apply mem_slitPlane_iff.mpr
      left
      simpa using ha)
  have hm : Continuous (fun x : ℝ => (a - x * I) ^ (-s)) :=
    Continuous.cpow (by fun_prop) continuous_const (fun x => by
      apply mem_slitPlane_iff.mpr
      left
      simpa using ha)
  have heq : kernel s a = fun x : ℝ => ((a - x * I) ^ (-s) - (a + x * I) ^ (-s)) /
      (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := funext (kernel_eq_cpow ha s)
  rw [heq]
  refine ContinuousOn.div ((hm.sub hp).div_const (2 * I)).continuousOn (by fun_prop) ?_
  intro x hx
  have hx' : 0 < x := hx
  exact_mod_cast (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity : 0 < 2 * π * x))).ne'

/-- A common integrable bound for Hermite's kernels of bounded order. -/
theorem exists_integrable_bound_kernel {a : ℂ} (ha : 0 < a.re) {M : ℝ} (hM : 0 ≤ M) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ s : ℂ, ‖s‖ ≤ M → ∀ x : ℝ, 0 < x → ‖kernel s a x‖ ≤ g x := by
  obtain ⟨C, hC, N, hb⟩ := exists_bound_sin_mul_arctan_div_cpow ha hM
  refine ⟨fun x => C * (x * (1 + x) ^ N / (Real.exp (2 * π * x) - 1)),
    (Real.integrableOn_mul_one_add_pow_div_exp_two_pi_sub_one N).const_mul C, ?_⟩
  intro s hs x hx
  have hE : 0 < Real.exp (2 * π * x) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  rw [kernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
  have h := div_le_div_of_nonneg_right (hb s hs x hx.le) hE.le
  convert h using 1 <;> ring

/-- Absolute convergence of Hermite's integral for every complex order. -/
theorem integrableOn_kernel {a : ℂ} (ha : 0 < a.re) (s : ℂ) :
    IntegrableOn (kernel s a) (Ioi 0) := by
  obtain ⟨g, hg, hb⟩ := exists_integrable_bound_kernel ha (norm_nonneg s)
  exact hg.mono' ((continuousOn_kernel ha s).aestronglyMeasurable measurableSet_Ioi)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hb s le_rfl x hx)

/-- The integral in Hermite's formula is entire in the order. -/
theorem differentiable_integral_kernel {a : ℂ} (ha : 0 < a.re) :
    Differentiable ℂ (fun s => ∫ x in Ioi (0 : ℝ), kernel s a x) := by
  rw [← differentiableOn_univ]
  refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_univ 0 ?_ ?_ ?_
  · intro s _
    exact (continuousOn_kernel ha s).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp0 : a + x * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hm0 : a - x * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have heq : (fun s => kernel s a x) = fun s =>
        ((a - x * I) ^ (-s) - (a + x * I) ^ (-s)) /
          (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := funext fun s => kernel_eq_cpow ha s x
    rw [heq]
    intro s _
    exact (((differentiableAt_id.neg.const_cpow (Or.inl hm0)).sub
      (differentiableAt_id.neg.const_cpow (Or.inl hp0))).div_const (2 * I)).div_const
        ((Real.exp (2 * π * x) - 1 : ℝ) : ℂ) |>.differentiableWithinAt
  · intro s _
    obtain ⟨g, hg, hb⟩ := exists_integrable_bound_kernel ha
      (M := ‖s‖ + 1) (by positivity)
    refine ⟨Metric.ball s 1, Metric.ball_mem_nhds s one_pos, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have ht' : ‖t‖ ≤ ‖s‖ + 1 := by
      have hdist : ‖t - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht
      have htri := norm_add_le (t - s) s
      rw [sub_add_cancel] at htri
      linarith
    exact hb t ht' x hx

/-- The double integral behind Hermite's formula is absolutely convergent in the
Gamma-integral half-plane. -/
theorem integrable_prod_sine {a s : ℂ} (ha : 0 < a.re) (hs : 0 < s.re) :
    Integrable (Function.uncurry fun t x : ℝ =>
      (t : ℂ) ^ (s - 1) * exp (-(a * t)) * sin ((t : ℂ) * x) /
        (Real.exp (2 * π * x) - 1 : ℝ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have ht := integrableOn_rpow_mul_exp_neg_mul (r := s.re) (by linarith) ha
  have hx : IntegrableOn (fun x : ℝ => x / (Real.exp (2 * π * x) - 1)) (Ioi 0) := by
    simpa only [pow_zero, mul_one] using
      Real.integrableOn_mul_one_add_pow_div_exp_two_pi_sub_one 0
  refine (ht.mul_prod hx).mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  have hmem : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ))), p ∈ (Ioi 0 ×ˢ Ioi 0) := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  filter_upwards [hmem] with p hp
  obtain ⟨t, x⟩ := p
  have ht0 : 0 < t := hp.1
  have hx0 : 0 < x := hp.2
  have hE : 0 < Real.exp (2 * π * x) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hsin : ‖sin ((t : ℂ) * x)‖ ≤ t * x := by
    rw [← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
    simpa only [abs_of_pos (mul_pos ht0 hx0)] using Real.abs_sin_le_abs (x := t * x)
  change ‖(t : ℂ) ^ (s - 1) * exp (-(a * t)) * sin ((t : ℂ) * x) /
    (Real.exp (2 * π * x) - 1 : ℝ)‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0,
    norm_exp, sub_re, one_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
  have hre : (-(a * t)).re = -a.re * t := by simp
  rw [hre]
  calc
    _ ≤ t ^ (s.re - 1) * Real.exp (-a.re * t) * (t * x) /
        (Real.exp (2 * π * x) - 1) := by gcongr
    _ = _ := by
      rw [show s.re = (s.re - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
      ring

/-- Interchanging the two Laplace integrals yields the regularized Bose–Einstein kernel. -/
theorem gamma_mul_integral_kernel {a s : ℂ} (ha : 0 < a.re) (hs : 0 < s.re) :
    Gamma s * (∫ x in Ioi (0 : ℝ), kernel s a x) =
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(a * t)) *
        (DLMF.Gamma.binetBeta t : ℂ)) / 2 := by
  let F : ℝ → ℝ → ℂ := fun t x =>
    (t : ℂ) ^ (s - 1) * exp (-(a * t)) * sin ((t : ℂ) * x) /
      (Real.exp (2 * π * x) - 1 : ℝ)
  have hswap := integral_integral_swap (integrable_prod_sine ha hs)
  have hsin (t : ℝ) (ht : t ∈ Ioi 0) :
      (∫ x in Ioi (0 : ℝ), F t x) =
        (t : ℂ) ^ (s - 1) * exp (-(a * t)) * (DLMF.Gamma.binetBeta t : ℂ) / 2 := by
    have heq : F t = fun x : ℝ => ((t : ℂ) ^ (s - 1) * exp (-(a * t))) *
        ((Real.sin (t * x) / (Real.exp (2 * π * x) - 1) : ℝ) : ℂ) := by
      funext x
      dsimp [F]
      rw [ofReal_div, ofReal_sin, ofReal_mul]
      ring
    rw [heq, integral_const_mul, integral_complex_ofReal]
    have h := (Real.integral_sin_div_exp_two_pi_sub_one ht).2
    have hv : (∫ x in Ioi (0 : ℝ), Real.sin (t * x) /
        (Real.exp (2 * π * x) - 1)) = DLMF.Gamma.binetBeta t / 2 := by
      rw [DLMF.Gamma.binetBeta]
      linarith
    rw [hv, ofReal_div, ofReal_ofNat]
    ring
  have hgamma (x : ℝ) (_ : x ∈ Ioi 0) :
      (∫ t in Ioi (0 : ℝ), F t x) = Gamma s * kernel s a x := by
    have heq : (fun t : ℝ => F t x) = fun t : ℝ =>
        (t : ℂ) ^ (s - 1) * exp (-(a * t)) * sin ((x : ℂ) * t) /
          (Real.exp (2 * π * x) - 1 : ℝ) := by
      funext t
      dsimp [F]
      rw [mul_comm (t : ℂ) (x : ℂ)]
    rw [heq, integral_div, (integral_cpow_mul_cexp_neg_mul_mul_sin_Ioi ha hs x).2]
    rw [kernel]
    ring
  change (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F t x) =
      (∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F t x) at hswap
  rw [setIntegral_congr_fun measurableSet_Ioi hsin,
    setIntegral_congr_fun measurableSet_Ioi hgamma, integral_div, integral_const_mul] at hswap
  exact hswap.symm

/-- The Laplace integral for the Hurwitz zeta function in its half-plane of absolute
convergence, with the Gamma factor retained. -/
theorem gamma_mul_hurwitzZetaComplex_eq_integral {a s : ℂ}
    (ha : 0 < a.re) (hs : 1 < s.re) :
    Gamma s * hurwitzZetaComplex s a =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(a * t)) /
        (1 - exp (-(t : ℂ))) := by
  have ha' : ∀ m : ℕ, a ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h := hasSum_lerch_lerchIntegral (s := s) (a := a) (z := 1)
    (by linarith) ha (Or.inr ⟨by simp, hs⟩)
  simp only [one_pow, one_div] at h
  have h' : HasSum (fun n : ℕ => 1 / ((n : ℂ) + a) ^ s)
      ((Gamma s)⁻¹ * lerchIntegral s a 1) :=
    h.congr_fun (fun n => by simp only [one_div, add_comm])
  have hζ := (hasSum_hurwitzZetaComplex hs ha').unique h'
  rw [hζ, ← mul_assoc, mul_inv_cancel₀ (Gamma_ne_zero_of_re_pos (by linarith)), one_mul]
  simp only [lerchIntegral, one_mul]

/-- Hermite's formula first follows in the half-plane of absolute Dirichlet-series
convergence by subtracting elementary Gamma integrals. -/
theorem hurwitzZetaComplex_eq_kernel_of_one_lt_re {a s : ℂ}
    (ha : 0 < a.re) (hs : 1 < s.re) :
    hurwitzZetaComplex s a = a ^ (-s) / 2 + a ^ (1 - s) / (s - 1) +
      2 * ∫ x in Ioi (0 : ℝ), kernel s a x := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hsminus : 0 < (s - 1).re := by simp; linarith
  have hsminus0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  let C : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * exp (-(a * t))
  let B : ℝ → ℂ := fun t => C t * (DLMF.Gamma.binetBeta t : ℂ)
  let P : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 2) * exp (-(a * t))
  have hC : IntegrableOn C (Ioi 0) := Complex.integrableOn_cpow_mul_exp_neg_mul hs0 ha
  have hP : IntegrableOn P (Ioi 0) := by
    convert Complex.integrableOn_cpow_mul_exp_neg_mul hsminus ha using 1
    funext t
    dsimp [P]
    congr 2
    ring
  have hB : IntegrableOn B (Ioi 0) := by
    refine (hC.norm.const_mul (1 / 2 : ℝ)).mono' ?_ ?_
    · have hbeta : AEStronglyMeasurable (fun t : ℝ => (DLMF.Gamma.binetBeta t : ℂ))
          (volume.restrict (Ioi 0)) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          (DLMF.Gamma.continuousOn_binetBeta.aestronglyMeasurable measurableSet_Ioi)
      exact hC.aestronglyMeasurable.mul hbeta
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp [B]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (DLMF.Gamma.binetBeta_nonneg ht)]
      nlinarith [norm_nonneg (C t), DLMF.Gamma.binetBeta_le_half ht]
  have hpoint (t : ℝ) (ht : t ∈ Ioi 0) :
      C t / (1 - exp (-(t : ℂ))) = B t + C t / 2 + P t := by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hE : exp (t : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero, ← ofReal_exp]
      exact_mod_cast (Real.one_lt_exp_iff.mpr ht).ne'
    have hPval : P t = C t / t := by
      dsimp [P, C]
      rw [show s - 2 = (s - 1) - 1 by ring, cpow_sub _ _ ht0, cpow_one]
      ring
    rw [hPval]
    dsimp [B]
    rw [DLMF.Gamma.binetBeta]
    push_cast
    rw [exp_neg]
    field_simp
    ring
  have hW := gamma_mul_hurwitzZetaComplex_eq_integral ha hs
  change Gamma s * hurwitzZetaComplex s a =
    ∫ t in Ioi (0 : ℝ), C t / (1 - exp (-(t : ℂ))) at hW
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint] at hW
  have hBC : IntegrableOn (fun t => B t + C t / 2) (Ioi 0) := hB.add (hC.div_const 2)
  rw [integral_add (f := fun t => B t + C t / 2) (g := P) hBC hP,
    integral_add (f := B) (g := fun t => C t / 2) hB (hC.div_const 2), integral_div] at hW
  have hCval : (∫ t in Ioi (0 : ℝ), C t) = Gamma s * a ^ (-s) :=
    integral_cpow_mul_cexp_neg_mul_Ioi hs0 ha
  have hPval : (∫ t in Ioi (0 : ℝ), P t) = Gamma (s - 1) * a ^ (1 - s) := by
    change (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 2) * exp (-(a * t))) = _
    convert integral_cpow_mul_cexp_neg_mul_Ioi hsminus ha using 1 <;> congr 2 <;> ring
  rw [hCval, hPval] at hW
  have hF := gamma_mul_integral_kernel ha hs0
  change Gamma s * (∫ x in Ioi (0 : ℝ), kernel s a x) = (∫ t in Ioi (0 : ℝ), B t) / 2 at hF
  have hG : Gamma s = (s - 1) * Gamma (s - 1) := by
    simpa only [sub_add_cancel] using Complex.Gamma_add_one (s - 1) hsminus0
  have hA : Gamma (s - 1) * a ^ (1 - s) = Gamma s * (a ^ (1 - s) / (s - 1)) := by
    rw [hG]
    field_simp
  apply mul_left_cancel₀ (Gamma_ne_zero_of_re_pos hs0)
  rw [hA] at hW
  linear_combination hW - 2 * hF

/-- Hermite's formula for every regular order follows by analytic continuation. -/
theorem hurwitzZetaComplex_eq_kernel {a s : ℂ} (ha : 0 < a.re) (hs : s ≠ 1) :
    hurwitzZetaComplex s a = a ^ (-s) / 2 + a ^ (1 - s) / (s - 1) +
      2 * ∫ x in Ioi (0 : ℝ), kernel s a x := by
  let U : Set ℂ := {1}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hUc : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have ha' : ∀ m : ℕ, a ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hleft : DifferentiableOn ℂ (fun z => hurwitzZetaComplex z a) U :=
    fun z hz => (differentiableAt_hurwitzZetaComplex hz ha').differentiableWithinAt
  have hright : DifferentiableOn ℂ (fun z => a ^ (-z) / 2 + a ^ (1 - z) / (z - 1) +
      2 * ∫ x in Ioi (0 : ℝ), kernel z a x) U := by
    intro z hz
    exact ((((differentiableAt_id.neg.const_cpow (Or.inl ha0)).div_const 2).add
      (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl ha0)
        |>.div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hz))).add
      ((differentiable_integral_kernel ha z).const_mul 2)).differentiableWithinAt
  refine (hleft.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hright.analyticOnNhd hU) hUc (z₀ := 2) (by norm_num [U]) ?_ hs
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  exact hurwitzZetaComplex_eq_kernel_of_one_lt_re ha hz

end DLMF.Zeta.HermiteIntegral
