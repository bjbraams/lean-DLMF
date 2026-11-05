/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.Pow.RightHalfPlane
public import DLMFMathlib.Analysis.Integral.LaplaceSine
public import DLMFMathlib.Analysis.Fourier.HyperbolicSecant
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The hyperbolic-cosine kernel in the zeta integral

The integral in DLMF 25.5.10 is entire in the order. Its Laplace representation follows
from the Fourier transform of the hyperbolic secant and Fubini's theorem.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.Zeta.HyperbolicIntegral

/-- The kernel in DLMF 25.5.10 for complex order and real positive argument, using the
principal power of the positive base `1 + x²`. -/
def kernel (s : ℂ) (x : ℝ) : ℂ :=
  cos (s * Real.arctan x) / ((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) /
    (Real.cosh (π * x / 2) : ℝ)

/-- A representation in vertical complex powers. -/
theorem kernel_eq_cpow (s : ℂ) (x : ℝ) :
    kernel s x = ((1 - x * I) ^ (-s) + (1 + x * I) ^ (-s)) / 2 /
      (Real.cosh (π * x / 2) : ℝ) := by
  have h := cos_mul_arctan_div_cpow (a := 1) (by norm_num) x s
  simp only [div_one, one_pow, ← ofReal_arctan] at h
  simpa only [kernel, ofReal_add, ofReal_one, ofReal_pow] using
    congrArg (fun z : ℂ => z / (Real.cosh (π * x / 2) : ℝ)) h

/-- Continuity of the kernel as a function of the integration variable. -/
theorem continuous_kernel (s : ℂ) : Continuous (kernel s) := by
  have hp : Continuous (fun x : ℝ => ((1 : ℂ) + x * I) ^ (-s)) :=
    Continuous.cpow (by fun_prop) continuous_const (fun x => by
      apply mem_slitPlane_iff.mpr; left; simp)
  have hm : Continuous (fun x : ℝ => ((1 : ℂ) - x * I) ^ (-s)) :=
    Continuous.cpow (by fun_prop) continuous_const (fun x => by
      apply mem_slitPlane_iff.mpr; left; simp)
  simp_rw [funext (kernel_eq_cpow s)]
  exact ((hm.add hp).div_const 2).div (by fun_prop)
    (fun x => ofReal_ne_zero.mpr (Real.cosh_pos _).ne')

/-- A common integrable majorant for all orders in a fixed bounded set. -/
theorem exists_integrable_bound_kernel {M : ℝ} (hM : 0 ≤ M) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ s : ℂ, ‖s‖ ≤ M → ∀ x : ℝ, 0 < x → ‖kernel s x‖ ≤ g x := by
  obtain ⟨C, hC, N, hb⟩ := exists_bound_cos_mul_arctan_div_cpow (a := 1) (by norm_num) hM
  refine ⟨fun x => C * ((1 + x) ^ N / Real.cosh (π * x / 2)), ?_, ?_⟩
  · change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
    simpa only [div_mul_eq_mul_div] using
      (Real.integrableOn_one_add_pow_div_cosh (r := π / 2) (by positivity) N).const_mul C
  · intro s hs x hx
    have h := hb s hs x hx.le
    simp only [div_one, one_pow, ← ofReal_arctan] at h
    rw [kernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    have h' := div_le_div_of_nonneg_right h (Real.cosh_pos (π * x / 2)).le
    simpa only [ofReal_add, ofReal_one, ofReal_pow, mul_div_assoc] using h'

/-- Absolute convergence for every complex order. -/
theorem integrableOn_kernel (s : ℂ) : IntegrableOn (kernel s) (Ioi 0) := by
  obtain ⟨g, hg, hb⟩ := exists_integrable_bound_kernel (norm_nonneg s)
  exact hg.mono' ((continuous_kernel s).aestronglyMeasurable)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hb s le_rfl x hx)

/-- The hyperbolic-cosine integral is entire in its order. -/
theorem differentiable_integral_kernel :
    Differentiable ℂ (fun s => ∫ x in Ioi (0 : ℝ), kernel s x) := by
  rw [← differentiableOn_univ]
  refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_univ 0 ?_ ?_ ?_
  · intro s _
    exact (continuous_kernel s).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp0 : (1 : ℂ) + x * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hm0 : (1 : ℂ) - x * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    simp_rw [show (fun s : ℂ => kernel s x) = fun s =>
      ((1 - x * I) ^ (-s) + (1 + x * I) ^ (-s)) / 2 /
        (Real.cosh (π * x / 2) : ℝ) from funext fun s => kernel_eq_cpow s x]
    intro s _
    exact (((differentiableAt_id.neg.const_cpow (Or.inl hm0)).add
      (differentiableAt_id.neg.const_cpow (Or.inl hp0))).div_const 2).div_const
        ((Real.cosh (π * x / 2) : ℝ) : ℂ) |>.differentiableWithinAt
  · intro s _
    obtain ⟨g, hg, hb⟩ := exists_integrable_bound_kernel (M := ‖s‖ + 1) (by positivity)
    refine ⟨Metric.ball s 1, Metric.ball_mem_nhds s one_pos, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have ht' : ‖t‖ ≤ ‖s‖ + 1 := by
      have hdist : ‖t - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht
      have htri := norm_add_le (t - s) s
      rw [sub_add_cancel] at htri
      linarith
    exact hb t ht' x hx

/-- Absolute convergence of the two-variable Laplace kernel. -/
theorem integrable_prod_cosine {s : ℂ} (hs : 0 < s.re) :
    Integrable (Function.uncurry fun t x : ℝ =>
      (t : ℂ) ^ (s - 1) * exp (-(t : ℂ)) * cos ((t : ℂ) * x) /
        (Real.cosh (π * x / 2) : ℝ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have ht := integrableOn_rpow_mul_exp_neg_mul (r := s.re - 1) (by linarith) one_pos
  have hx : IntegrableOn (fun x : ℝ => 1 / Real.cosh (π * x / 2)) (Ioi 0) := by
    simpa only [pow_zero, div_mul_eq_mul_div] using
      Real.integrableOn_one_add_pow_div_cosh (r := π / 2) (by positivity) 0
  refine (ht.mul_prod hx).mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  have hmem : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ))), p ∈ (Ioi 0 ×ˢ Ioi 0) := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  filter_upwards [hmem] with p hp
  obtain ⟨t, x⟩ := p
  have ht0 : 0 < t := hp.1
  have hc : ‖cos ((t : ℂ) * x)‖ ≤ 1 := by
    rw [← ofReal_mul, ← ofReal_cos, norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  change ‖(t : ℂ) ^ (s - 1) * exp (-(t : ℂ)) * cos ((t : ℂ) * x) /
    (Real.cosh (π * x / 2) : ℝ)‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0,
    ← ofReal_neg, norm_exp_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _), sub_re, one_re]
  calc
    _ ≤ t ^ (s.re - 1) * Real.exp (-t) * 1 / Real.cosh (π * x / 2) := by gcongr
    _ = _ := by simp; ring

/-- Fubini's theorem identifies the hyperbolic-cosine integral with a Laplace integral. -/
theorem gamma_mul_integral_kernel {s : ℂ} (hs : 0 < s.re) :
    Gamma s * (∫ x in Ioi (0 : ℝ), kernel s x) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(t : ℂ)) / (Real.cosh t : ℝ) := by
  let F : ℝ → ℝ → ℂ := fun t x =>
    (t : ℂ) ^ (s - 1) * exp (-(t : ℂ)) * cos ((t : ℂ) * x) /
      (Real.cosh (π * x / 2) : ℝ)
  have hswap := integral_integral_swap (integrable_prod_cosine hs)
  have hcos (t : ℝ) : (∫ x in Ioi (0 : ℝ), F t x) =
      (t : ℂ) ^ (s - 1) * exp (-(t : ℂ)) / (Real.cosh t : ℝ) := by
    have heq : F t = fun x : ℝ => ((t : ℂ) ^ (s - 1) * exp (-(t : ℂ))) *
        ((Real.cos (t * x) / Real.cosh (π * x / 2) : ℝ) : ℂ) := by
      funext x
      dsimp [F]
      rw [ofReal_div, ofReal_cos, ofReal_mul]
      ring
    rw [heq, integral_const_mul, integral_complex_ofReal,
      (Real.integral_cos_div_cosh_pi_mul_div_two_Ioi t).2, ofReal_div, ofReal_one]
    ring
  have hgamma (x : ℝ) : (∫ t in Ioi (0 : ℝ), F t x) = Gamma s * kernel s x := by
    have heq : (fun t : ℝ => F t x) = fun t : ℝ =>
        (t : ℂ) ^ (s - 1) * exp (-((1 : ℂ) * t)) * cos ((x : ℂ) * t) /
          (Real.cosh (π * x / 2) : ℝ) := by
      funext t
      dsimp [F]
      rw [one_mul, mul_comm (t : ℂ) (x : ℂ)]
    rw [heq, integral_div,
      (integral_cpow_mul_cexp_neg_mul_mul_cos_Ioi (by norm_num) hs x).2]
    simp only [div_one, one_pow, ← ofReal_arctan]
    simp only [kernel, ofReal_add, ofReal_one, ofReal_pow]
    ring
  change (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F t x) =
    ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F t x at hswap
  simp_rw [hcos, hgamma] at hswap
  rw [integral_const_mul] at hswap
  exact hswap.symm

/-- Scaling the Laplace integral gives the Fermi–Dirac Mellin kernel. -/
theorem gamma_mul_integral_kernel_eq_mellin {s : ℂ} (hs : 0 < s.re) :
    Gamma s * (∫ x in Ioi (0 : ℝ), kernel s x) =
      2 ^ (1 - s) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) / (exp t + 1) := by
  rw [gamma_mul_integral_kernel hs]
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) / (exp t + 1)
  have hpt (t : ℝ) (ht : t ∈ Ioi 0) :
      (t : ℂ) ^ (s - 1) * exp (-(t : ℂ)) / (Real.cosh t : ℝ) =
        (2 * 2 ^ (1 - s)) * F (2 * t) := by
    have ht0 : 0 < t := ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hpow : (2 : ℂ) ^ (1 - s) * 2 ^ (s - 1) = 1 := by
      rw [← cpow_add _ _ (by norm_num), show 1 - s + (s - 1) = 0 by ring, cpow_zero]
    have hE : exp (t : ℂ) ≠ 0 := exp_ne_zero _
    have hE2 : exp (2 * (t : ℂ)) + 1 ≠ 0 := by
      rw [show 2 * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; rfl, ← ofReal_exp, ← ofReal_one,
        ← ofReal_add]
      exact ofReal_ne_zero.mpr (by positivity)
    have hE3 : exp (t : ℂ) ^ 2 + 1 ≠ 0 := by
      rw [sq, ← exp_add, show (t : ℂ) + t = 2 * t by ring]
      exact hE2
    have hsplit : (2 * (t : ℂ)) ^ (s - 1) = 2 ^ (s - 1) * (t : ℂ) ^ (s - 1) := by
      simpa only [ofReal_ofNat] using
        mul_cpow_ofReal_nonneg (a := 2) (b := t) (by norm_num) ht0.le (s - 1)
    dsimp [F]
    rw [show ((2 * t : ℝ) : ℂ) = (2 : ℂ) * t by push_cast; rfl,
      hsplit, ← mul_div_assoc, ← mul_assoc,
      show 2 * 2 ^ (1 - s) * 2 ^ (s - 1) = (2 : ℂ) by rw [mul_assoc, hpow, mul_one],
      Real.cosh_eq]
    push_cast
    rw [exp_neg, show exp (2 * (t : ℂ)) = exp (t : ℂ) ^ 2 by
      rw [sq, ← exp_add]; congr 1; ring]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hscale := integral_comp_mul_left_Ioi F 0 two_pos
  rw [mul_zero, Complex.real_smul] at hscale
  rw [hscale]
  push_cast
  dsimp [F]
  ring

end DLMF.Zeta.HyperbolicIntegral
