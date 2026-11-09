/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF.AsymptoticApproximations.Basics.Transcendental
import DLMF.AsymptoticApproximations.Basics.Calculus
import DLMF.AsymptoticApproximations.Basics.Existence
import DLMFMathlib.Analysis.Asymptotics.ComplexPowerSeries
import DLMFMathlib.Analysis.Asymptotics.WatsonComplexLog
import DLMFMathlib.Analysis.Asymptotics.WatsonComplexKernel
import DLMF.Gamma.VerticalStrips
import DLMF.Gamma.Integrals.ExponentialMellin
import DLMF.AsymptoticApproximations.Remainders.Stokes
import DLMF.AsymptoticApproximations.Mellin.ContourAsymptotics
import DLMF.AsymptoticApproximations.Integrals.Watson
import DLMF.AsymptoticApproximations.Integrals.Parts
import DLMF.AsymptoticApproximations.Integrals.RayLaplace
import DLMF.IncompleteGamma.ExponentialIntegral
import DLMF.AsymptoticApproximations.Mellin.SmallParameter
import DLMFMathlib.Analysis.Complex.VerticalResidues
import DLMFMathlib.Analysis.Complex.LaplaceInversion
import DLMFMathlib.Analysis.Fourier.TrigonometricTails
import DLMFMathlib.Analysis.Asymptotics.ElementaryPowerSeries
import DLMFMathlib.Analysis.Complex.VerticalResidueExamples
import DLMF.AsymptoticApproximations.Mellin.ContinuationResidues

import DLMF.AsymptoticApproximations.Integrals.InverseLaplace
import DLMF.AsymptoticApproximations.Mellin.LaplaceResidueExpansion
import DLMFMathlib.Analysis.Integral.LaplaceConvergence

import DLMF.AsymptoticApproximations.Mellin.ContinuedExamples
import DLMF.AsymptoticApproximations.Mellin.OscillatoryExamples
import DLMF.AsymptoticApproximations.Basics.ReversionExamples
import DLMF.AsymptoticApproximations.Integrals.WatsonExamples
import DLMF.Gamma.SpecialValues
/-!
# Checks for asymptotic expansion roadmap proofs

The coefficient and normalization checks accompany the general asymptotic theorems.
The cosine-integral check distinguishes the signed coefficients of DLMF 2.11.3 from
the unsigned odd derivatives. The axiom inventory checks the proof dependencies of
the results prepared for the asymptotic expansion roadmap.
-/

open PowerSeries DLMF.AsymptoticApproximations

namespace DLMF.AsymptoticApproximations.CosineIntegral

/-- The second signed coefficient of the cosine integral at `t = 2`. -/
theorem second_coefficient_at_two : cosRationalCoeff 2 2 = 144 / 625 := by
  have h := (cosRationalCoeff_explicit 2).2.1
  norm_num at h ⊢
  exact h

/-- The third derivative of `(1+t²)⁻¹` has the opposite sign to the second coefficient. -/
theorem third_derivative_at_two :
    iteratedDeriv 3 (fun t : ℝ => 1 / (t ^ 2 + 1)) 2 = -(144 / 625) := by
  have h := second_coefficient_at_two
  norm_num [cosRationalCoeff] at h ⊢
  linarith

/-- DLMF's second coefficient is not the unsigned third derivative. -/
theorem second_coefficient_ne_third_derivative :
    cosRationalCoeff 2 2 ≠ iteratedDeriv 3 (fun t : ℝ => 1 / (t ^ 2 + 1)) 2 := by
  rw [second_coefficient_at_two, third_derivative_at_two]
  norm_num

end DLMF.AsymptoticApproximations.CosineIntegral

example (β : ℂ) : logarithmicPower (1 + X) 0 β = PowerSeries.binomialSeries ℂ β := by
  have h : (mk fun n => Ring.choose β n) = PowerSeries.binomialSeries ℂ β := by
    ext n
    simp only [coeff_mk, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  simp [logarithmicPower, binomialSubstitution, h]

example : coeff 0 logSeries = 0 ∧ coeff 1 logSeries = 1 := by
  norm_num [logSeries]

example {c : ℝ} (hc : 0 < c) :
    (∫ y : ℝ, Complex.Gamma ((c : ℂ) + y * Complex.I)) =
      2 * (Real.pi : ℂ) / Complex.exp 1 := by
  simpa only [Complex.one_cpow, mul_one, Complex.exp_neg, div_eq_mul_inv] using
    DLMF.Gamma.integral_Gamma_mul_cpow_neg hc (w := 1) (by norm_num)

open Filter Set Asymptotics
open scoped Topology

example : IsAsymptoticScale atTop (fun (n : ℕ) (x : ℝ) => x⁻¹ ^ n) :=
  isAsymptoticScale_pow tendsto_inv_atTop_zero

example : ¬ IsAsymptoticScale (𝓝[>] (0 : ℝ)) (fun (n : ℕ) (x : ℝ) => x⁻¹ ^ n) := by
  intro h
  have hlim : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Nat.zero_add, pow_zero, pow_one] using (isLittleO_one_iff ℝ).mp (h 0)
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_inv_nhdsGT_zero 0 hlim

example : HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => x⁻¹ ^ n)
    (fun _ => (0 : ℝ)) (fun x => Real.exp (-x)) := by
  intro N
  have h := (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-(N : ℝ))).isBigO
  simpa [Real.rpow_neg, Real.rpow_natCast, inv_pow] using h

example : HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => x⁻¹ ^ n)
    (fun _ => (0 : ℝ)) (fun _ => 0) := by
  intro N
  simpa using isBigO_zero (fun x : ℝ => x⁻¹ ^ N) atTop

example : HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => 2 * x⁻¹ ^ n)
    (fun n => if n = 0 then (1 / 2 : ℝ) else 0) (fun _ => (1 : ℝ)) := by
  have hf := hasAsymptoticPowerSeries_const tendsto_inv_atTop_zero (1 : ℝ)
  have h := HasAsymptoticExpansion.smul_scale (ψ := fun n (x : ℝ) => 2 * x⁻¹ ^ n)
    (κ := fun _ => (1 / 2 : ℝ)) hf (fun n => Filter.Eventually.of_forall fun x => by
      simp only [smul_eq_mul]; ring)
  simpa only [PowerSeries.coeff_C, smul_eq_mul, mul_ite, mul_one, mul_zero] using h

example : ¬ HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => 2 * x⁻¹ ^ n)
    (fun n => if n = 0 then (1 : ℝ) else 0) (fun _ => (1 : ℝ)) := by
  intro hf
  have hs : Tendsto (fun x : ℝ => 2 * x⁻¹ ^ (1 : ℕ)) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  have ht := (hf 1).trans_tendsto hs
  norm_num [Finset.sum_range_succ] at ht

example {P : ℂ⟦X⟧} {L : ℂ} (hL : Complex.exp L = constantCoeff P) :
    logarithmicPower P L 1 = P := logarithmicPower_one hL

example {P : ℂ⟦X⟧} {L : ℂ} (hL : Complex.exp L = constantCoeff P) (r s : ℂ) :
    logarithmicPower P L (r + s) = logarithmicPower P L r * logarithmicPower P L s :=
  logarithmicPower_add (hL ▸ Complex.exp_ne_zero L) L r s

example {P : ℂ⟦X⟧} {L : ℂ} (hL : Complex.exp L = constantCoeff P) (n : ℕ) :
    logarithmicPower P L n = P ^ n := logarithmicPower_natCast hL n

example (P : ℂ⟦X⟧) (L r : ℂ) :
    logarithmicPower P (L + 2 * Real.pi * Complex.I) r =
      C (Complex.exp (2 * Real.pi * Complex.I * r)) * logarithmicPower P L r :=
  logarithmicPower_add_two_pi_mul_I P L r

example : (∫ t : ℝ in Ioi 0, Complex.exp (-((1 + Complex.I) * t))) =
    (1 + Complex.I)⁻¹ := by
  exact integral_exp_neg_one_add_I

example (y : ℝ) :
    ‖Complex.Gamma (1 / 2 + Complex.I * y)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |y|) / 2) := by
  have hcosh : Real.exp (Real.pi * |y|) / 2 ≤ Real.cosh (Real.pi * y) := by
    rw [← Real.cosh_abs (Real.pi * y), abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * |y|))]
  have hb : ‖Complex.Gamma (1 / 2 + Complex.I * y)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-(Real.pi * |y|)) := by
    rw [(DLMF.Gamma.Gamma_half_add_mul_I y).2]
    calc Real.pi / Real.cosh (Real.pi * y) ≤
        Real.pi / (Real.exp (Real.pi * |y|) / 2) :=
          div_le_div_of_nonneg_left Real.pi_pos.le
            (half_pos (Real.exp_pos _)) hcosh
      _ = _ := by rw [Real.exp_neg]; field_simp
  have hs : (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |y|) / 2)) ^ 2 =
      2 * Real.pi * Real.exp (-(Real.pi * |y|)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), pow_two, ← Real.exp_add]
    congr 2
    ring
  have hn := mul_nonneg (Real.sqrt_nonneg (2 * Real.pi))
    (Real.exp_pos (-(Real.pi * |y|) / 2)).le
  nlinarith [norm_nonneg (Complex.Gamma (1 / 2 + Complex.I * y))]

example (a y : ℂ) : y - a + a = y := sub_add_cancel y a

example {R : ℝ} (hR : 0 < R) :
    Complex.rayLaplace (fun w : ℂ => w ^ (-(1 / 2 : ℂ))) (3 * Real.pi / 4)
      ((Real.log R : ℂ) - (Real.pi : ℂ) * Complex.I) =
        Complex.I * (Real.sqrt (Real.pi / R) : ℂ) := by
  let ζ : ℂ := (Real.log R : ℂ) - (Real.pi : ℂ) * Complex.I
  let θ : ℝ := 3 * Real.pi / 4
  have hθ : θ ∈ Ioo (-Real.pi) Real.pi := by
    dsimp [θ]
    constructor <;> linarith [Real.pi_pos]
  have hζ : ζ ∈ Complex.rayLaplaceDomain 0 θ := by
    have him : ζ.im + θ = -Real.pi / 4 := by simp [ζ, θ]; ring
    have hre : (ζ + θ * Complex.I).re = Real.log R := by simp [ζ]
    have him' : (ζ + θ * Complex.I).im = -Real.pi / 4 := by
      simpa using him
    constructor
    · rw [him]
      rw [abs_of_neg (by linarith [Real.pi_pos] : -Real.pi / 4 < 0)]
      linarith [Real.pi_pos]
    · rw [Complex.exp_re, hre, him']
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hhalf : Complex.Gamma (1 / 2) = (Real.sqrt Real.pi : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow Real.pi_nonneg]
    norm_num
  have hreal : Real.exp (-Real.log R / 2) = (Real.sqrt R)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hR, ← Real.exp_neg]
    congr 1
    ring
  have he : Complex.exp (-(1 / 2 : ℂ) * ζ) = ((Real.sqrt R)⁻¹ : ℂ) * Complex.I := by
    rw [show -(1 / 2 : ℂ) * ζ = ((-Real.log R / 2 : ℝ) : ℂ) +
        (Real.pi : ℂ) / 2 * Complex.I by dsimp [ζ]; push_cast; ring,
      Complex.exp_add, Complex.exp_pi_div_two_mul_I, ← Complex.ofReal_exp, hreal,
      Complex.ofReal_inv]
  have h := Complex.rayLaplace_cpow (α := (1 / 2 : ℂ)) (by norm_num) hθ hζ
  change Complex.rayLaplace _ θ ζ = _
  rw [show -(1 / 2 : ℂ) = (1 / 2 : ℂ) - 1 by ring, h, hhalf, he,
    Real.sqrt_div Real.pi_nonneg, Complex.ofReal_div]
  ring

example {R : ℝ} (hR : 0 < R) :
    Complex.rayLaplace (fun w : ℂ => w ^ (-(1 / 2 : ℂ))) (-(3 * Real.pi / 4))
      ((Real.log R : ℂ) + (Real.pi : ℂ) * Complex.I) =
        (-Complex.I) * (Real.sqrt (Real.pi / R) : ℂ) := by
  let ζ : ℂ := (Real.log R : ℂ) + (Real.pi : ℂ) * Complex.I
  let θ : ℝ := -(3 * Real.pi / 4)
  have hθ : θ ∈ Ioo (-Real.pi) Real.pi := by
    dsimp [θ]
    constructor <;> linarith [Real.pi_pos]
  have hζ : ζ ∈ Complex.rayLaplaceDomain 0 θ := by
    have him : ζ.im + θ = Real.pi / 4 := by simp [ζ, θ]; ring
    have hre : (ζ + θ * Complex.I).re = Real.log R := by simp [ζ]
    have him' : (ζ + θ * Complex.I).im = Real.pi / 4 := by
      simpa using him
    constructor
    · rw [him]
      rw [abs_of_pos (by linarith [Real.pi_pos] : 0 < Real.pi / 4)]
      linarith [Real.pi_pos]
    · rw [Complex.exp_re, hre, him']
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hhalf : Complex.Gamma (1 / 2) = (Real.sqrt Real.pi : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow Real.pi_nonneg]
    norm_num
  have hreal : Real.exp (-Real.log R / 2) = (Real.sqrt R)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hR, ← Real.exp_neg]
    congr 1
    ring
  have he : Complex.exp (-(1 / 2 : ℂ) * ζ) = ((Real.sqrt R)⁻¹ : ℂ) * (-Complex.I) := by
    rw [show -(1 / 2 : ℂ) * ζ = ((-Real.log R / 2 : ℝ) : ℂ) +
        (-(Real.pi : ℂ) / 2) * Complex.I by dsimp [ζ]; push_cast; ring,
      Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I, ← Complex.ofReal_exp, hreal,
      Complex.ofReal_inv]
  have h := Complex.rayLaplace_cpow (α := (1 / 2 : ℂ)) (by norm_num) hθ hζ
  change Complex.rayLaplace _ θ ζ = _
  rw [show -(1 / 2 : ℂ) = (1 / 2 : ℂ) - 1 by ring, h, hhalf, he,
    Real.sqrt_div Real.pi_nonneg, Complex.ofReal_div]
  ring

-- Audit the selected core APIs and the declarations prepared for the roadmap.
#print axioms Asymptotics.AsymptoticInversion.coeff_one_mcMahonPhase
#print axioms Asymptotics.AsymptoticInversion.constantCoeff_mcMahonPhase
#print axioms Asymptotics.AsymptoticInversion.isBigO_eval_of_coeff_eq_zero
#print axioms Asymptotics.AsymptoticInversion.isBigO_eval_one
#print axioms Asymptotics.AsymptoticInversion.mcMahonPhase
#print axioms Asymptotics.AsymptoticInversion.trunc_subst
#print axioms Asymptotics.HasAsymptoticExpansion
#print axioms Asymptotics.HasAsymptoticExpansion.add
#print axioms Asymptotics.HasAsymptoticExpansion.comp_tendsto
#print axioms Asymptotics.HasAsymptoticExpansion.congr'
#print axioms Asymptotics.HasAsymptoticExpansion.congr_coeff
#print axioms Asymptotics.HasAsymptoticExpansion.congr_scale
#print axioms Asymptotics.HasAsymptoticExpansion.const_smul
#print axioms Asymptotics.HasAsymptoticExpansion.eq_zero_of_smul_isLittleO
#print axioms Asymptotics.HasAsymptoticExpansion.integral_Ioi_inv_pow
#print axioms Asymptotics.HasAsymptoticExpansion.isLittleO
#print axioms Asymptotics.HasAsymptoticExpansion.mul_left
#print axioms Asymptotics.HasAsymptoticExpansion.neg
#print axioms Asymptotics.HasAsymptoticExpansion.smul_scale
#print axioms Asymptotics.HasAsymptoticExpansion.sub
#print axioms Asymptotics.HasAsymptoticExpansion.sub_smul_isLittleO
#print axioms Asymptotics.HasAsymptoticExpansion.unique
#print axioms Asymptotics.HasAsymptoticExpansion.unique_pow_sub
#print axioms Asymptotics.HasAsymptoticPowerSeries
#print axioms Asymptotics.HasAsymptoticPowerSeries.add
#print axioms Asymptotics.HasAsymptoticPowerSeries.aeval
#print axioms Asymptotics.HasAsymptoticPowerSeries.analytic_comp
#print axioms Asymptotics.HasAsymptoticPowerSeries.comp
#print axioms Asymptotics.HasAsymptoticPowerSeries.comp_tendsto
#print axioms Asymptotics.HasAsymptoticPowerSeries.congr'
#print axioms Asymptotics.HasAsymptoticPowerSeries.const_mul
#print axioms Asymptotics.HasAsymptoticPowerSeries.cpow
#print axioms Asymptotics.HasAsymptoticPowerSeries.div_var
#print axioms Asymptotics.HasAsymptoticPowerSeries.inversion
#print axioms Asymptotics.HasAsymptoticPowerSeries.isBigO_of_constantCoeff_eq_zero
#print axioms Asymptotics.HasAsymptoticPowerSeries.isBigO_one
#print axioms Asymptotics.HasAsymptoticPowerSeries.log
#print axioms Asymptotics.HasAsymptoticPowerSeries.mcMahon_inversion
#print axioms Asymptotics.HasAsymptoticPowerSeries.mul
#print axioms Asymptotics.HasAsymptoticPowerSeries.mul_var
#print axioms Asymptotics.HasAsymptoticPowerSeries.neg
#print axioms Asymptotics.HasAsymptoticPowerSeries.of_remainder
#print axioms Asymptotics.HasAsymptoticPowerSeries.one
#print axioms Asymptotics.HasAsymptoticPowerSeries.pow
#print axioms Asymptotics.HasAsymptoticPowerSeries.recip
#print axioms Asymptotics.HasAsymptoticPowerSeries.remainder
#print axioms Asymptotics.HasAsymptoticPowerSeries.sub
#print axioms Asymptotics.HasAsymptoticPowerSeries.tendsto
#print axioms Asymptotics.HasAsymptoticPowerSeries.unique
#print axioms Asymptotics.IsAsymptoticScale
#print axioms Asymptotics.IsBigO.integral_Ioi_rpow
#print axioms Asymptotics.hasAsymptoticExpansion_exp_neg_ofReal
#print axioms Asymptotics.hasAsymptoticExpansion_integral_kernel_mul_cpow_seq
#print axioms Asymptotics.hasAsymptoticExpansion_inv_one_add_atTop
#print axioms Asymptotics.hasAsymptoticExpansion_inv_one_add_atZero
#print axioms Asymptotics.hasAsymptoticPowerSeries_const
#print axioms Asymptotics.hasAsymptoticPowerSeries_eval
#print axioms Asymptotics.hasAsymptoticPowerSeries_iff
#print axioms Asymptotics.hasAsymptoticPowerSeries_mcMahon_atTop
#print axioms Asymptotics.hasAsymptoticPowerSeries_of_hasFPowerSeriesAt
#print axioms Asymptotics.hasAsymptoticPowerSeries_recip_iff
#print axioms Asymptotics.hasAsymptoticPowerSeries_var
#print axioms Asymptotics.integrableOn_exp_neg_mul_log_smul
#print axioms Asymptotics.integrableOn_kernel_mul_cpow
#print axioms Asymptotics.integral_Ioi_inv_pow
#print axioms Asymptotics.integral_kernel_mul_cpow
#print axioms Asymptotics.isAsymptoticScale_pow
#print axioms Asymptotics.isAsymptoticScale_rpow_neg
#print axioms Asymptotics.isBigO_cpow_rpow_atTop
#print axioms Asymptotics.isBigO_integral_exp_neg_mul_sub_sum
#print axioms Asymptotics.isBigO_laplace_log_sub_sum_cpow
#print axioms Asymptotics.isBigO_log_gamma_term_cpow
#print axioms Asymptotics.mcMahonSeries
#print axioms Asymptotics.mcMahonSeries_coeff_le_two
#print axioms Asymptotics.mcMahonSeries_spec
#print axioms Asymptotics.natCast_mul_coeff_mcMahonSeries
#print axioms Complex.FourierInversePowers.amplitude
#print axioms Complex.FourierInversePowers.continuousOn_amplitude
#print axioms Complex.FourierInversePowers.derivativePolynomial
#print axioms Complex.FourierInversePowers.hasDerivAt_amplitude
#print axioms Complex.FourierInversePowers.hasUniformFourierLimit_amplitude
#print axioms Complex.FourierInversePowers.hasUniformFourierLimit_iteratedDerivWithin_amplitude_one
#print axioms Complex.FourierInversePowers.hasUniformFourierLimit_iteratedDerivWithin_sin_div
#print axioms Complex.FourierInversePowers.iteratedDerivWithin_amplitude_one
#print axioms Complex.FourierInversePowers.iteratedDerivWithin_sin_div
#print axioms Complex.FourierInversePowers.iteratedDerivativePolynomial
#print axioms Complex.FourierInversePowers.not_integrableOn_iteratedDerivWithin_one_sin_div
#print axioms Complex.HasRayLaplaceBounds
#print axioms Complex.HasUniformFourierLimit
#print axioms Complex.HasUniformFourierLimit.add
#print axioms Complex.HasUniformFourierLimit.congr
#print axioms Complex.HasUniformFourierLimit.const_mul
#print axioms Complex.MellinBarnesSeries.hasSum_residue
#print axioms Complex.MellinBarnesSeries.residue_eq
#print axioms Complex.MellinBarnesSeries.sub_eq_sum_residue
#print axioms Complex.MellinBarnesSeries.tendsto_sum_residue
#print axioms Complex.OscillatoryMellinTail.continuous_integrand
#print axioms Complex.OscillatoryMellinTail.integrableOn_integrand
#print axioms Complex.OscillatoryMellinTail.integrand
#print axioms Complex.differentiableAt_oscillatoryMellinTailIntegral
#print axioms Complex.differentiableOn_rayLaplace
#print axioms Complex.differentiable_oscillatoryMellinTail
#print axioms Complex.eq_zero_of_tendsto_mul_exp_pi_I
#print axioms Complex.eventually_circleIntegral_eq_two_pi_mul_I_residue
#print axioms Complex.eventually_log_eq_log_add_log_normalized
#print axioms Complex.exists_bound_on_ray_rectangle
#print axioms Complex.exists_differentiableOn_rayLaplace
#print axioms Complex.exists_entire_oscillatoryMellinTail
#print axioms Complex.exists_inverseLaplace_of_deriv_norm_le_rpow
#print axioms Complex.exists_inverseLaplace_of_norm_le_rpow
#print axioms Complex.exists_re_ge_mem_iUnion_rayLaplaceDomain
#print axioms Complex.hasMellin_exp_neg_mul_log
#print axioms Complex.hasMellin_indicator_exp_I_mul_rpow_cpow
#print axioms Complex.hasRayLaplaceBounds_of_local_bounds
#print axioms Complex.hasUniformFourierLimit_cpow_neg
#print axioms Complex.hasUniformFourierLimit_exp_mul_cpow_neg
#print axioms Complex.integrableOn_cpow_mul_exp_I
#print axioms Complex.integrableOn_exp_neg_mul_cpow_sub_one_mul_log
#print axioms Complex.integrableOn_rayLaplace_kernel
#print axioms Complex.integrable_exp_mul_vertical_of_norm_le
#print axioms Complex.integrable_exp_mul_vertical_of_norm_le_rpow
#print axioms Complex.integrable_norm_vertical_rpow
#print axioms Complex.integral_exp_neg_mul_cpow_sub_one_mul_log
#print axioms Complex.integral_inv_sq_add_sq
#print axioms Complex.integral_vertical_one_div_mul_one_sub_half
#print axioms Complex.integral_vertical_one_div_mul_one_sub_neg_half
#print axioms Complex.integral_vertical_sub_eq_two_pi_mul_sum_residue
#print axioms Complex.isOpen_rayLaplaceDomain
#print axioms Complex.mellinInv_eq_sum_residue_add
#print axioms Complex.mellinInv_eq_sum_residue_add_of_iSup_norm
#print axioms Complex.min_re_exp_add_mul_I_le
#print axioms Complex.norm_exp_neg_ofReal_sub_sum_le
#print axioms Complex.norm_fourier_truncation_sub_integral_le
#print axioms Complex.norm_one_div_mul_one_sub_le
#print axioms Complex.norm_rpow_neg_le_vertical_quadratic
#print axioms Complex.not_tendsto_exp_mul_I_atTop
#print axioms Complex.not_tendsto_integral_exp_mul_I
#print axioms Complex.oscillatoryMellinTail
#print axioms Complex.oscillatoryMellinTailIntegral
#print axioms Complex.oscillatoryMellinTailIntegral_recurrence
#print axioms Complex.oscillatoryMellinTail_eq_integral
#print axioms Complex.oscillatoryMellinTail_neg_conj
#print axioms Complex.oscillatoryMellinTail_one
#print axioms Complex.rayLaplace
#print axioms Complex.rayLaplaceDomain
#print axioms Complex.rayLaplace_cpow
#print axioms Complex.rayLaplace_differentiableOn_and_eqOn
#print axioms Complex.rayLaplace_eq_of_bounds
#print axioms Complex.rayLaplace_zero
#print axioms Complex.residue_eq_of_analyticAt_sub_sum_div
#print axioms Complex.residue_eq_of_eventuallyEq_div_sub
#print axioms Complex.residue_one_div_mul_one_sub_zero
#print axioms Complex.residue_sum_div_sub
#print axioms Complex.tendstoUniformlyOn_integral_exp_mul_of_integrable_deriv
#print axioms Complex.tendsto_exp_mul_vertical_of_norm_le_rpow
#print axioms Complex.tendsto_integral_exp_mul_vertical_of_deriv
#print axioms Complex.tendsto_integral_horizontal_exp_mul_of_norm_le
#print axioms Complex.tendsto_integral_oscillatoryMellinTail
#print axioms Complex.tendsto_integral_oscillatoryMellinTail_of_pos
#print axioms Complex.tendsto_integral_vertical_sub
#print axioms DLMF.AsymptoticApproximations.CosineIntegral.second_coefficient_ne_third_derivative
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansion.add
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansion.deriv
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansion.inv
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansion.mul
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansion.pow
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansion.sub
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansion.unique
#print axioms DLMF.AsymptoticApproximations.HasPoincareExpansionAt.unique
#print axioms DLMF.AsymptoticApproximations.besselSqMellinA
#print axioms DLMF.AsymptoticApproximations.besselSqMellinB
#print axioms DLMF.AsymptoticApproximations.besselSqMellinKernel
#print axioms DLMF.AsymptoticApproximations.bromwichPartialIntegral_sub_sum
#print axioms DLMF.AsymptoticApproximations.cexp_mul_I_isBigO_one
#print axioms DLMF.AsymptoticApproximations.cexp_neg_isLittleO_one_sector
#print axioms DLMF.AsymptoticApproximations.cexp_sub_one_sub_isBigO_sq
#print axioms DLMF.AsymptoticApproximations.convolution_add_residues_isLittleO
#print axioms DLMF.AsymptoticApproximations.convolution_eq_sum_trunc
#print axioms DLMF.AsymptoticApproximations.differentiableAt_mellinContinuationAtTop
#print axioms DLMF.AsymptoticApproximations.differentiableAt_mellinContinuationAtZero
#print axioms DLMF.AsymptoticApproximations.differentiableAt_mellin_truncHigh_continuation
#print axioms DLMF.AsymptoticApproximations.differentiableAt_oscillatoryMellinContinuationAtTop
#print axioms DLMF.AsymptoticApproximations.existsUnique_root_of_isEquivalent
#print axioms DLMF.AsymptoticApproximations.existsUnique_sq_sub_log_eq
#print axioms DLMF.AsymptoticApproximations.exists_bound_mellin_truncHigh_continuation
#print axioms DLMF.AsymptoticApproximations.exists_differentiableOn_oscillatoryMellinContinuation
#print axioms DLMF.AsymptoticApproximations.exists_entire_oscillatoryMellinContinuationAtTop
#print axioms DLMF.AsymptoticApproximations.exists_hasAsymptoticExpansion_inv_pow_atTop
#print axioms DLMF.AsymptoticApproximations.exists_hasPoincareExpansion_closed_sector
#print axioms DLMF.AsymptoticApproximations.exists_hasPoincareExpansion_sector
#print axioms DLMF.AsymptoticApproximations.exists_hasPoincareExpansion_sector'
#print axioms DLMF.AsymptoticApproximations.exists_inverseLaplace_hasExpansion
#print axioms DLMF.AsymptoticApproximations.exists_inverseLaplace_hasExpansion'
#print axioms DLMF.AsymptoticApproximations.exists_meromorphic_mellinContinuationAtTop
#print axioms DLMF.AsymptoticApproximations.exists_meromorphic_mellinContinuationAtZero
#print axioms DLMF.AsymptoticApproximations.exists_punctured_differentiableAt
#print axioms DLMF.AsymptoticApproximations.exists_tendsto_intervalIntegral_of_isEquivalent_cpow
#print axioms DLMF.AsymptoticApproximations.exp_neg_isLittleO_one
#print axioms DLMF.AsymptoticApproximations.fourier_Ioi_hasGeneralizedAsymptoticExpansion
#print axioms DLMF.AsymptoticApproximations.fourier_error_bound
#print axioms DLMF.AsymptoticApproximations.fourier_hasGeneralizedAsymptoticExpansion
#print axioms DLMF.AsymptoticApproximations.haar_isLittleO
#print axioms DLMF.AsymptoticApproximations.haar_isLittleO_pow
#print axioms DLMF.AsymptoticApproximations.haar_isLittleO_pow'
#print axioms DLMF.AsymptoticApproximations.haar_sub
#print axioms DLMF.AsymptoticApproximations.hasAsymptoticExpansion_integral_cexp_smul_cpow_seq
#print axioms DLMF.AsymptoticApproximations.hasAsymptoticExpansion_integral_exp_smul_rpow_seq
#print axioms DLMF.AsymptoticApproximations.hasAsymptoticExpansion_laplace_inv_one_add
#print axioms DLMF.AsymptoticApproximations.hasAsymptoticExpansion_rayLaplace
#print axioms DLMF.AsymptoticApproximations.hasGeneralizedAsymptoticExpansion_convergent_ne
#print axioms DLMF.AsymptoticApproximations.hasPoincareExpansion_cexp_neg
#print axioms DLMF.AsymptoticApproximations.hasPoincareExpansion_cexp_neg_sqrt
#print axioms DLMF.AsymptoticApproximations.hasPoincareExpansion_iff_hasAsymptoticPowerSeries
#print axioms DLMF.AsymptoticApproximations.hasPoincareExpansion_iff_tendsto
#print axioms DLMF.AsymptoticApproximations.hasPoincareExpansion_inv_sub_one
#print axioms DLMF.AsymptoticApproximations.hasPoincareExpansion_of_hasSum
#print axioms DLMF.AsymptoticApproximations.hasPoincareExpansion_zero
#print axioms DLMF.AsymptoticApproximations.hasSum_laplace_inv_one_add
#print axioms DLMF.AsymptoticApproximations.hasUniformPoincareExpansion_iff
#print axioms DLMF.AsymptoticApproximations.integrableOn_exp_neg_mul_cpow_tail
#print axioms DLMF.AsymptoticApproximations.integrableOn_exp_neg_mul_truncHigh_cpow
#print axioms DLMF.AsymptoticApproximations.integral_Ioi_isEquivalent_of_isEquivalent_cpow
#print axioms DLMF.AsymptoticApproximations.integral_exp_neg_mul_cpow_neg_half
#print axioms DLMF.AsymptoticApproximations.integral_exp_neg_mul_truncHigh_cpow
#print axioms DLMF.AsymptoticApproximations.integral_exp_neg_one_add_I
#print axioms DLMF.AsymptoticApproximations.integral_truncHigh_mul_truncLow
#print axioms DLMF.AsymptoticApproximations.intervalIntegral_isEquivalent_cpow
#print axioms DLMF.AsymptoticApproximations.intervalIntegral_isEquivalent_log
#print axioms DLMF.AsymptoticApproximations.inverseLaplace_of_hasAsymptoticExpansion
#print axioms DLMF.AsymptoticApproximations.inverseLaplace_of_hasAsymptoticExpansion'
#print axioms DLMF.AsymptoticApproximations.lagrangeReversionCoeff_affine
#print axioms DLMF.AsymptoticApproximations.lagrangeReversionCoeff_eq_neg_coeff_mcMahonSeries
#print axioms DLMF.AsymptoticApproximations.lagrangeReversionCoeff_le_two
#print axioms DLMF.AsymptoticApproximations.lagrange_reversion
#print axioms DLMF.AsymptoticApproximations.lagrange_reversion_of_isEquivalent
#print axioms DLMF.AsymptoticApproximations.laplace_cpow_tail_sub_sum_isBigO
#print axioms DLMF.AsymptoticApproximations.laplace_eq_trunc_add
#print axioms DLMF.AsymptoticApproximations.laplace_error_bound
#print axioms DLMF.AsymptoticApproximations.laplace_expansion_residues_of_asymptoticExpansion
#print axioms DLMF.AsymptoticApproximations.laplace_expansion_residues_of_asymptoticExpansion_atLine
#print axioms
  DLMF.AsymptoticApproximations.laplace_expansion_residues_of_asymptoticExpansion_of_pole_locations
#print axioms DLMF.AsymptoticApproximations.laplace_hasAsymptoticExpansion_of_contDiffOn
#print axioms DLMF.AsymptoticApproximations.laplace_inv_one_add_eq
#print axioms DLMF.AsymptoticApproximations.laplace_inv_one_add_eq_complex
#print axioms DLMF.AsymptoticApproximations.laplace_inv_one_add_isBigO
#print axioms DLMF.AsymptoticApproximations.laplace_inversion
#print axioms DLMF.AsymptoticApproximations.laplace_remainder_isBigO
#print axioms DLMF.AsymptoticApproximations.laplace_small_parameter
#print axioms DLMF.AsymptoticApproximations.laplace_small_parameter_cutoff
#print axioms DLMF.AsymptoticApproximations.laplace_small_parameter_isBigO_rpow
#print axioms DLMF.AsymptoticApproximations.laplace_small_parameter_of_lt_re
#print axioms DLMF.AsymptoticApproximations.laplace_truncHigh_shift
#print axioms DLMF.AsymptoticApproximations.laplace_truncHigh_shift'
#print axioms DLMF.AsymptoticApproximations.laplace_truncLow_shift
#print axioms DLMF.AsymptoticApproximations.laplace_trunc_eq_mellinInv
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtTop
#print axioms
  DLMF.AsymptoticApproximations.mellinContinuationAtTop_add_principalParts_differentiableAt
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtTop_eq
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtTop_eq_mellin
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtTop_inv_one_add
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtTop_zero
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtZero
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtZero_eq
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtZero_eq_mellin
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtZero_exp_neg
#print axioms
  DLMF.AsymptoticApproximations.mellinContinuationAtZero_sub_principalParts_differentiableAt
#print axioms DLMF.AsymptoticApproximations.mellinContinuationAtZero_zero
#print axioms DLMF.AsymptoticApproximations.mellinConvergent_pairs
#print axioms DLMF.AsymptoticApproximations.mellinConvergent_truncHigh
#print axioms DLMF.AsymptoticApproximations.mellinConvergent_truncHigh_sub_sum
#print axioms DLMF.AsymptoticApproximations.mellinConvergent_truncLow
#print axioms DLMF.AsymptoticApproximations.mellinConvergent_trunc_h
#print axioms DLMF.AsymptoticApproximations.mellinInv_add_residues_isLittleO
#print axioms DLMF.AsymptoticApproximations.mellinInv_isLittleO
#print axioms DLMF.AsymptoticApproximations.mellinInv_shift
#print axioms DLMF.AsymptoticApproximations.mellinTruncHigh
#print axioms DLMF.AsymptoticApproximations.mellinTruncHigh_eq_indicator
#print axioms DLMF.AsymptoticApproximations.mellinTruncLow
#print axioms DLMF.AsymptoticApproximations.mellin_convolution
#print axioms DLMF.AsymptoticApproximations.mellin_convolution_eq_mellinInv
#print axioms DLMF.AsymptoticApproximations.mellin_eq_truncLow_add_truncHigh
#print axioms DLMF.AsymptoticApproximations.mellin_exp_neg
#print axioms DLMF.AsymptoticApproximations.mellin_inv_one_add
#print axioms DLMF.AsymptoticApproximations.mellin_truncHigh_continuation
#print axioms DLMF.AsymptoticApproximations.mellin_truncHigh_continuation_osc
#print axioms DLMF.AsymptoticApproximations.mellin_truncHigh_continuation_regularPart_eq
#print axioms DLMF.AsymptoticApproximations.mellin_truncLow_continuation
#print axioms DLMF.AsymptoticApproximations.mellin_truncLow_differentiableAt
#print axioms DLMF.AsymptoticApproximations.meromorphicOn_mellinContinuationAtTop
#print axioms DLMF.AsymptoticApproximations.meromorphicOn_mellinContinuationAtZero
#print axioms DLMF.AsymptoticApproximations.meromorphic_mellin_truncHigh_continuation
#print axioms DLMF.AsymptoticApproximations.norm_mellinInv_le
#print axioms DLMF.AsymptoticApproximations.norm_mellin_truncLow_le
#print axioms DLMF.AsymptoticApproximations.not_cexp_neg_isLittleO_one_halfPlane
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_eq
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_eq_mellin
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_exp
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_one_term
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_quadratic
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_single
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_two_terms
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_two_terms_one
#print axioms DLMF.AsymptoticApproximations.oscillatoryMellinContinuationAtTop_zero
#print axioms DLMF.AsymptoticApproximations.rational_reversion_sub_isBigO
#print axioms DLMF.AsymptoticApproximations.residueAt_laplace_inv_one_add
#print axioms DLMF.AsymptoticApproximations.residueAt_laplace_inv_one_add_truncHigh
#print axioms DLMF.AsymptoticApproximations.residueAt_neg_of_differentiableAt
#print axioms DLMF.AsymptoticApproximations.residue_mellinContinuationAtTop
#print axioms DLMF.AsymptoticApproximations.residue_mellinContinuationAtTop_inv_one_add
#print axioms DLMF.AsymptoticApproximations.residue_mellinContinuationAtZero
#print axioms DLMF.AsymptoticApproximations.residue_mellinContinuationAtZero_exp_neg
#print axioms DLMF.AsymptoticApproximations.ritt_isBigO
#print axioms DLMF.AsymptoticApproximations.ritt_isLittleO
#print axioms DLMF.AsymptoticApproximations.root_isEquivalent
#print axioms DLMF.AsymptoticApproximations.sin_pi_mul_add_inv_isBigO
#print axioms DLMF.AsymptoticApproximations.sq_sub_log_root_isEquivalent
#print axioms DLMF.AsymptoticApproximations.sq_sub_log_root_second
#print axioms DLMF.AsymptoticApproximations.sq_sub_log_root_sq
#print axioms DLMF.AsymptoticApproximations.strictMonoOn_sub_half_log
#print axioms DLMF.AsymptoticApproximations.sub_half_log_isEquivalent
#print axioms DLMF.AsymptoticApproximations.tanh_isEquivalent_id
#print axioms DLMF.AsymptoticApproximations.tendsto_bromwichPartialIntegral_Gamma_cpow
#print axioms DLMF.AsymptoticApproximations.tendsto_bromwichPartialIntegral_cpow_neg
#print axioms DLMF.AsymptoticApproximations.tsum_tail_isBigO_pow
#print axioms DLMF.AsymptoticApproximations.watson_lemma
#print axioms DLMF.AsymptoticApproximations.watson_lemma_kernel
#print axioms DLMF.AsymptoticApproximations.watson_lemma_laplaceTransform
#print axioms DLMF.AsymptoticApproximations.watson_lemma_log
#print axioms DLMF.AsymptoticApproximations.watson_lemma_rotate
#print axioms DLMF.AsymptoticApproximations.watson_lemma_sector
#print axioms DLMF.Confluent.expIntegralE_hasSum_noninteger
#print axioms DLMF.Confluent.expIntegralE_laplace_complex
#print axioms DLMF.Gamma.Gamma_half_add_mul_I
#print axioms DLMF.Gamma.continuous_Gamma_vertical
#print axioms DLMF.Gamma.continuous_vertical_of_Gamma_one_sub_mul
#print axioms DLMF.Gamma.exists_norm_Gamma_le_line
#print axioms DLMF.Gamma.exists_norm_Gamma_le_positive_strip
#print axioms DLMF.Gamma.exists_norm_Gamma_le_strip_of_one_le_abs_im
#print axioms DLMF.Gamma.exists_norm_Gamma_le_strip_of_separated
#print axioms DLMF.Gamma.integrable_Gamma_mul_cpow_neg
#print axioms DLMF.Gamma.integrable_Gamma_vertical_mul_exp
#print axioms DLMF.Gamma.integral_Gamma_mul_cpow_neg
#print axioms DLMF.Gamma.integral_Gamma_mul_exp
#print axioms DLMF.Gamma.tendsto_iSup_norm_Gamma_one_sub_mul
#print axioms DLMF.Gamma.verticalIntegrable_Gamma_of_ne_neg_nat
#print axioms DLMF.Gamma.verticalIntegrable_Gamma_one_sub_mul
#print axioms MeasureTheory.IntegrableOn.cexp_neg_mul_of_nonneg
#print axioms MeasureTheory.integrableOn_Ioc_of_isBigO_rpow
#print axioms MeasureTheory.integrableOn_exp_neg_smul_iff
#print axioms MeromorphicOn.eq_of_isConnected_of_eventuallyEq
#print axioms MeromorphicOn.eventuallyEq_nhdsNE_of_isConnected_of_eventuallyEq
#print axioms PowerSeries.coeff_lagrangeBurmann_basis
#print axioms PowerSeries.coeff_mul_logarithmicJacobian_subst
#print axioms PowerSeries.coeff_mul_subst_eq_sum_range
#print axioms PowerSeries.coeff_pow_sub_X_mul_derivative
#print axioms PowerSeries.coeff_subst_eq_sum_range_of_lt
#print axioms PowerSeries.coeff_subst_inverse_coordinate
#print axioms PowerSeries.hasFPowerSeriesAt_log_one_add
#print axioms PowerSeries.logSeries
#print axioms PowerSeries.logarithmicPower_add_two_pi_mul_I
#print axioms PowerSeries.logarithmicPower_natCast
#print axioms PowerSeries.natCast_mul_coeff_reversion
#print axioms Real.norm_exp_neg_sub_sum_le
#print axioms Real.not_integrableOn_cos_div
#print axioms Real.not_integrableOn_deriv_sin_div
#print axioms Real.tendsto_integral_cos_mul_div
#print axioms continuousAt_integral_exp_neg_mul_dilate_of_mellinConvergent
#print axioms continuousOn_integral_cexp_neg_mul_smul
#print axioms integrableOn_exp_neg_mul_of_mellinConvergent
#print axioms integrable_mellinInv_integrand
#print axioms inv_one_add_sub_sum_inv_pow
#print axioms inv_one_add_sub_sum_neg_pow
#print axioms mellinInv_add
#print axioms norm_mellin_le_of_support_gt_one
