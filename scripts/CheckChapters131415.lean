/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF.Confluent
import DLMF.Legendre
import DLMF.Hypergeometric
import DLMF.Bessel.ModifiedComparison
import DLMF.Bessel.ModifiedComparison.Asymptotics
import DLMF.Legendre.Uniform.HyperbolicEquation
import DLMF.Legendre.Uniform.BesselApproximation
import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
import DLMFMathlib.Analysis.Asymptotics.WatsonGaussian
import DLMFMathlib.Analysis.ODE.RecessiveUniqueness
import DLMFMathlib.Analysis.Integral.HyperbolicComparison

/-!
# Axiom audit for Chapter 13, 14 and 15 proofs

The closed admissions and their supporting declarations must use standard axioms only,
without `sorryAx`. The chapter umbrellas retain other explicitly admitted results.
-/

#print axioms DLMF.Gamma.scaledGamma_ofReal_eq_exp_binetIntegral
#print axioms DLMF.Gamma.isBigO_binetIntegral_sub_inv
#print axioms DLMF.Gamma.isBigO_binetIntegral_inv
#print axioms DLMF.Gamma.isBigO_binetIntegral_div_sub
#print axioms DLMF.Gamma.isBigO_binetIntegral_div_sub_main
#print axioms DLMF.Gamma.isBigO_exp_binetIntegral_div_sub_main
#print axioms DLMF.Gamma.isBigO_scaledGamma_div_sub_main
#print axioms DLMF.Confluent.KummerLargeParameter.ratioCoefficient
#print axioms DLMF.Confluent.KummerLargeParameter.firstCoefficient
#print axioms DLMF.Confluent.KummerLargeParameter.nonneg_firstCoefficient_and_le
#print axioms DLMF.Confluent.KummerLargeParameter.firstCoefficient_succ
#print axioms DLMF.Confluent.KummerLargeParameter.factor_bounds
#print axioms DLMF.Confluent.KummerLargeParameter.abs_ratioCoefficient_sub_le
#print axioms DLMF.Confluent.KummerLargeParameter.ratioCoefficient_eq_pochhammer_div
#print axioms DLMF.Confluent.KummerLargeParameter.hasSum_firstCoefficient
#print axioms DLMF.Confluent.KummerLargeParameter.hasSum_ratioCoefficient
#print axioms DLMF.Confluent.KummerLargeParameter.isBigO_kummerM_sub_exp
#print axioms DLMF.Confluent.kummerM_large_a_b
#print axioms Real.summable_nat_pow_mul_pow_div_factorial
#print axioms DLMF.Hypergeometric.fractional_integral_one
#print axioms DLMF.Legendre.FerrersBarnes.ferrersP_quadratic
#print axioms DLMF.Legendre.FerrersBarnes.integral_kernel_transform
#print axioms DLMF.Legendre.FerrersBarnes.integral_value
#print axioms DLMF.Legendre.ferrers_barnes_integral
#print axioms DLMF.Legendre.FerrersTriple.legendreQRegular_nat
#print axioms DLMF.Legendre.FerrersTriple.intervalIntegrable_ferrersQ
#print axioms DLMF.Legendre.FerrersTriple.integral_ferrersP_mul_ferrersQ_eq_neg_swap
#print axioms DLMF.Legendre.FerrersTriple.ferrersQ_nat_recurrence
#print axioms DLMF.Legendre.FerrersTriple.integral_legendrePolynomialP_mul_ferrersQ
#print axioms
  DLMF.Legendre.FerrersTriple.intervalIntegrable_ferrersQ_mul_pow_mul_legendrePolynomialP
#print axioms
  DLMF.Legendre.FerrersTriple.intervalIntegrable_legendrePolynomialP_mul_pow_mul_ferrersQ
#print axioms DLMF.Legendre.FerrersTriple.integral_moments_eq_neg_swap
#print axioms DLMF.Legendre.FerrersTriple.differencePolynomial
#print axioms DLMF.Legendre.FerrersTriple.natDegree_differencePolynomial_le
#print axioms DLMF.Legendre.FerrersTriple.eval_differencePolynomial
#print axioms DLMF.Legendre.FerrersTriple.integral_legendrePolynomialP_mul_pow_eq_zero
#print axioms DLMF.Legendre.FerrersTriple.integral_legendrePolynomialP_mul_polynomial_eq_zero
#print axioms DLMF.Legendre.FerrersTriple.integral_polynomial_moments_eq_neg_swap
#print axioms DLMF.Legendre.FerrersTriple.natDegree_legendrePolyR_le
#print axioms DLMF.Legendre.FerrersTriple.integral
#print axioms DLMF.Legendre.FerrersTriple.intervalIntegrable_triple
#print axioms DLMF.Legendre.FerrersTriple.integral_eq_neg_swap
#print axioms DLMF.Legendre.FerrersTriple.integral_eq_swap_of_le
#print axioms DLMF.Legendre.FerrersTriple.integral_eq_swap
#print axioms DLMF.Legendre.FerrersTriple.integral_comm
#print axioms DLMF.Legendre.FerrersTriple.integral_zero_triangle
#print axioms DLMF.Legendre.FerrersTriple.legendrePolynomialP_neg
#print axioms DLMF.Legendre.FerrersTriple.integral_zero_even
#print axioms DLMF.Legendre.FerrersTriple.integral_cos_mul_sin
#print axioms DLMF.Legendre.ferrers_triple_integral'
#print axioms DLMF.Legendre.ferrers_triple_integral
#print axioms LiouvilleGreen.eqOn_of_tendsto_zero_of_tendsto_div_one
#print axioms DLMF.Legendre.ZonalSeries.tendsto_sum_legendreCoeff

#print axioms DLMF.Legendre.conical_stieltjes_integral
#print axioms DLMF.Legendre.ConicalStieltjes.hasIntegralAtTop
#print axioms DLMF.Legendre.ZonalSeries.exists_summable_bound
#print axioms DLMF.Hypergeometric.GaussMoments.squareCoeff
#print axioms DLMF.Hypergeometric.GaussMoments.integral_norm_square_term
#print axioms DLMF.Hypergeometric.GaussMoments.norm_regularized_coefficient
#print axioms DLMF.Hypergeometric.GaussMoments.summable_integral_norm_square_term
#print axioms DLMF.Hypergeometric.GaussMoments.square_gauss_moment
#print axioms DLMF.Hypergeometric.GaussMoments.pfaff_positive
#print axioms DLMF.Hypergeometric.GaussMoments.symmetric_gauss_moment_transform
#print axioms DLMF.Hypergeometric.GaussMoments.symmetric_gauss_moment
#print axioms DLMF.Hypergeometric.GaussMoments.stieltjesBase
#print axioms DLMF.Hypergeometric.GaussMoments.stieltjesTransform
#print axioms DLMF.Hypergeometric.GaussMoments.integrable_stieltjesBase
#print axioms DLMF.Hypergeometric.GaussMoments.integrable_stieltjesBase_div
#print axioms DLMF.Hypergeometric.GaussMoments.stieltjesTransform_eq_small
#print axioms DLMF.Hypergeometric.GaussMoments.integrable_stieltjes_kernel
#print axioms DLMF.Hypergeometric.GaussMoments.differentiableOn_stieltjesTransform
#print axioms DLMF.Hypergeometric.GaussMoments.stieltjesTransform_eq
#print axioms DLMF.Hypergeometric.GaussMoments.symmetric_stieltjes
#print axioms Real.sinh_le_mul_cosh
#print axioms Real.cosh_div_sinh_sub_inv_bounds
#print axioms Real.hasDerivAt_cosh_div_sinh_sub_inv
#print axioms Real.integrableOn_inv_sq_sub_inv_sinh_sq
#print axioms Real.integral_Ioi_inv_sq_sub_inv_sinh_sq
#print axioms DLMF.Bessel.re_besselK_eq_integral_cosh
#print axioms DLMF.Bessel.re_besselK_le_re_besselK_of_nonneg_of_le
#print axioms DLMF.Bessel.mul_re_besselI_mul_re_besselK_le_one
#print axioms DLMF.Bessel.strictMonoOn_re_besselI_div_re_besselK
#print axioms DLMF.Bessel.ModifiedComparison.green_nonneg
#print axioms DLMF.Bessel.ModifiedComparison.norm_green_mul_le
#print axioms DLMF.Bessel.ModifiedComparison.recessive
#print axioms DLMF.Bessel.ModifiedComparison.dominant
#print axioms DLMF.Bessel.ModifiedComparison.recessiveDerivative
#print axioms DLMF.Bessel.ModifiedComparison.dominantDerivative
#print axioms DLMF.Bessel.ModifiedComparison.hasDerivAt_recessive
#print axioms DLMF.Bessel.ModifiedComparison.hasDerivAt_dominant
#print axioms DLMF.Bessel.ModifiedComparison.wronskian_recessive_dominant
#print axioms DLMF.Bessel.ModifiedComparison.norm_recessive
#print axioms DLMF.Bessel.ModifiedComparison.norm_dominant
#print axioms DLMF.Bessel.ModifiedComparison.norm_recessive_pos
#print axioms DLMF.Bessel.ModifiedComparison.norm_dominant_pos
#print axioms DLMF.Bessel.ModifiedComparison.norm_green_mul_norm_recessive_le
#print axioms DLMF.Bessel.ModifiedComparison.norm_dominant_mul_norm_recessive_le
#print axioms DLMF.Bessel.ModifiedComparison.norm_recessive_div_norm_dominant_le
#print axioms DLMF.Bessel.ModifiedComparison.derivativeWeight
#print axioms DLMF.Bessel.ModifiedComparison.norm_green_deriv_mul_norm_recessive_le
#print axioms DLMF.Bessel.ModifiedComparison.norm_recessive_sq_le
#print axioms DLMF.Bessel.ModifiedComparison.exists_solution

#print axioms Complex.differentiableOn_intervalIntegral_of_continuousOn
#print axioms DLMF.Legendre.ferrersP_dougall_series
#print axioms DLMF.Legendre.ZonalSeries.hasSum_negative_order
#print axioms DLMF.Legendre.ZonalSeries.tendsto_partialSum_negative_order
#print axioms DLMF.Legendre.HyperbolicAssociatedP.value
#print axioms DLMF.Legendre.HyperbolicAssociatedP.firstDerivative
#print axioms DLMF.Legendre.HyperbolicAssociatedP.hasDerivAt_value
#print axioms DLMF.Legendre.HyperbolicAssociatedP.hasDerivAt_firstDerivative
#print axioms DLMF.Legendre.HyperbolicAssociatedP.value_eq_exp_mul
#print axioms DLMF.Legendre.HyperbolicAssociatedP.exp_mul_firstDerivative
#print axioms DLMF.Legendre.HyperbolicAssociatedP.tendsto_exp_mul_value
#print axioms DLMF.Legendre.HyperbolicAssociatedP.tendsto_exp_mul_firstDerivative
#print axioms DLMF.Legendre.HyperbolicAssociatedP.tendsto_value_zero
#print axioms DLMF.Legendre.HyperbolicAssociatedP.tendsto_firstDerivative_zero
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_sqrt_mul_exp_mul_besselK
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_sqrt_mul_exp_neg_mul_besselI
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_exp_mul_recessive
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_exp_neg_mul_dominant
#print axioms DLMF.Bessel.ModifiedComparison.recessiveDerivative_eq
#print axioms DLMF.Bessel.ModifiedComparison.dominantDerivative_eq
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_exp_mul_recessiveDerivative
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_exp_neg_mul_dominantDerivative
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_recessive_zero
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_recessiveDerivative_zero
#print axioms DLMF.Bessel.ModifiedComparison.tendsto_derivativeWeight_zero
#print axioms DLMF.Bessel.ModifiedComparison.norm_div_recessive_sub_one_le
#print axioms Real.one_lt_cosh_div_sinh
#print axioms Real.one_sub_cosh_div_sinh_sq
#print axioms Real.tendsto_cosh_div_sinh_atTop
#print axioms Real.log_cosh_div_sinh_ratio
#print axioms Complex.QuadraticLaplace.integral_cpow_mul_exp_neg_mul_sq
#print axioms Complex.QuadraticLaplace.mellin_exp_neg_half_sq
#print axioms Complex.ofReal_sqrt_cpow
#print axioms Complex.one_div_two_cpow_neg
#print axioms AnalyticAt.ofReal_cpow
#print axioms Asymptotics.hasAsymptoticExpansion_gaussian_cpow
#print axioms Asymptotics.isBigO_ofReal_cpow_of_re_le
#print axioms DLMF.Confluent.KummerTransition.phase
#print axioms DLMF.Confluent.KummerTransition.quadraticFactor
#print axioms DLMF.Confluent.KummerTransition.coordinate
#print axioms DLMF.Confluent.KummerTransition.analyticAt_quadraticFactor
#print axioms DLMF.Confluent.KummerTransition.quadraticFactor_zero
#print axioms DLMF.Confluent.KummerTransition.hasDerivAt_quadraticFactor_zero
#print axioms DLMF.Confluent.KummerTransition.analyticAt_coordinate
#print axioms DLMF.Confluent.KummerTransition.hasDerivAt_coordinate_zero
#print axioms DLMF.Confluent.KummerTransition.phase_eq_sq_mul
#print axioms DLMF.Confluent.KummerTransition.exists_inverse
#print axioms DLMF.Confluent.KummerTransition.inverse_dslope_derivative
#print axioms DLMF.Confluent.KummerTransition.inverse_second_derivative
#print axioms DLMF.Confluent.KummerTransition.amplitude
#print axioms DLMF.Confluent.KummerTransition.amplitude_data
#print axioms DLMF.Confluent.KummerTransition.integral_substitution
#print axioms DLMF.Confluent.KummerTransition.exists_interval
#print axioms DLMF.Confluent.KummerTransition.hasDerivAt_phase
#print axioms DLMF.Confluent.KummerTransition.strictMonoOn_phase
#print axioms DLMF.Confluent.KummerTransition.phase_pos
#print axioms DLMF.Confluent.KummerTransition.integrableOn_weight
#print axioms DLMF.Confluent.KummerTransition.isBigO_tail
#print axioms DLMF.Confluent.KummerTransition.isBigO_tail_cpow
#print axioms DLMF.Confluent.KummerTransition.isBigO_local
#print axioms DLMF.Confluent.KummerTransition.kernel_eq
#print axioms DLMF.Confluent.KummerTransition.isBigO_integral_of_re_pos
#print axioms DLMF.Confluent.KummerTransition.leadingCoefficient
#print axioms DLMF.Confluent.KummerTransition.firstCorrection
#print axioms DLMF.Confluent.KummerTransition.approximation
#print axioms DLMF.Confluent.KummerTransition.leadingCoefficient_sub_one
#print axioms DLMF.Confluent.KummerTransition.firstCorrection_sub_one
#print axioms DLMF.Confluent.KummerTransition.integralCoefficient_leading
#print axioms DLMF.Confluent.KummerTransition.integralCoefficient_correction
#print axioms DLMF.Confluent.KummerTransition.isBigO_sub_approximation_of_re_pos
#print axioms DLMF.Confluent.KummerTransition.isBigO_kummerU_of_expansion
#print axioms DLMF.Confluent.KummerTransition.isBigO_sub_approximation_sub_one
#print axioms DLMF.Confluent.KummerTransition.approximation_eq
#print axioms DLMF.Confluent.kummerU_transition

#print axioms DLMF.Legendre.associatedP_large_order_uniform
#print axioms Real.inv_sq_sub_inv_sinh_sq_nonneg
#print axioms DLMF.Legendre.HyperbolicAssociatedP.perturbation
#print axioms DLMF.Legendre.HyperbolicAssociatedP.integrableOn_perturbation
#print axioms DLMF.Legendre.HyperbolicAssociatedP.continuousOn_perturbation
#print axioms DLMF.Legendre.HyperbolicAssociatedP.norm_perturbation
#print axioms DLMF.Legendre.HyperbolicAssociatedP.integral_norm_perturbation
#print axioms DLMF.Legendre.HyperbolicAssociatedP.potential_eq
#print axioms DLMF.Legendre.HyperbolicAssociatedP.coordinate_pos
#print axioms DLMF.Legendre.HyperbolicAssociatedP.coth_coordinate
#print axioms DLMF.Legendre.HyperbolicAssociatedP.normalization
#print axioms DLMF.Legendre.HyperbolicAssociatedP.normalization_ne_zero
#print axioms DLMF.Legendre.HyperbolicAssociatedP.normalization_mul_leading
#print axioms DLMF.Legendre.HyperbolicAssociatedP.norm_ratio_le
#print axioms DLMF.Legendre.HyperbolicAssociatedP.isBigO_associatedP_large_order

#print axioms DLMF.Legendre.ExteriorAddition.argument
#print axioms DLMF.Legendre.ExteriorAddition.domain
#print axioms DLMF.Legendre.ExteriorAddition.argument_eq_cos_sub_add
#print axioms DLMF.Legendre.ExteriorAddition.im_cos_mul_neg
#print axioms DLMF.Legendre.ExteriorAddition.im_argument_neg
#print axioms DLMF.Legendre.ExteriorAddition.isOpen_domain
#print axioms DLMF.Legendre.ExteriorAddition.convex_domain
#print axioms DLMF.Legendre.ExteriorAddition.cos_mul_sub_one_mem_slitPlane
#print axioms DLMF.Legendre.ExteriorAddition.argument_sub_one_mem_slitPlane
#print axioms DLMF.Legendre.ExteriorAddition.continuous_argument
#print axioms DLMF.Legendre.ExteriorAddition.differentiable_argument
#print axioms DLMF.Legendre.ExteriorAddition.differentiableOn_coefficient
#print axioms DLMF.Legendre.ExteriorAddition.differentiableOn_coefficient_associatedQ
#print axioms DLMF.Legendre.ExteriorAddition.localDomain
#print axioms DLMF.Legendre.ExteriorAddition.isOpen_localDomain
#print axioms DLMF.Legendre.ExteriorAddition.argument_mem_ball
#print axioms DLMF.Legendre.ExteriorAddition.ofReal_mem_localDomain
#print axioms DLMF.Legendre.ExteriorAddition.localCombination
#print axioms DLMF.Legendre.ExteriorAddition.argument_ofReal
#print axioms DLMF.Legendre.ExteriorAddition.coeff_localCombination_real
#print axioms DLMF.Legendre.ExteriorAddition.associatedQ_eq_localCombination
#print axioms DLMF.Legendre.ExteriorAddition.localDifference
#print axioms DLMF.Legendre.ExteriorAddition.difference
#print axioms DLMF.Legendre.ExteriorAddition.analyticOnNhd_localCombination
#print axioms DLMF.Legendre.ExteriorAddition.differentiableOn_localDifference
#print axioms DLMF.Legendre.ExteriorAddition.differentiableOn_difference
#print axioms DLMF.Legendre.ExteriorAddition.legendreQRegular_nat_order
#print axioms DLMF.Legendre.ExteriorAddition.difference_eq_localDifference
#print axioms DLMF.Legendre.ExteriorAddition.exists_ball_localDifference_zero
#print axioms DLMF.Legendre.ExteriorAddition.difference_eq_zero
#print axioms DLMF.Legendre.ExteriorAddition.exteriorDomain
#print axioms DLMF.Legendre.ExteriorAddition.isOpen_exteriorDomain
#print axioms DLMF.Legendre.ExteriorAddition.argument_re_gt_one
#print axioms DLMF.Legendre.ExteriorAddition.differentiableOn_difference_exterior
#print axioms DLMF.Legendre.ExteriorAddition.difference_mul_I_eq_zero
#print axioms DLMF.Legendre.ExteriorAddition.coefficient_associatedQ_hyperbolicArg
#print axioms DLMF.Legendre.ExteriorAddition.hyperbolicArg_gt_one
#print axioms DLMF.Legendre.ExteriorAddition.contDiff_associatedQ_hyperbolicArg
#print axioms DLMF.Legendre.ExteriorAddition.hasSum_addition
#print axioms DLMF.Legendre.associatedQ_addition

#print axioms Complex.cosh_div_sinh_sub_one_mem_slitPlane
#print axioms Complex.exp_mul_log_cosh_div_sinh_ratio

#print axioms DLMF.Confluent.KummerTransition.isBigO_sub_approximation
#print axioms DLMF.Gamma.GammaRatioNormalization.isBigO_mul_sub_two_term
#print axioms DLMF.Confluent.KummerTransition.phase_eq_sq_mul_near
#print axioms DLMF.Confluent.KummerTransition.eulerPhase
#print axioms DLMF.Confluent.KummerTransition.reflectedInverse
#print axioms DLMF.Confluent.KummerTransition.exists_euler_interval
#print axioms DLMF.Confluent.KummerTransition.euler_integral_substitution
#print axioms DLMF.Confluent.KummerTransition.euler_kernel_eq
#print axioms DLMF.Confluent.KummerTransition.integrableOn_euler_kernel
#print axioms DLMF.Confluent.KummerTransition.hasDerivAt_eulerPhase
#print axioms DLMF.Confluent.KummerTransition.strictMonoOn_eulerPhase
#print axioms DLMF.Confluent.KummerTransition.eulerPhase_pos
#print axioms DLMF.Confluent.KummerTransition.isBigO_euler_tail
#print axioms DLMF.Confluent.KummerTransition.isBigO_euler_local
#print axioms DLMF.Confluent.KummerTransition.isBigO_euler_integral_of_re_pos
#print axioms DLMF.Confluent.KummerTransition.eulerApproximation
#print axioms DLMF.Confluent.KummerTransition.isBigO_eulerApproximation
#print axioms DLMF.Confluent.KummerTransition.isBigO_kummerM_sub_one
#print axioms DLMF.Confluent.KummerTransition.reflected_approximation_eq
#print axioms DLMF.Confluent.KummerTransition.isBigO_kummerM_of_re_pos
#print axioms DLMF.Confluent.KummerTransition.isBigO_kummerM_all
#print axioms DLMF.Confluent.kummerM_transition
