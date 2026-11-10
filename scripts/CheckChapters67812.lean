/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF.ExpIntegrals
import DLMF.ErrorFunctions
import DLMF.IncompleteGamma
import DLMF.ParabolicCylinder
import DLMFMathlib

/-!
# Axiom audit for the chapter 6, 7, 8 and 12 proofs

The declarations below cover the closed admissions, their new support, and the independent
counterexamples to the three defective variants. Their proof dependencies must
contain no `sorryAx`; the chapter umbrellas still contain other, explicitly retained admissions.
-/

namespace DLMF.Confluent.Real

#print axioms abs_normalized_erfc_sub_one_le
#print axioms tendsto_normalized_erfc_atTop
#print axioms tendsto_neg_log_erfc_div_sq_atTop
#print axioms tendsto_invErfc_sq_div_neg_log
#print axioms tendsto_invErfc_div_sqrt_log
#print axioms tendsto_invErfc_nhdsGT_zero

end DLMF.Confluent.Real

namespace DLMF.Confluent.IncompleteBetaBarnes

#print axioms gammaKernel
#print axioms kummerKernel
#print axioms integrable_gammaKernel
#print axioms integrable_kummerKernel
#print axioms fourier_gammaKernel
#print axioms fourier_kummerKernel
#print axioms integrable_fourier_kummerKernel
#print axioms integral_kummerKernel_mul_gammaKernel
#print axioms integral_vertical

end DLMF.Confluent.IncompleteBetaBarnes

namespace DLMF.Confluent.IncompleteBetaUniform

#print axioms shiftedMoment
#print axioms translated_integrand
#print axioms integrable_shiftedMoment
#print axioms betaAuxF_eq_shiftedMoment
#print axioms nonneg_shiftedMoment
#print axioms shiftedMoment_half_rate
#print axioms shiftedMoment_le
#print axioms norm_betaAuxF
#print axioms norm_betaAuxF_le
#print axioms complexGeneratingKernel
#print axioms differentiableOn_complexGeneratingKernel
#print axioms complexGeneratingKernel_ofReal
#print axioms norm_complexGeneratingKernel_le
#print axioms norm_iteratedDeriv_complexGeneratingKernel_le
#print axioms exists_norm_iteratedDeriv_betaGeneratingKernel_le
#print axioms integral_beta_exp_substitution
#print axioms betaGeneratingKernel_weight_eq
#print axioms normalizedIncompleteBeta_eq_integral
#print axioms normalizedIncompleteBeta_eq_laplace_integral
#print axioms exists_betaGeneratingKernel_taylor_bound
#print axioms norm_integral_generatingKernel_sub_sum_le
#print axioms analyticAt_betaGeneratingKernel

end DLMF.Confluent.IncompleteBetaUniform

namespace DLMF.Confluent

#print axioms incompleteBeta_large_a_uniform_of_pos_order
#print axioms upperGammaIndentPV_eq_compact_add_tail
#print axioms differentiableOn_upperGammaIndentPV
#print axioms upperIncompleteGamma_indented_integral_ofReal
#print axioms gammaUniformAlpha_two
#print axioms gammaUniformC_maclaurin_zero
#print axioms gammaUniformD_zero_zero
#print axioms gammaUniformD_zero_succ
#print axioms pcfDescendingZero_eventually
#print axioms upperIncompleteGamma_indented_integral
#print axioms tricomiIncompleteGamma_two_parameter_zeros_negative_x

end DLMF.Confluent

namespace DLMF.Confluent.LaguerreSeries

#print axioms laguerrePolynomialL_neg_one_succ
#print axioms hasSum_laguerrePolynomialL_neg_one_one
#print axioms upperIncompleteGamma_neg_one_one_ne_exp_neg_one
#print axioms not_hasSum_laguerrePolynomialL_neg_one_one

end DLMF.Confluent.LaguerreSeries

namespace DLMF.Confluent.BetaUniformEndpoint

#print axioms normalizedIncompleteBeta_eq_integral
#print axioms div_le_integral_beta_half
#print axioms norm_betaAuxF_zero_le
#print axioms not_isBigO_normalizedIncompleteBeta_half
#print axioms not_incompleteBeta_large_a_uniform_zero

end DLMF.Confluent.BetaUniformEndpoint

namespace DLMF.Confluent.IncompleteGammaZeros

#print axioms unique_parameter_zero_negative_x
#print axioms existsUnique_parameter_zero_negative_x

end DLMF.Confluent.IncompleteGammaZeros

namespace DLMF.Confluent.CylinderRealZeros

#print axioms finite_zeros_Ioi
#print axioms finite_derivative_zeros_Ioi
#print axioms eventually_strictMono_positive_zeros
#print axioms eventually_strictMono_positive_derivative_zeros

end DLMF.Confluent.CylinderRealZeros

namespace Complex

#print axioms iteratedDeriv_comp_ofReal_of_differentiableOn
#print axioms iteratedDeriv_re_comp_ofReal_of_differentiableOn
#print axioms abs_le_norm_add_mul_I
#print axioms ofReal_add_mul_I_ne_zero
#print axioms integral_horizontal_inv_add_mul_I
#print axioms tendsto_integral_inv_add_mul_I
#print axioms tendsto_integral_inv_add_sign_mul_I
#print axioms norm_div_sub_add_mul_I_le
#print axioms exponentialDifferenceQuotient
#print axioms continuous_exponentialDifferenceQuotient
#print axioms exponentialDifferenceQuotient_eq
#print axioms negativeAxisApproach
#print axioms tendsto_negativeAxisApproach
#print axioms tendsto_log_negativeAxisApproach
#print axioms negativeAxisApproach_mem_slitPlane
#print axioms integral_cpow_mul_exp_neg_div_negativeAxisApproach

end Complex

namespace MeasureTheory

#print axioms tendsto_intervalIntegral_sub_div_add_mul_I
#print axioms tendsto_intervalIntegral_div_add_mul_I
#print axioms tendsto_intervalIntegral_div_add_sign_mul_I
#print axioms integrableOn_Ioi_div_sub_add_mul_I
#print axioms tendsto_integral_Ioi_div_sub_add_mul_I
#print axioms tendsto_integral_Ioi_div_sub_add_sign_mul_I
#print axioms integral_comp_exp_neg_Ioi
#print axioms integrableOn_comp_exp_neg_Ioi

end MeasureTheory

namespace DLMF.Confluent.UpperGammaPrincipalValue

#print axioms integrableOn_compactIntegrand
#print axioms differentiable_compactIntegral
#print axioms integrableOn_tailIntegrand
#print axioms differentiableOn_tailIntegral
#print axioms upperIncompleteGammaOnLog_eq_of_tendsto

end DLMF.Confluent.UpperGammaPrincipalValue

namespace DLMF.Confluent.IncompleteGammaUniform

#print axioms gammaUniformC_zero_comp_eq_dslope
#print axioms differentiableOn_gammaUniformC_zero_comp

end DLMF.Confluent.IncompleteGammaUniform

namespace DLMF.Confluent.RotationalAdditionEndpoint

#print axioms evenTerm
#print axioms parameter_step
#print axioms evenTerm_zero
#print axioms initial_ne_zero
#print axioms evenTerm_recurrence
#print axioms initial_norm_le
#print axioms not_summable_evenTerm
#print axioms not_summable_endpoint
#print axioms not_hasSum_rotational_addition_endpoint

end DLMF.Confluent.RotationalAdditionEndpoint

namespace Real

#print axioms pow_mul_exp_neg_le_mul_exp_neg_half
#print axioms rpow_add_two_mul_le

end Real

namespace DLMF.Statistical

#print axioms incompleteBeta_large_a_uniform

#print axioms regularizedIncompleteBeta_mellinBarnes

end DLMF.Statistical

