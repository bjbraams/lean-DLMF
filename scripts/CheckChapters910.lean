/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF.Airy
import DLMF.Bessel

/-!
# Axiom audit for Chapter 9 and 10 proofs

The closed admissions and their support must depend only on standard axioms, with no
`sorryAx`. The chapter umbrellas also contain explicitly retained admissions.
-/

#print axioms DLMF.Airy.airyAi_stieltjes
#print axioms DLMF.Airy.airyBi_complex_zeros_sector
#print axioms DLMF.Airy.airyBiDeriv_complex_zeros_sector
#print axioms DLMF.Airy.ComplexBiZeros.energy_identity
#print axioms DLMF.Airy.ComplexBiZeros.zero_re_pos_and_im_sq
#print axioms DLMF.Airy.ComplexBiZeros.zero_sector
#print axioms DLMF.Airy.StieltjesRepresentation.normalization
#print axioms DLMF.Airy.StieltjesRepresentation.airyAi_eq_tricomi
#print axioms DLMF.Airy.StieltjesRepresentation.two_zeta_mem_slitPlane
#print axioms DLMF.Airy.StieltjesRepresentation.normalization_mul_tricomi
#print axioms DLMF.Airy.StieltjesRepresentation.transformed_kernel
#print axioms DLMF.Airy.StieltjesRepresentation.tricomiKernel
#print axioms DLMF.Airy.StieltjesRepresentation.airyKernel
#print axioms DLMF.Airy.StieltjesRepresentation.integral_kernel_transform
#print axioms DLMF.Airy.StieltjesRepresentation.gamma_sixth_mul_five_sixths
#print axioms DLMF.Airy.StieltjesRepresentation.kummerU_eq_stieltjes
#print axioms DLMF.Airy.StieltjesRepresentation.cpow_normalization
#print axioms DLMF.Confluent.hasAsymptoticExpansion_regularizedConfluent_sector_of_re_pos
#print axioms DLMF.Confluent.tendsto_regularizedHGFun_mul_exp_neg_sector
#print axioms DLMF.Bessel.besselI_eq_mul_regularizedConfluent_of_mem_slitPlane
#print axioms DLMF.Bessel.besselI_main_term_of_ne_zero
#print axioms DLMF.Bessel.besselI_isEquivalent_sector
#print axioms DLMF.Airy.tendsto_norm_generalizedAiryZeta
#print axioms DLMF.Airy.tendsto_generalizedAiryZeta_sector
#print axioms DLMF.Airy.generalizedAiry_besselI_sector
#print axioms DLMF.Airy.generalizedAiryA_isLittleO_generalizedAiryB
#print axioms DLMF.Airy.tendsto_ofReal_mul_airySector
#print axioms DLMF.Airy.olverAiry_rotated_recessive
#print axioms DLMF.Airy.airyAi_fourth_integral
#print axioms DLMF.Airy.AiSquare.mellinValue
#print axioms DLMF.Airy.AiSquare.mellin_eq_value
#print axioms DLMF.Airy.AiSquare.mellinValue_mul_mellinValue_one_sub
#print axioms DLMF.Airy.AiSquare.mellinValue_half_mul_reflected
#print axioms DLMF.Airy.AiSquare.norm_mellinValue_half
#print axioms DLMF.Airy.AiSquare.integrable_mellinValue_half
#print axioms Real.sinh_div_three_div_cosh_eq_tanh_sub
#print axioms Real.tendsto_tanh_atTop
#print axioms Real.integrable_sinh_div_three_div_mul_cosh
#print axioms Real.integral_sinh_div_three_div_mul_cosh
#print axioms DLMF.Bessel.besselI_sub_main_isBigO_sector
#print axioms DLMF.Airy.generalizedAiry_dominant_factor
#print axioms DLMF.Airy.generalizedAiryB_asymptotic
#print axioms DLMF.Airy.generalizedAiryA_negative_even_asymptotic
#print axioms DLMF.Airy.scorerHi_mellinBarnes
#print axioms DLMF.Airy.ScorerMellin.rotation_parameters
#print axioms DLMF.Airy.ScorerMellin.phase_factor
#print axioms DLMF.Airy.ScorerMellin.scorerHi_eq_rotated
#print axioms Complex.CubicLaplace.integral_cpow_mul_exp_neg_mul_cube
#print axioms Complex.CubicLaplace.integrableOn_cpow_mul_exp_neg_mul_cube
#print axioms Complex.CubicLaplace.mellin_exp_neg_mul_cube
#print axioms Complex.CubicLaplace.mellinConvergent_exp_neg_mul_cube
#print axioms Complex.CubicLaplace.mellinConvergent_exp_neg_mul
#print axioms Complex.CubicLaplace.mellin_exp_neg_mul
#print axioms Complex.CubicLaplace.norm_mellin_exp_neg_mul_cube_le
