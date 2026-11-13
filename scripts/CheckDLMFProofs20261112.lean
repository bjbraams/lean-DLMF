/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF
import DLMFMathlib

/-!
# Axiom audit for the DLMF proofs with updated dependencies

The completed proofs and their supporting APIs must use only Lean's standard axioms.
Other declarations in the library retain their explicit admissions.
-/

#print axioms DLMF.Combinatorics.staysAbove_cons
#print axioms DLMF.Combinatorics.MotzkinPaths.count
#print axioms DLMF.Combinatorics.MotzkinPaths.count_def
#print axioms DLMF.Combinatorics.MotzkinPaths.count_of_lt
#print axioms DLMF.Combinatorics.MotzkinPaths.count_zero
#print axioms DLMF.Combinatorics.MotzkinPaths.count_succ
#print axioms DLMF.Combinatorics.MotzkinPaths.count_succ_zero
#print axioms DLMF.Combinatorics.MotzkinPaths.count_succ_succ
#print axioms DLMF.Combinatorics.MotzkinPaths.count_self
#print axioms DLMF.Combinatorics.MotzkinPaths.latticeCount
#print axioms DLMF.Combinatorics.MotzkinPaths.latticeCount_def
#print axioms DLMF.Combinatorics.MotzkinPaths.latticeCount_of_neg
#print axioms DLMF.Combinatorics.MotzkinPaths.latticeCount_zero_zero
#print axioms DLMF.Combinatorics.MotzkinPaths.latticeCount_eq_sum
#print axioms DLMF.Combinatorics.MotzkinPaths.latticeCount_eq_count
#print axioms DLMF.Combinatorics.MotzkinPaths.count_zero_eq_sum
#print axioms DLMF.Combinatorics.card_latticePaths_above_eq_motzkin
#print axioms DLMF.Combinatorics.numPeaks
#print axioms DLMF.Combinatorics.numPeaks_def
#print axioms DLMF.Combinatorics.NarayanaPaths.step
#print axioms DLMF.Combinatorics.NarayanaPaths.readStep
#print axioms DLMF.Combinatorics.NarayanaPaths.readStep_step
#print axioms DLMF.Combinatorics.NarayanaPaths.step_readStep
#print axioms DLMF.Combinatorics.NarayanaPaths.sum_map_step
#print axioms DLMF.Combinatorics.NarayanaPaths.map_step_readStep
#print axioms DLMF.Combinatorics.NarayanaPaths.toLattice
#print axioms DLMF.Combinatorics.NarayanaPaths.toLattice_zero
#print axioms DLMF.Combinatorics.NarayanaPaths.mem_latticePaths_toLattice
#print axioms DLMF.Combinatorics.NarayanaPaths.staysWeaklyAboveDiagonal_toLattice
#print axioms DLMF.Combinatorics.NarayanaPaths.ofLattice
#print axioms DLMF.Combinatorics.NarayanaPaths.semilength_ofLattice
#print axioms DLMF.Combinatorics.NarayanaPaths.toLattice_ofLattice
#print axioms DLMF.Combinatorics.NarayanaPaths.ofLattice_toLattice
#print axioms DLMF.Combinatorics.NarayanaPaths.numPeaks_nil
#print axioms DLMF.Combinatorics.NarayanaPaths.numPeaks_cons_cons
#print axioms DLMF.Combinatorics.NarayanaPaths.numPeaks_down_cons
#print axioms DLMF.Combinatorics.NarayanaPaths.numPeaks_append_down
#print axioms DLMF.Combinatorics.NarayanaPaths.treePath
#print axioms DLMF.Combinatorics.NarayanaPaths.treePath_nil
#print axioms DLMF.Combinatorics.NarayanaPaths.treePath_node
#print axioms DLMF.Combinatorics.NarayanaPaths.toLattice_add
#print axioms DLMF.Combinatorics.NarayanaPaths.toLattice_nest
#print axioms DLMF.Combinatorics.NarayanaPaths.exists_toLattice_eq_up_append_down
#print axioms DLMF.Combinatorics.NarayanaPaths.numPeaks_toLattice_add
#print axioms DLMF.Combinatorics.NarayanaPaths.numPeaks_toLattice_nest
#print axioms DLMF.Combinatorics.NarayanaPaths.blockPolynomial
#print axioms DLMF.Combinatorics.NarayanaPaths.blockPolynomial_of_card_eq
#print axioms DLMF.Combinatorics.NarayanaPaths.blockPolynomial_empty
#print axioms DLMF.Combinatorics.NarayanaPaths.blockPolynomial_first_part
#print axioms DLMF.Combinatorics.NarayanaPaths.blockPolynomial_eq_sum
#print axioms DLMF.Combinatorics.NarayanaPaths.numPeaks_treePath_node
#print axioms DLMF.Combinatorics.NarayanaPaths.treePolynomial
#print axioms DLMF.Combinatorics.NarayanaPaths.treePolynomial_zero
#print axioms DLMF.Combinatorics.NarayanaPaths.treeWeight_node
#print axioms DLMF.Combinatorics.NarayanaPaths.treePolynomial_succ
#print axioms DLMF.Combinatorics.NarayanaPaths.treePolynomial_eq_blockPolynomial
#print axioms DLMF.Combinatorics.NarayanaPaths.coeff_treePolynomial
#print axioms DLMF.Combinatorics.NarayanaPaths.coeff_blockPolynomial
#print axioms DLMF.Combinatorics.NarayanaPaths.card_treePath_peaks
#print axioms DLMF.Combinatorics.NarayanaPaths.dyckEquiv
#print axioms DLMF.Combinatorics.NarayanaPaths.treeEquiv
#print axioms DLMF.Combinatorics.NarayanaPaths.treePath_treeEquiv
#print axioms DLMF.Combinatorics.NarayanaPaths.card_latticePaths_peaks_eq_card_treePath_peaks
#print axioms DLMF.Combinatorics.NarayanaPaths.card_latticePaths_peaks
#print axioms DLMF.Combinatorics.NarayanaPaths.step_def
#print axioms DLMF.Combinatorics.NarayanaPaths.readStep_def
#print axioms DLMF.Combinatorics.NarayanaPaths.toLattice_def
#print axioms DLMF.Combinatorics.NarayanaPaths.ofLattice_toList
#print axioms DLMF.Combinatorics.NarayanaPaths.treePath_def
#print axioms DLMF.Combinatorics.NarayanaPaths.blockPolynomial_def
#print axioms DLMF.Combinatorics.NarayanaPaths.treePolynomial_def
#print axioms DLMF.Combinatorics.NarayanaPaths.dyckEquiv_apply
#print axioms DLMF.Combinatorics.NarayanaPaths.treeEquiv_def
#print axioms DLMF.Combinatorics.card_latticePaths_peaks_eq_narayana
#print axioms DLMF.JacobiElliptic.FourPointAddition.det_two_K_sn_polynomial
#print axioms DLMF.JacobiElliptic.FourPointAddition.det_two_K_cn_polynomial
#print axioms DLMF.JacobiElliptic.FourPointAddition.det_two_K_of_additionDenominators_ne_zero
#print axioms DLMF.JacobiElliptic.FourPointAddition.det_two_K_thetaMatrix_eq_prod_mul_det
#print axioms DLMF.JacobiElliptic.FourPointAddition.det_two_K_eq_zero
#print axioms DLMF.JacobiElliptic.jacobi_det_sum_two_K
#print axioms DLMF.JacobiElliptic.jacobi_det_sum_two_K'
#print axioms MeasureTheory.pv_tendsto_of_integrableOn_sub_of_tendsto_ratio
#print axioms HasDerivAt.tendsto_left_right_increment_ratio
#print axioms intervalIntegral.integral_deriv_rpow_smul_comp_of_nonneg
#print axioms MeasureTheory.pv_tendsto_rpow_div_sub
#print axioms Complex.ofReal_add_mul_I_ne_zero_of_im_ne_zero
#print axioms DLMF.Bessel.besselJ_sub_cos_mul_sqrt_tendsto_zero
#print axioms DLMF.CoalescingSaddles.cuspoidIntegral_two_zero_atBot
#print axioms ContDiffAt.isBigO_sub_sum_iteratedFDeriv
#print axioms ContDiffAt.isLittleO_sub_sum_iteratedFDeriv
#print axioms DLMF.AlgebraicAnalytic.taylor_isLittleO_prod
#print axioms MeasureTheory.IntegrableOn.hasDerivAt_integral_Ioi
#print axioms MeasureTheory.Lp.integral_norm_sq_eq_norm_sq
#print axioms MeasureTheory.MemLp.integral_norm_sq_eq_norm_toLp_sq
#print axioms DLMF.Airy.BiStieltjes.integrableOn_density
#print axioms DLMF.Airy.BiStieltjes.differentiableAt_density
#print axioms DLMF.Airy.BiStieltjes.integrableOn_scaledDensity
#print axioms DLMF.Airy.BiStieltjes.differentiableAt_scaledDensity
#print axioms DLMF.Airy.BiStieltjes.integral_scaledDensity_div_add
#print axioms DLMF.Airy.BiStieltjes.kummerU_eq_scaled_stieltjes
#print axioms DLMF.Airy.BiStieltjes.airyArgument_spec
#print axioms DLMF.Airy.BiStieltjes.airyAi_eq_scaled_stieltjes
#print axioms DLMF.Airy.BiStieltjes.density_change_variable
#print axioms DLMF.Airy.BiStieltjes.jacobianKernel_eq
#print axioms DLMF.Airy.BiStieltjes.finitePart_relation
#print axioms DLMF.Airy.PrincipalValue.tail_integrableOn
#print axioms sub_isLittleO_norm_rpow_add_one_of_fderiv
#print axioms ContDiffAt.isLittleO_sub_taylor_two
#print axioms ContDiffAt.isLocalMin_of_fderiv_eq_zero_of_le_secondFDeriv
#print axioms ContDiffAt.isLocalMin_of_fderiv_eq_zero_of_pos_secondFDeriv
#print axioms DLMF.Theta.GaussReciprocity.jacobiTheta_rational_add
#print axioms DLMF.Theta.GaussReciprocity.tendsto_jacobiTheta₂_real_shift
#print axioms DLMF.Theta.GaussReciprocity.sqrt_mul_jacobiTheta_rational_add_I_mul
#print axioms DLMF.Theta.GaussReciprocity.tendsto_sqrt_mul_jacobiTheta_rational
#print axioms DLMF.Theta.GaussReciprocity.sqrt_mul_jacobiTheta_inversion_eq_sum
#print axioms DLMF.Theta.GaussReciprocity.sum_reciprocity
#print axioms DLMF.Theta.thetaGaussSum_reciprocity'
#print axioms DLMF.Theta.thetaGaussSum_reciprocity
#print axioms DLMF.Combinatorics.MultisetWords.words
#print axioms DLMF.Combinatorics.MultisetWords.mem_words
#print axioms DLMF.Combinatorics.MultisetWords.inversions
#print axioms DLMF.Combinatorics.MultisetWords.inversions_nil
#print axioms DLMF.Combinatorics.MultisetWords.inversions_cons
#print axioms DLMF.Combinatorics.MultisetWords.words_zero
#print axioms DLMF.Combinatorics.MultisetWords.words_eq_biUnion
#print axioms DLMF.Combinatorics.MultisetWords.enumerator
#print axioms DLMF.Combinatorics.MultisetWords.lowerCount
#print axioms DLMF.Combinatorics.MultisetWords.countP_lt_of_cons_eq
#print axioms DLMF.Combinatorics.MultisetWords.enumerator_zero
#print axioms DLMF.Combinatorics.MultisetWords.enumerator_eq_sum
#print axioms DLMF.Combinatorics.MultisetWords.factorialProduct
#print axioms DLMF.Combinatorics.MultisetWords.factorialProduct_erase
#print axioms DLMF.Combinatorics.MultisetWords.lowerCount_eq_sum
#print axioms DLMF.Combinatorics.MultisetWords.sum_pow_lowerCount_mul_one_sub_pow_count
#print axioms DLMF.Combinatorics.MultisetWords.enumerator_mul_factorialProduct_of_card
#print axioms DLMF.Combinatorics.MultisetWords.enumerator_mul_factorialProduct
#print axioms DLMF.Combinatorics.MultisetWords.qMultinomial_succ
#print axioms DLMF.Combinatorics.MultisetWords.qMultinomial_mul_factorialProduct
#print axioms DLMF.Combinatorics.MultisetWords.content
#print axioms DLMF.Combinatorics.MultisetWords.count_content
#print axioms DLMF.Combinatorics.MultisetWords.card_content
#print axioms DLMF.Combinatorics.MultisetWords.factorialProduct_content
#print axioms DLMF.Combinatorics.MultisetWords.factorialProduct_ne_zero
#print axioms DLMF.Combinatorics.MultisetWords.enumerator_content_of_norm_ne_one
#print axioms DLMF.Combinatorics.MultisetWords.continuous_enumerator
#print axioms DLMF.Combinatorics.MultisetWords.continuous_qMultinomial
#print axioms DLMF.Combinatorics.MultisetWords.enumerator_content
#print axioms DLMF.Combinatorics.MultisetWords.mem_words_content_ofFn
#print axioms DLMF.Combinatorics.MultisetWords.exists_ofFn_eq_of_mem_words_content
#print axioms DLMF.Combinatorics.MultisetWords.inversions_ofFn
#print axioms DLMF.Combinatorics.MultisetWords.sum_pow_wordInversions
#print axioms DLMF.Combinatorics.MultisetWords.inversions_def
#print axioms DLMF.Combinatorics.MultisetWords.enumerator_def
#print axioms DLMF.Combinatorics.MultisetWords.lowerCount_def
#print axioms DLMF.Combinatorics.MultisetWords.factorialProduct_def
#print axioms DLMF.Combinatorics.MultisetWords.content_eq_iff
#print axioms DLMF.Combinatorics.multisetPermutations
#print axioms DLMF.Combinatorics.multisetPermutations_def
#print axioms DLMF.Combinatorics.mem_multisetPermutations
#print axioms DLMF.Combinatorics.sum_pow_wordInversions_multisetPermutations
#print axioms DLMF.Airy.BiStieltjes.tendsto_scaled_stieltjes
#print axioms DLMF.Airy.BiStieltjes.tendsto_airyArgument
#print axioms DLMF.Airy.BiStieltjes.tendsto_stieltjesPrefactor
#print axioms DLMF.Airy.BiStieltjes.airyAi_rotated_eq_finitePart
#print axioms DLMF.Airy.BiStieltjes.airyBi_eq_finitePart
#print axioms DLMF.Airy.BiStieltjes.stieltjesPrefactor_normalization
#print axioms DLMF.Airy.BiStieltjes.airyBi_eq_principalValue
#print axioms DLMF.Airy.airyBi_stieltjes_principalValue
#print axioms Complex.tendsto_cpow_negativeAxisApproach

#print axioms DLMF.AlgebraicAnalytic.isLocalMin_of_hessian_posDef
#print axioms DLMF.AlgebraicAnalytic.isLocalMax_of_hessian_negDef
#print axioms DLMF.Bessel.verticalIntegrable_mellin_besselK
#print axioms mellinConvergent_one_div_one_add_sq
#print axioms mellin_one_div_one_add_sq
#print axioms mellinConvergent_one_div_sq_add_sq
#print axioms mellin_one_div_sq_add_sq
#print axioms ContDiffAt.deriv_comp_curve
#print axioms Complex.deriv_comp_three
#print axioms Complex.deriv_coord_three
#print axioms DifferentiableAt.hasDerivAt_section_fst
#print axioms DifferentiableAt.hasDerivAt_section_snd
#print axioms ContDiffAt.deriv_deriv_section_fst
#print axioms ContDiffAt.deriv_deriv_section_snd
#print axioms ContDiffAt.deriv_deriv_section_snd_fst
#print axioms ContDiffAt.deriv_deriv_section_fst_snd

#print axioms DLMF.AlgebraicAnalytic.laplacian_polar

#print axioms DLMF.AlgebraicAnalytic.laplacian_cylindrical

#print axioms ContDiffAt.secondFDeriv_polar

#print axioms DLMF.AlgebraicAnalytic.harmonic_polar

#print axioms DLMF.JacobiElliptic.Real.jacobiEpsilon_eq_theta
#print axioms DLMF.JacobiElliptic.Real.hasDerivAt_jacobiEpsilon
#print axioms DLMF.JacobiElliptic.Real.incompleteEllipticEOfParameter_jacobiAmOfParameter
#print axioms DLMF.JacobiElliptic.Real.jacobiEpsilon_add_two_completeEllipticKOfParameter
#print axioms DLMF.JacobiElliptic.EpsilonTheta.thetaFour_second_relation
#print axioms DLMF.JacobiElliptic.EpsilonTheta.hasDerivAt_thetaFour_logDeriv
#print axioms DLMF.JacobiElliptic.EpsilonTheta.hasDerivAt_normalized_thetaFour_logDeriv
#print axioms DLMF.JacobiElliptic.EpsilonTheta.epsilon_eq_theta
#print axioms DLMF.JacobiElliptic.EpsilonTheta.thetaFour_second_deriv_zero_div_eq
#print axioms DLMF.Theta.jacobiThetaFourTau_logDeriv_deriv_hasSum
#print axioms DLMF.JacobiElliptic.jacobiSn_sq_hasSum_fourier
#print axioms DLMF.Combinatorics.MultisetWords.listMajorIndex
#print axioms DLMF.Combinatorics.MultisetWords.listMajorIndex_nil
#print axioms DLMF.Combinatorics.MultisetWords.listMajorIndex_singleton
#print axioms DLMF.Combinatorics.MultisetWords.listMajorIndex_snoc_snoc
#print axioms DLMF.Combinatorics.MultisetWords.words_eq_snoc_biUnion
#print axioms DLMF.Combinatorics.MultisetWords.greaterCount
#print axioms DLMF.Combinatorics.MultisetWords.greaterCount_eq_sum
#print axioms DLMF.Combinatorics.MultisetWords.sum_pow_greaterCount_mul_one_sub_pow_count
#print axioms DLMF.Combinatorics.MultisetWords.sum_pow_greaterCount_filter_mul_one_sub_pow_count
#print axioms DLMF.Combinatorics.MultisetWords.sum_pow_greaterCount_mul_boundary
#print axioms DLMF.Combinatorics.MultisetWords.boundaryEnumerator
#print axioms DLMF.Combinatorics.MultisetWords.boundaryEnumerator_zero
#print axioms DLMF.Combinatorics.MultisetWords.boundaryEnumerator_eq_sum
#print axioms DLMF.Combinatorics.MultisetWords.greaterCount_erase_self
#print axioms DLMF.Combinatorics.MultisetWords.boundaryEnumerator_mul_factorialProduct_of_card
#print axioms DLMF.Combinatorics.MultisetWords.boundaryEnumerator_mul_factorialProduct
#print axioms DLMF.Combinatorics.MultisetWords.listMajorIndex_append_of_forall_le
#print axioms DLMF.Combinatorics.MultisetWords.majorIndexEnumerator
#print axioms DLMF.Combinatorics.MultisetWords.majorIndexEnumerator_eq_boundaryEnumerator
#print axioms DLMF.Combinatorics.MultisetWords.greaterCount_card_alphabet
#print axioms DLMF.Combinatorics.MultisetWords.majorIndexEnumerator_mul_factorialProduct
#print axioms DLMF.Combinatorics.MultisetWords.majorIndexEnumerator_content_of_norm_ne_one
#print axioms DLMF.Combinatorics.MultisetWords.continuous_majorIndexEnumerator
#print axioms DLMF.Combinatorics.MultisetWords.majorIndexEnumerator_content
#print axioms DLMF.Combinatorics.MultisetWords.listMajorIndex_map_ofFn
#print axioms DLMF.Combinatorics.MultisetWords.sum_pow_wordMajorIndex
#print axioms DLMF.Combinatorics.MultisetWords.listMajorIndex_def
#print axioms DLMF.Combinatorics.MultisetWords.greaterCount_def
#print axioms DLMF.Combinatorics.MultisetWords.boundaryEnumerator_def
#print axioms DLMF.Combinatorics.MultisetWords.majorIndexEnumerator_def
#print axioms DLMF.Combinatorics.sum_pow_wordMajorIndex_multisetPermutations
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized_def
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized_zero_right
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized_zero_left
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized_succ_succ
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized_one
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized_le_harmonic_pow
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.harmonic_pow_sub_le_normalized
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.normalized_div_bounds
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.tendsto_normalized_div_harmonic_pow
#print axioms DLMF.Combinatorics.StirlingFirstEstimates.tendsto_normalized_div_log_add_constant_pow
#print axioms DLMF.Combinatorics.tendsto_signedStirlingFirst_div
#print axioms DLMF.Combinatorics.stirlingSecond_add_bounds
#print axioms DLMF.Combinatorics.stirlingSecond_add_div_bounds
#print axioms DLMF.Combinatorics.tendsto_stirlingSecond_add_div
#print axioms Complex.sq_re_le_norm_sq_add_sq
#print axioms MeasureTheory.differentiableOn_integral_div_sq_add_sq
#print axioms DLMF.Airy.ScorerStieltjes.airy_scale_cpow
#print axioms DLMF.Airy.ScorerStieltjes.mellin_factor_identity
#print axioms DLMF.Airy.ScorerStieltjes.scorerHi_stieltjes_positive
#print axioms DLMF.Airy.scorerHi_stieltjes_integral

#print axioms DLMF.AlgebraicAnalytic.laplacian_spherical

#print axioms LinearPMap.isOpen_setOf_exists_pos_mul_norm_le_smul_sub

#print axioms IsSelfAdjoint.denseRange_smul_sub_of_injective

#print axioms DLMF.AlgebraicAnalytic.IsSelfAdjoint.operatorSpectrum_real

#print axioms Complex.integral_exp_div_cosh_mul

#print axioms DLMF.AlgebraicAnalytic.fourierTransform_cosh_div_cosh

#print axioms DLMF.JacobiElliptic.jacobiSn_sq_hasSum_sech
#print axioms DLMF.JacobiElliptic.SquaredSnHyperbolic.eta_one_div_add_e_three_eq
#print axioms MeasureTheory.cauchy_finitePart_div_add
#print axioms MeasureTheory.tendsto_integral_Ioi_div_quadratic_sign_mul_I
#print axioms MeasureTheory.pv_tendsto_div_sq_sub_sq
#print axioms DLMF.Airy.ScorerStieltjes.inverseAiry_spec
#print axioms DLMF.Airy.ScorerStieltjes.inverseAiry_imaginary
#print axioms DLMF.Airy.ScorerStieltjes.principalValue_besselK_eq_neg_finitePart
#print axioms DLMF.Airy.ScorerStieltjes.scorerHi_boundary_eq_finitePart
#print axioms DLMF.Airy.ScorerStieltjes.scorerGi_eq_neg_finitePart
#print axioms DLMF.Airy.scorerGi_principalValue
#print axioms Polynomial.sign_coeff_zero_eq_neg_one_pow_signVariations_mul_sign_leadingCoeff
#print axioms Polynomial.coeffList_X_mul
#print axioms Polynomial.signVariations_X_mul
#print axioms Polynomial.sign_coeff_zero_eq_sign_leadingCoeff_of_no_pos_root
#print axioms Polynomial.neg_one_pow_signVariations_X_sub_C_mul
#print axioms Polynomial.neg_one_pow_signVariations_eq_neg_one_pow_countP_pos
#print axioms Polynomial.even_signVariations_sub_countP_pos
#print axioms DLMF.AlgebraicAnalytic.signVariations_sub_countP_pos_even
#print axioms DLMF.AlgebraicAnalytic.surfaceArea_comp_diffeomorph
#print axioms DLMF.AlgebraicAnalytic.fluxIntegral_comp_diffeomorph

#print axioms DLMF.AlgebraicAnalytic.fourierSinTransform_rpow_neg_three_halves

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_inv_sqrt

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierTransform_exp_sq

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierTransform_sin_cos_sq

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierTransform_sin_sq

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierTransform_cos_sq

#print axioms Complex.integral_symm_mul_exp_mul_I

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierCosTransform_sin_sq

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierCosTransform_cos_sq

#print axioms DLMF.AlgebraicAnalytic.tangentU_eq_fderiv
#print axioms DLMF.AlgebraicAnalytic.tangentV_eq_fderiv
#print axioms DLMF.AlgebraicAnalytic.fluxIntegral_curl_eq_lineIntegral
#print axioms Matrix.summable_principalMinor_of_summable_norm
#print axioms Matrix.det_one_add_submatrix_eq_sum_principalMinor
#print axioms Matrix.tendsto_det_one_add_submatrix_of_summable_norm
#print axioms DLMF.AlgebraicAnalytic.IsHillType.exists_hasInfiniteDet
#print axioms Real.inv_cosh_mul_isBigO_abs_rpow
#print axioms Real.summable_nat_pow_div_cosh_mul
#print axioms Complex.fourier_inv_cosh_mul
#print axioms Complex.tsum_inv_cosh_add_two_pi_mul
#print axioms Real.tsum_inv_cosh_add_two_pi_mul
#print axioms Real.hasSum_exp_div_exp_sub_one_eq_cosh_sum
#print axioms Real.summable_inv_cosh_nat_mul_add
#print axioms Real.tsum_inv_cosh_add_int_mul
#print axioms Real.hasSum_cosh_div_exp_sub_one_periodization
#print axioms Real.summable_abs_weighted_coshSeries
#print axioms Real.hasSum_tsum_mul_cosh
#print axioms Real.hasSum_tsum_mul_cos
#print axioms RCLike.eq_zero_of_hasSum_mul_pow_ball
#print axioms RCLike.eq_of_hasSum_mul_pow_ball
#print axioms RCLike.eq_of_hasSum_mul_pow_mul_ball
#print axioms Real.inv_cosh_add_lambert_eq_cos_sum
#print axioms DLMF.BernoulliEuler.eulerNumber_two_mul_eq_series

#print axioms DLMF.Weierstrass.weierstrassSigma_eq_exp_sum
#print axioms DLMF.Weierstrass.summable_logarithmicLatticeSeries
#print axioms DLMF.Theta.thetaDelta_two_eq_two_eta_one
#print axioms DLMF.Theta.G_eq_thetaDelta
#print axioms DLMF.Theta.sumInvPow_eq_shifted_lattice
#print axioms DLMF.Theta.LogarithmicTheta.thetaLatticeMinNorm_pos
#print axioms DLMF.Theta.LogarithmicTheta.summable_norm_shiftedLatticeLogSeries
#print axioms DLMF.Theta.LogarithmicTheta.analyticOnNhd_shiftedLatticeLogSeries
#print axioms DLMF.Theta.LogarithmicTheta.thetaTwo_powerSeries_of_lattice_relation
#print axioms DLMF.Theta.LogarithmicTheta.thetaThree_powerSeries_of_lattice_relation
#print axioms DLMF.Theta.LogarithmicTheta.thetaFour_powerSeries_of_lattice_relation
#print axioms DLMF.Theta.thetaGamma_eq_thetaDelta_sub
#print axioms DLMF.Theta.thetaBeta_eq_thetaAlpha_sub
#print axioms DLMF.Theta.two_mul_jacobiThetaOneTau_mul_jacobiThetaFourTau_two_mul
#print axioms DLMF.Theta.two_mul_jacobiThetaTwoTau_mul_jacobiThetaThreeTau_two_mul
#print axioms DLMF.Theta.jacobiThetaOneTau_powerSeries
#print axioms DLMF.Theta.jacobiThetaTwoTau_powerSeries
#print axioms DLMF.Theta.jacobiThetaThreeTau_powerSeries
#print axioms DLMF.Theta.jacobiThetaFourTau_powerSeries
#print axioms DLMF.AlgebraicAnalytic.vanVleck_arg_convs
#print axioms DLMF.AlgebraicAnalytic.vanVleck_arg_limit
#print axioms DLMF.AlgebraicAnalytic.cosEigenfunction_hilbertBasis

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_sin_div

#print axioms Real.tendsto_integral_Ioi_exp_mul_sin_of_bounded_antiderivative

#print axioms DLMF.AlgebraicAnalytic.tendsto_fourierSinTransform_arctan_abel

#print axioms MeasureTheory.integrableOn_Ioi_cut_div_sub

#print axioms MeasureTheory.pv_tendsto_setIntegral_Ioi_div_sub

#print axioms MeasureTheory.tendsto_setIntegral_Ioi_cut

#print axioms DLMF.AlgebraicAnalytic.tendsto_mellin_inv_one_sub_pv

#print axioms Complex.norm_exp_sub_mul_abs_le

#print axioms Complex.integrable_exp_sub_mul_abs

#print axioms Complex.integral_exp_sub_mul_abs

#print axioms mellin_log_abs_one_add_div_one_sub

#print axioms DLMF.AlgebraicAnalytic.mellin_log_abs_one_add_div_one_sub

#print axioms DLMF.AlgebraicAnalytic.sinEigenfunction_hilbertBasis

#print axioms Complex.sq_add_sq_ne_zero

#print axioms Complex.norm_sq_add_sq_ge

#print axioms Complex.integrableOn_pow_div_sq_add_sq_pow

#print axioms Complex.sq_add_mul_sq_mem_slitPlane

#print axioms Complex.integral_quadratic_log_kernel

#print axioms Complex.integrable_quadratic_log_kernel

#print axioms Complex.integrableOn_log_one_add_sq_div_sq_mul_cos

#print axioms DLMF.AlgebraicAnalytic.fourierCosTransform_log_one_add

#print axioms DLMF.AlgebraicAnalytic.fourierCosTransform_log_sub_log

#print axioms DLMF.AlgebraicAnalytic.expEigenfunction_hilbertBasis

#print axioms MeasureTheory.integrableOn_Ioi_div_of_memLp

#print axioms MeasureTheory.integral_abs_sub_cut_eq_integral_Ioi

#print axioms DLMF.AlgebraicAnalytic.hilbertTruncated_eq_integral_Ioi

#print axioms TestFunction.instBarrelledSpace

#print axioms CompactConvergenceCLM.tendsto_atTop_iff_forall_apply

#print axioms DLMF.AlgebraicAnalytic.distrib_tendsto_iff

#print axioms StieltjesFunction.integral_mul_deriv_eq_neg

#print axioms DLMF.AlgebraicAnalytic.stieltjes_eq_deriv

#print axioms DLMF.AlgebraicAnalytic.deriv_stieltjes_of_density

#print axioms DLMF.AlgebraicAnalytic.hausdorffMeasure_parallelogram

#print axioms DLMF.AlgebraicAnalytic.fourierCosTransform_quartic
