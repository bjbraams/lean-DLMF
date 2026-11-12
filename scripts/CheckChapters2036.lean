/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF
import DLMFMathlib

/-!
# Axiom audit for completed proofs from DLMF Chapters 20–36

The audited declarations and their transitive dependencies use standard axioms only.
The chapter umbrellas retain other explicitly admitted statements.
-/

#print axioms DLMF.WignerSymbols.LegendreProducts.zero_projection_square
#print axioms DLMF.WignerSymbols.LegendreProducts.coefficient
#print axioms DLMF.WignerSymbols.LegendreProducts.zero_of_not_gap
#print axioms DLMF.WignerSymbols.LegendreProducts.linearization
#print axioms DLMF.WignerSymbols.LegendreProducts.triple_integral
#print axioms DLMF.WignerSymbols.LegendreProducts.triple_integral_cos
#print axioms DLMF.WignerSymbols.legendrePolynomialP_mul_legendrePolynomialP
#print axioms DLMF.WignerSymbols.integral_legendrePolynomialP_mul_mul

#print axioms DLMF.JacobiElliptic.FourPointAddition.squares
#print axioms
  DLMF.JacobiElliptic.FourPointAddition.det_and_product_eq_zero_of_additionDenominators_ne_zero
#print axioms DLMF.JacobiElliptic.FourPointAddition.isJacobiRegular_zero
#print axioms DLMF.JacobiElliptic.FourPointAddition.continuousAt_jacobiSn_zero
#print axioms DLMF.JacobiElliptic.FourPointAddition.eventually_isJacobiRegular_mul
#print axioms DLMF.JacobiElliptic.FourPointAddition.eventually_additionDenominator_ne_zero
#print axioms DLMF.JacobiElliptic.FourPointAddition.det_thetaMatrix_eq_prod_mul_det
#print axioms DLMF.JacobiElliptic.FourPointAddition.product_theta_eq_prod_mul_relation
#print axioms DLMF.JacobiElliptic.FourPointAddition.det_and_product_eq_zero
#print axioms DLMF.JacobiElliptic.jacobi_det_sum_zero
#print axioms DLMF.JacobiElliptic.jacobi_prod_sum_zero
#print axioms Real.radianFourierIntegral
#print axioms Real.radianFourierIntegral_def
#print axioms Real.fourier_eq_radianFourierIntegral
#print axioms Real.radianFourierIntegral_inversion
#print axioms Real.radianFourierIntegral_smul_measure
#print axioms Real.radianFourierIntegral_inversion_of_volume_eq_smul
#print axioms Matrix.trace_map_ofReal_add_I_smul_mul_map_ofReal
#print axioms DLMF.MatrixArgument.MatrixLaplaceInversion.damped
#print axioms DLMF.MatrixArgument.MatrixLaplaceInversion.damped_def
#print axioms DLMF.MatrixArgument.MatrixLaplaceInversion.damped_of_mem
#print axioms DLMF.MatrixArgument.MatrixLaplaceInversion.damped_of_notMem
#print axioms DLMF.MatrixArgument.MatrixLaplaceInversion.radianFourierIntegral_damped
#print axioms DLMF.MatrixArgument.MatrixLaplaceInversion.continuousAt_damped
#print axioms DLMF.MatrixArgument.matrixLaplaceTransform_inversion
#print axioms DLMF.CoalescingSaddles.PearceySymmetryLine.pearcey_eq_quartic
#print axioms DLMF.CoalescingSaddles.PearceySymmetryLine.pearcey_eq_kummer
#print axioms DLMF.CoalescingSaddles.PearceySymmetryLine.value_bessel
#print axioms DLMF.CoalescingSaddles.cuspoidIntegral_two_zero_left

#print axioms DLMF.Mathieu.isInceCosPoly_inceC
#print axioms DLMF.Mathieu.isInceSinPoly_inceS
#print axioms DLMF.Mathieu.IsInceCosPoly.neg_eq
#print axioms DLMF.Mathieu.IsInceSinPoly.neg_eq
#print axioms DLMF.Mathieu.IsInceCosPoly.periodic
#print axioms DLMF.Mathieu.IsInceSinPoly.periodic
#print axioms DLMF.Mathieu.paraboloidalHc_neg
#print axioms DLMF.Mathieu.paraboloidalHs_neg
#print axioms DLMF.Mathieu.periodic_paraboloidalHc
#print axioms DLMF.Mathieu.periodic_paraboloidalHs
#print axioms DLMF.Mathieu.isInceSolution_zero
#print axioms DLMF.Mathieu.isInceSolution_inceC
#print axioms DLMF.Mathieu.isInceSolution_inceS
#print axioms DLMF.Mathieu.isWhittakerHillSolution_iff_isInceSolution
#print axioms DLMF.Mathieu.paraboloidal_isWhittakerHillSolution
#print axioms DLMF.Mathieu.integral_paraboloidalHc_mul_paraboloidalHs
#print axioms DLMF.Mathieu.paraboloidalHc_Hs_double_orthogonal'
#print axioms DLMF.Mathieu.paraboloidalHc_Hs_double_orthogonal

#print axioms DLMF.BernoulliEuler.bernoulliFun_two_mul_add_one_bounds
