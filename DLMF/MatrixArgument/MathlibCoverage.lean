/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral

/-!
# DLMF Chapter 35 results already in Tau Ceti

Tau Ceti formalizes the real multivariate gamma function `TauCeti.multivariateGamma p a`
(DLMF 35.3.4 for real `a`) and its cone integral against `TauCeti.symmetricLebesgue p`, the
Lebesgue measure on the upper-triangular coordinates, which is DLMF's
`dX = ∏_{j≤k} dx_{j,k}` (35.1). The project's complex `DLMF.MatrixArgument.multivariateGamma`
agrees with it on real arguments (`DLMF.MatrixArgument.multivariateGamma_ofReal`); the complex
integral 35.3.1 is `DLMF.MatrixArgument.multivariateGamma_eq_integral`.
-/

dlmf_upstream 35.3.E1 TauCeti.integral_posDef_multivariateGamma
  "special case: real a > (m-1)/2; Bochner integral over the cone against symmetricLebesgue"
dlmf_upstream 35.3.E1 TauCeti.integrableOn_posDef_det_rpow_mul_exp_neg_trace
  "partial: absolute convergence of 35.3.1 for real a > (m-1)/2"
dlmf_upstream 35.3.E4 TauCeti.multivariateGamma_def
  "special case: the product formula for real a"
dlmf_upstream 35.1 TauCeti.symmetricLebesgue
  "exact: the measure dX = ∏_{j≤k} dx_{j,k} on real symmetric matrices"
