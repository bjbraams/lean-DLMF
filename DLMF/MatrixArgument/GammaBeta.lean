/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.MatrixArgument.GammaBeta.LaplaceTransform
public import DLMF.MatrixArgument.GammaBeta.CholeskyCoordinates
public import DLMF.MatrixArgument.GammaBeta.GammaIntegrals
public import DLMF.MatrixArgument.GammaBeta.BetaIntegrals

/-!
# Laplace transform, multivariate gamma and beta functions (DLMF §§35.2–35.3)

This umbrella collects the Laplace transform of functions of matrix argument (DLMF §35.2,
`GammaBeta.LaplaceTransform`), the Cholesky substitution (`GammaBeta.CholeskyCoordinates`), the
integrals for the multivariate gamma functions `Γ_m` and `Γ_m(s₁, …, s_m)` (DLMF 35.3.1, 35.3.2,
35.3.4, `GammaBeta.GammaIntegrals`) and for the multivariate beta function `B_m` (DLMF 35.3.3,
35.3.6–35.3.8, `GammaBeta.BetaIntegrals`), all for complex parameters. For real `a` the
integral 35.3.1 is Tau Ceti's `TauCeti.integral_posDef_multivariateGamma`, recorded as an
upstream pointer in `DLMF.MatrixArgument.MathlibCoverage`.

## Implementation notes

**Correction of 35.2.2.** With DLMF's `dX = ∏_{j≤k} dx_{j,k}` (and `d𝐙 = ∏_{j≤k} dz_{j,k}`) the
pairing `tr(VX) = ∑_j v_{jj}x_{jj} + 2∑_{j<k} v_{jk}x_{jk}` doubles the off-diagonal
frequencies, so Fourier inversion on `𝓢` carries the factor `2^{m(m-1)/2}`:
`f(X) = 2^{m(m-1)/2} (2πi)^{-m(m+1)/2} ∫ expTrace(𝐙X) g(𝐙) d𝐙`. (Check with the Gaussian
`exp(-½ tr X²)`, whose Fourier transform on `𝓢` integrates to `(2π)^m π^{m(m-1)/2}`.)
DLMF prints the formula without it; the two agree for `m = 1`. The corrected formula is
`matrixLaplaceTransform_inversion`.
-/
