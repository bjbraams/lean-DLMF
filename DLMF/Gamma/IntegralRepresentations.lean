/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.IntegralRepresentations.HankelAndGaussian
public import DLMF.Gamma.IntegralRepresentations.PrymAndOscillatory
public import DLMF.Gamma.IntegralRepresentations.DigammaAndBinet
public import DLMF.Gamma.IntegralRepresentations.FrullaniAndMoments

/-!
# Integral representations of the Gamma and digamma functions (DLMF §5.9)

This umbrella collects the real-line Laplace, Fourier, Hankel-type and Binet-type integral
representations of `Γ`, `1/Γ`, `ln Γ` and `ψ` of DLMF §5.9; Euler's integral 5.2.1 is Mathlib's
`Gamma_eq_integral`. The Hankel loop 5.9.2 and the Mellin–Barnes formulae 5.9.11 and 5.9.17
are not formalized; the Hankel loop on its steepest-descent path is `recip_Gamma_binet`, proved
without contour deformation.
-/
