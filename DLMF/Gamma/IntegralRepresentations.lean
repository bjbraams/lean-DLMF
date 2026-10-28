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
# Integral representations (DLMF §5.9)

Euler's integral 5.2.1 is Mathlib `Gamma_eq_integral`. Real-line Laplace,
Fourier, and Binet-type integrals are acquired below. The Hankel loop 5.9.2
and the Mellin–Barnes formulae 5.9.11, 5.9.17 are deferred; the Hankel loop on its
steepest-descent path, `recip_Gamma_binet`, is proved without contour deformation
(section `BinetLoop`).

The digamma integrals 5.9.12, 5.9.13 and 5.9.16 are proved from the digamma series by
termwise integration (`integral_tsum_of_summable_integral_norm`; the terms do not change
sign). Mathlib's Frullani integral gives `log x`. The constant in Binet's formula is
fixed by letting `x → ∞`, using `log x - 1/x ≤ ψ(x) ≤ log x`.
-/
