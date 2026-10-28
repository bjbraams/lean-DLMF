/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Integrals.Laplace
public import DLMF.Confluent.Integrals.HankelKernels
public import DLMF.Confluent.Integrals.BesselTransforms
public import DLMF.Confluent.Integrals.WhittakerTransforms
public import DLMF.Confluent.Integrals.Stieltjes
public import DLMF.Confluent.Integrals.GaussTransforms

/-!
# Integrals (DLMF §§13.10, 13.23)

Gauss functions in the transforms use cut-plane continuation. The former series-only
statements were false when their transformed argument left the unit disk.

The general regularized Kummer Laplace transform is proved by termwise integration
when `‖k‖ < Re z` and then by holomorphic continuation throughout the full
convergence half-plane, retaining all denominator parameters, including Gamma poles.
The self-transform specializes it using the binomial identity.
Mathlib's summable-integral-norm theorem justifies the exchange, using a regularized
Gauss series to sum the absolute Gamma moments. The Whittaker M closed transform
then follows with an explicit principal-logarithm calculation in the right half-plane.
Tricomi's Mellin transform follows from its Laplace representation and Mathlib's
Fubini theorem. Absolute convergence of the double kernel reduces to the Tau Ceti
contributors' second Beta integrability theorem; the local proved Gamma and Beta
integral formulas evaluate the exchanged integrals.

The boundary Mellin transform uses a summable Gamma-moment majorant from the
proved Gamma-ratio asymptotics. Regularized Gauss summation, including singular
denominator parameters, evaluates the resulting series; the regularized Whittaker
M transform follows by combining positive-real powers and exponential factors.

The Hankel-type transforms 13.10.14–13.10.15 and 13.23.10–13.23.11 use a power bound for the
kernel `t^{ν/2} J_ν(2√(xt))`, its termwise Laplace transform
`x^{ν/2} s^{-ν-1} e^{-x/s}`, Fubini against the Tricomi Laplace or the Euler integral, and the
substitutions `s ↦ 1/s` and `s = 1/(1+v)`. The cosine transforms 13.10.12 and 13.23.8 use the
Gaussian Fourier integral in the same way. In the Euler cases the result is extended to all
parameters by the identity theorem: the integrals are holomorphic in a parameter by the locally
uniform decay bound of `DLMF.Confluent.KummerDecay`, and `U` is entire in its first parameter.
The Stieltjes transform 13.4.6 is proved here as well.

Indefinite integrals are stated as derivative identities. Laplace, Mellin, and
Bessel transforms use real half-lines. Hankel-loop formulas 13.10.8–13.10.9 and
13.23.6–13.23.7, and the inversion pair 13.23.13–13.23.14, are deferred.
-/
