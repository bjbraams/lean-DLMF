/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Bessel.Asymptotics
public import DLMF.Bessel.Basic
public import DLMF.Bessel.BesselIntegral
public import DLMF.Bessel.Elementary
public import DLMF.Bessel.KIntegrals
public import DLMF.Bessel.KIntegralRep
public import DLMF.Bessel.IntegralTransforms
public import DLMF.Bessel.LaplaceTransform
public import DLMF.Bessel.LargeOrder
public import DLMF.Bessel.Lommel
public import DLMF.Bessel.Modified
public import DLMF.Bessel.NeumannSeries
public import DLMF.Bessel.ProductIntegral
public import DLMF.Bessel.Schlafli
public import DLMF.Bessel.SecondKind
public import DLMF.Bessel.SphericalSeriesTools
public import DLMF.Bessel.SphericalProductTools
public import DLMF.Bessel.KMellin
public import DLMF.Bessel.SturmZeros
public import DLMF.Bessel.Theorems
public import DLMF.Bessel.YIntegralRep
public import DLMF.Bessel.YSchlafli
public import DLMF.Bessel.WeberSeries
public import DLMF.Bessel.Zeros
public import DLMF.Bessel.MathlibCoverage
public import DLMF.Bessel.P3mGraf

/-!
# Bessel functions (AAR Chapter 4, §§4.5–4.15; DLMF Chapter 10)

`J_ν` is Mathlib's `Complex.besselJ`, used directly; `besselJ_eq_regularized` gives its
regularized `₀F₁` series form, and Mathlib supplies parity at integer order (DLMF 10.11.1),
analyticity, entireness at integer order and the value at `0`. This cluster defines `Y_ν`,
`I_ν`, `K_ν` and the Hankel functions. It proves differential equations, recurrences,
Wronskians, half-integer values, Poisson's, Sonine's, Bessel's and Lommel's integrals, the
generating function, Hankel's large-argument expansions and the existence of infinitely many real
zeros.

The integer-order values of `Y` and `K` are parameter limits (`Filter.limUnder`). These limits
exist at every nonzero argument, are jointly continuous in order and argument
(`continuousAt_besselY`, `continuousAt_besselK`), and satisfy the recurrences and differential
equations for all orders. `WeberSeries` gives `Y_{-n} = (-1)ⁿ Y_n`, `Y_n` as an order derivative
of `J_ν`, the logarithmic series of `Y_n` (DLMF 10.8.1–10.8.2), the general solution
`A J_ν + B Y_ν` of Bessel's equation, the product formula 10.8.3 and the Jacobi–Anger cosine and
sine series. The values at zero supplied by the totalized definitions must not be
interpreted as finite limits of the classical singular functions.

The remaining admitted results are Gegenbauer's addition theorem (DLMF 10.23.8) and Nicholson's
integral (10.9.30). Their
stated domains agree with DLMF; in particular, no radius ordering is needed in 10.23.8 for `J`.
-/
