/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.TricomiLaplace
public import DLMF.Confluent.MobiusTaylor
public import DLMF.Confluent.Basic
public import DLMF.Confluent.Regularized
public import DLMF.Confluent.ParameterDerivatives
public import DLMF.Confluent.LogSeries
public import DLMF.Confluent.BasicProperties
public import DLMF.Confluent.Whittaker
public import DLMF.Confluent.Recurrence
public import DLMF.Confluent.ConnectionWronskians
public import DLMF.Confluent.IntegralRepresentations
public import DLMF.Confluent.ContinuedFractions
public import DLMF.Confluent.Relations
public import DLMF.Confluent.Asymptotics
public import DLMF.Confluent.TricomiRotated
public import DLMF.Confluent.AsymptoticConsequences
public import DLMF.Confluent.IncompleteGamma
public import DLMF.Confluent.ExpIntegral
public import DLMF.Confluent.ParabolicCylinder
public import DLMF.Confluent.ErrorFunctions
public import DLMF.Confluent.FresnelAsymptotics
public import DLMF.Confluent.Coulomb
public import DLMF.Confluent.CoulombAsymptotics
public import DLMF.Confluent.CoulombIrregular
public import DLMF.Confluent.ZeroTools
public import DLMF.Confluent.Zeros
public import DLMF.Confluent.KummerDecay
public import DLMF.Confluent.Integrals
public import DLMF.Confluent.Series
public import DLMF.Confluent.ProductsAddition
public import DLMF.Confluent.MathlibCoverage
public import DLMF.Confluent.Continuation
public import DLMF.Confluent.LargeA
public import DLMF.Confluent.LargeASharp

/-!
# Confluent hypergeometric functions (AAR Chapter 4, §§4.1–4.4; DLMF Chapter 13)

Mathlib has the regularized generalized hypergeometric series, including the `p = q`
case of infinite radius, but not the named Kummer function `M(a,c,z) = ₁F₁(a;c;z)`,
Tricomi's `U(a,b,z)`, nor Whittaker's `M_{κ,μ}` and `W_{κ,μ}`. Bessel functions are
in `DLMF.Bessel`.

The additional modules collect DLMF Chapter 13 statements from §§13.2–13.26.
Applications (§§13.27–13.28) and computation (§§13.29–13.32) are excluded, as is
notation §13.1.

The special cases of Temme, *Special Functions*, §7.3 have their own modules:
`IncompleteGamma` (DLMF Chapter 8 and the `erfc` expansion), `ExpIntegral` (DLMF Chapter 6
and §§8.19–8.20), `ParabolicCylinder` (DLMF Chapter 12), `ErrorFunctions` (Fresnel and
Dawson integrals) and `Coulomb` (DLMF §33.2). Each statement taken from the DLMF records its equation number in a
`@[dlmf]` attribute. Many newly acquired statements are admitted and remain proof
obligations.

`LargeA` proves the large-negative-`a` behaviour of `M` and `U` (Beals–Wong (8.1.12), (8.2.10))
and Fejér's formula for Laguerre polynomials, by the Volterra method of Beals–Wong §13.2.
`LargeASharp` sharpens these to the error orders of DLMF 13.8.9, 13.8.10 and 18.15.14.
-/
