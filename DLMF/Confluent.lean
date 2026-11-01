/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.TricomiLaplace
public import DLMF.Confluent.MobiusTaylor
public import DLMF.Confluent.KummerProperties
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

Kummer's function `M(a,b,z) = ₁F₁(a;b;z)` and its regularized form, Tricomi's `U(a,b,z)`, and
Whittaker's `M_{κ,μ}` and `W_{κ,μ}`, with the statements of DLMF §§13.2–13.26: basic
properties, recurrences, connection formulas and Wronskians, integral representations,
continued fractions, asymptotic expansions, zeros, integrals, series and addition theorems.
Mathlib has the regularized generalized hypergeometric series but not these named functions.
Bessel functions are in `DLMF.Bessel`.

The special cases of Temme, *Special Functions*, §7.3 have their own modules:
`IncompleteGamma` (DLMF Chapter 8 and the `erfc` expansion), `ExpIntegral` (DLMF Chapter 6 and
§§8.19–8.20), `ParabolicCylinder` (DLMF Chapter 12), `ErrorFunctions` (Fresnel and Dawson
integrals) and `Coulomb` (DLMF §33.2). `LargeA` proves the large-negative-`a` behaviour of `M`
and `U` (Beals–Wong (8.1.12), (8.2.10)) and Fejér's formula for Laguerre polynomials, by the
Volterra method of Beals–Wong §13.2; `LargeASharp` sharpens these to the error orders of
DLMF 13.8.9, 13.8.10 and 18.15.14.

Notation (§13.1), applications (§§13.27–13.28) and computation (§§13.29–13.32) are not
covered.
-/
