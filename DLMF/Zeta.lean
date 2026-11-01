/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Zeta.Riemann
public import DLMF.Zeta.Reflection
public import DLMF.Zeta.IntegralReps
public import DLMF.Zeta.IntegerArguments
public import DLMF.Zeta.Sums
public import DLMF.Zeta.Asymptotics
public import DLMF.Zeta.Zeros
public import DLMF.Zeta.MathlibCoverage
public import DLMF.Zeta.HurwitzEulerMaclaurin
public import DLMF.Zeta.DirichletTest
public import DLMF.Zeta.HurwitzContinuation
public import DLMF.Zeta.Hurwitz
public import DLMF.Zeta.HurwitzIntegrals
public import DLMF.Zeta.Polylog
public import DLMF.Zeta.Periodic
public import DLMF.Zeta.LerchContinuation
public import DLMF.Zeta.Lerch
public import DLMF.Zeta.DirichletL
public import DLMF.Zeta.MathlibCoverageB
public import DLMF.Zeta.CotangentMoments

/-!
# Zeta and related functions

This area covers DLMF Chapter 25: the Riemann zeta function (§§25.1–25.10, files `Riemann`
through `Zeros`), the Hurwitz zeta function, polylogarithms, periodic zeta functions, Lerch's
transcendent and Dirichlet `L`-functions (§§25.11–25.15, files `Hurwitz` through `DirichletL`).
`ζ(s)` is Mathlib's `riemannZeta`; `ζ(s,a)`, `F(x,s)` and `L(s,χ)` reuse Mathlib's Hurwitz zeta,
`HurwitzZeta.expZeta` and `DirichletCharacter.LFunction` (and the project's
`DLMF.Confluent.hurwitzZetaComplex` for complex `a`).
-/
