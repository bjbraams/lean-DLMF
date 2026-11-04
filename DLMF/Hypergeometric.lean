/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.EulerHalfLine
public import DLMF.Hypergeometric.Boundary
public import DLMF.Hypergeometric.AnalyticProperties
public import DLMF.Hypergeometric.Asymptotics
public import DLMF.Hypergeometric.Basic.SpecialValues
public import DLMF.Hypergeometric.QuadraticConnections
public import DLMF.Hypergeometric.ConnectionFormulas
public import DLMF.Hypergeometric.LogConnectionsRecipGamma
public import DLMF.Hypergeometric.Contiguous
public import DLMF.Hypergeometric.ContinuedFractions
public import DLMF.Hypergeometric.Continuation
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Derivatives
public import DLMF.Hypergeometric.DiffEq
public import DLMF.Hypergeometric.Elementary
public import DLMF.Hypergeometric.EulerIntegral
public import DLMF.Hypergeometric.FurtherTransformations
public import DLMF.Hypergeometric.Identities
public import DLMF.Hypergeometric.IntegralRepresentations
public import DLMF.Hypergeometric.Kummer
public import DLMF.Hypergeometric.Riemann
public import DLMF.Hypergeometric.Solutions
public import DLMF.Hypergeometric.Transformations
public import DLMF.Hypergeometric.BarnesAux
public import DLMF.Hypergeometric.Basic.GeneralizedEquation
public import DLMF.Hypergeometric.LoopIntegral
public import DLMF.Hypergeometric.Saalschutz
public import DLMF.Hypergeometric.AppellF4
public import DLMF.Hypergeometric.FiniteConvolution
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import DLMF.Hypergeometric.GeneralizedContinuity
public import DLMF.Hypergeometric.Basic.GeneralizedIntegral
public import DLMF.Hypergeometric.Clausen
public import DLMF.Hypergeometric.SpecialCases
public import DLMF.Hypergeometric.ParameterHolomorphy
public import DLMF.Hypergeometric.MathlibCoverage
public import DLMF.Hypergeometric.SpecialValueTools
public import DLMF.Hypergeometric.CubicTools

/-!
# The hypergeometric function (DLMF Chapter 15; AAR Chapters 2 and 3)

Mathlib supplies the Gaussian series `₂F₁` (`ordinaryHypergeometric`), its radius of
convergence, the regularized generalized series and the binomial series `(1+x)^a`. This
umbrella imports the identities of AAR Chapters 2–3 and the results of DLMF Chapter 15 that are
absent from Mathlib: continuation in the argument and the parameters, special values,
derivatives and contiguous relations, integral representations, transformations, connection
formulas, local solutions of the hypergeometric equation, continued fractions and asymptotics.

It also imports results from Duverney, *An Introduction to Hypergeometric Functions*,
Chapters 3–4: Pfaff–Saalschütz (`Saalschutz`); the derivative, contiguous relation, uniqueness of
power-series solutions and Euler–Pochhammer integral of the general `ₚF_q`
(`GeneralizedCalculus`, `GeneralizedIntegral`); Clausen's formula with Euler's `arcsin²` series
and `π² = 18 ∑ 1/(n² C(2n,n))` (`Clausen`); and `Si` as a `₁F₂` (`SpecialCases`).
-/
