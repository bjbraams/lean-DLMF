/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QHypergeometric.Ramanujan
public import DLMF.QHypergeometric.BilateralParity
public import DLMF.QHypergeometric.BilateralEven

public import DLMF.QHypergeometric.TerminatingQuadraticTransformation
public import DLMF.QHypergeometric.FiniteBilateralTransformations
public import DLMF.QHypergeometric.FiniteDifferenceRational
public import DLMF.QHypergeometric.ParitySummation

public import DLMF.QHypergeometric.Appell
public import DLMF.QHypergeometric.BaileyPairs
public import DLMF.QHypergeometric.Convergence
public import DLMF.QHypergeometric.Dixon
public import DLMF.QHypergeometric.BasicSummations
public import DLMF.QHypergeometric.BasicSummations.FineCounterexample
public import DLMF.QHypergeometric.BasicSummations.HeineClassicalLimits
public import DLMF.QHypergeometric.BasicSummations.RogersFine
public import DLMF.QHypergeometric.BilateralParameterContinuity
public import DLMF.QHypergeometric.BilateralSummations
public import DLMF.QHypergeometric.BilateralTransformations
public import DLMF.QHypergeometric.Calculus
public import DLMF.QHypergeometric.ConstantTerms
public import DLMF.QHypergeometric.Elementary
public import DLMF.QHypergeometric.HigherSummations
public import DLMF.QHypergeometric.VeryWellPoised
public import DLMF.QHypergeometric.HigherSummationCounterexamples
public import DLMF.QHypergeometric.Integrals
public import DLMF.QHypergeometric.ContinuousBetaIntegrals
public import DLMF.QHypergeometric.WilsonIntegralLimit
public import DLMF.QHypergeometric.MathlibCoverage
public import DLMF.QHypergeometric.SearsTransformation
public import DLMF.QHypergeometric.Transformations
public import DLMF.QHypergeometric.VeryWellPoisedSums
public import DLMF.QHypergeometric.QuintupleProduct
public import DLMF.QHypergeometric.BibasicBilateral

public import DLMF.QHypergeometric.BaileyAbsoluteConvergence

/-!
# Basic hypergeometric and related functions (DLMF Chapter 17)

This umbrella collects the DLMF Chapter 17 development of basic hypergeometric (`q`-)series:
`q`-calculus, the general unilateral and bilateral series and their convergence, elementary
and higher summations, transformations, `q`-Appell functions, Bailey pairs, constant-term
identities and integrals.
-/
