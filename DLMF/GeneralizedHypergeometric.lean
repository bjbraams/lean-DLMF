/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.Appell
public import DLMF.GeneralizedHypergeometric.GHATools
public import DLMF.GeneralizedHypergeometric.AppellContinuation
public import DLMF.GeneralizedHypergeometric.Asymptotics
public import DLMF.GeneralizedHypergeometric.ParameterAndSeriesProperties
public import DLMF.GeneralizedHypergeometric.Derivatives
public import DLMF.GeneralizedHypergeometric.DifferentialEquations
public import DLMF.GeneralizedHypergeometric.Integrals
public import DLMF.GeneralizedHypergeometric.MathlibCoverage
public import DLMF.GeneralizedHypergeometric.MeijerG
public import DLMF.GeneralizedHypergeometric.MeijerGRelations
public import DLMF.GeneralizedHypergeometric.Transformations
public import DLMF.GeneralizedHypergeometric.UnitArgument

/-!
# Generalized hypergeometric, Appell and Meijer G functions (DLMF Chapter 16)

This umbrella imports the generalized hypergeometric functions `ₚF_q` (definitions, analytic
properties, derivatives, unit-argument sums, integrals, transformations, differential
equations and asymptotics), the Appell and Horn double series, and the Meijer G function.
-/
