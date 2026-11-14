/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.GeneralizedHypergeometric.KarlssonMinton

public import DLMF.GeneralizedHypergeometric.KummerCubeAction

public import DLMF.GeneralizedHypergeometric.CubeDiagonalAction

public import DLMF.GeneralizedHypergeometric.TerminatingDifferentialEquation

public import DLMF.GeneralizedHypergeometric.ThomaeGroup


public import DLMF.GeneralizedHypergeometric.FactorialTripleSeries

public import DLMF.GeneralizedHypergeometric.KummerCubeCoordinates

public import DLMF.GeneralizedHypergeometric.WhippleCoordinates

public import DLMF.GeneralizedHypergeometric.SeedTransformations
public import DLMF.GeneralizedHypergeometric.RamanujanDigamma
public import DLMF.GeneralizedHypergeometric.FiniteTransformationGroups
public import DLMF.GeneralizedHypergeometric.BetaTransforms
public import DLMF.GeneralizedHypergeometric.TransformationGroups
public import DLMF.GeneralizedHypergeometric.KampeDeFeriet
public import DLMF.GeneralizedHypergeometric.Watson
public import DLMF.GeneralizedHypergeometric.Whipple
public import DLMF.GeneralizedHypergeometric.Thomae
public import DLMF.GeneralizedHypergeometric.UnitParameterAnalyticity
public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.Appell
public import DLMF.GeneralizedHypergeometric.GeneralSquare
public import DLMF.GeneralizedHypergeometric.GHATools
public import DLMF.GeneralizedHypergeometric.AppellContinuation
public import DLMF.GeneralizedHypergeometric.Asymptotics
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.GeneralizedHypergeometric.LimitFunctionBarnes
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import Mathlib.RingTheory.PowerSeries.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Solutions
public import DLMF.GeneralizedHypergeometric.Derivatives
public import DLMF.GeneralizedHypergeometric.BookSeries
public import DLMF.GeneralizedHypergeometric.DifferentialEquations
public import DLMF.GeneralizedHypergeometric.Integrals
public import DLMF.GeneralizedHypergeometric.MathlibCoverage
public import DLMF.GeneralizedHypergeometric.MeijerG
public import DLMF.GeneralizedHypergeometric.MeijerGRelations
public import DLMF.GeneralizedHypergeometric.Transformations
public import DLMF.GeneralizedHypergeometric.UnitArgument
public import DLMF.GeneralizedHypergeometric.TwoTermConnections
public import DLMF.GeneralizedHypergeometric.UnitArgumentDougall
public import DLMF.GeneralizedHypergeometric.ClearedTerminating
public import DLMF.GeneralizedHypergeometric.WhippleTerminating

/-!
# Generalized hypergeometric, Appell and Meijer G functions (DLMF Chapter 16)

This umbrella imports the generalized hypergeometric functions `ₚF_q` (definitions, analytic
properties, derivatives, unit-argument sums, integrals, transformations, differential
equations and asymptotics), the Appell and Horn double series, and the Meijer G function.
-/
