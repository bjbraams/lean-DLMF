/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Heun.Basic
public import DLMF.Heun.Basic.Equation
public import DLMF.Heun.LocalSolutions
public import DLMF.Heun.SeriesBoundary
public import DLMF.Heun.HeunFunctions
public import DLMF.Heun.PolynomialCriterion
public import DLMF.Heun.Hypergeometric
public import DLMF.Heun.JacobiExpansion
public import DLMF.Heun.DoublyPeriodic
public import DLMF.Heun.KernelAngles
public import DLMF.Heun.Integral
public import DLMF.Heun.IntegralPath
public import DLMF.Heun.Confluent
public import DLMF.Heun.ConfluenceLimits
public import DLMF.Heun.Fuchsian
public import DLMF.Heun.Classification
public import DLMF.Heun.KernelExamples

/-!
# Heun functions (DLMF Chapter 31)

This umbrella imports Heun's equation and its transformations, the local solution `Hl` as an
explicit power series, Heun functions and polynomials, hypergeometric reductions and expansions,
integral equations and representations, the confluent forms, the general Fuchsian equation and
Stieltjes polynomials.
-/
