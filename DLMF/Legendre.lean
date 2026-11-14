/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.PolynomialAddition
public import DLMF.Legendre.EndpointPair
public import DLMF.Legendre.AssociatedSchlafliContours
public import DLMF.Legendre.OrdinaryLocalSeries
public import DLMF.Legendre.IntegerSecondKind

public import DLMF.Legendre.OrderMinimality

public import DLMF.Legendre.FiniteWeightedIntegral

public import DLMF.Legendre.Associated
public import DLMF.Legendre.SpecialValues
public import DLMF.Legendre.Connections
public import DLMF.Legendre.AssociatedRecurrences
public import DLMF.Legendre.Hypergeometric
public import DLMF.Legendre.IntegralRepresentations
public import DLMF.Legendre.SchlafliContours
public import DLMF.Legendre.IntegralTools
public import DLMF.Legendre.BoundaryAsymptotics
public import DLMF.Legendre.Integrals
public import DLMF.Legendre.SeriesTools
public import DLMF.Legendre.FourierEstimates
public import DLMF.Legendre.Series
public import DLMF.Legendre.Singularities
public import DLMF.Legendre.IntegerTheory
public import DLMF.Legendre.Toroidal
public import DLMF.Legendre.Conical
public import DLMF.Legendre.UniformCoordinates
public import DLMF.Legendre.Uniform
public import DLMF.Legendre.Uniform.HyperbolicEquation
public import DLMF.Legendre.ConicalAsymptotics
public import DLMF.Legendre.Sums
public import DLMF.Legendre.Zeros
public import DLMF.Legendre.Continuation
public import DLMF.Legendre.Harmonics
public import DLMF.Legendre.RelatedFunctions
public import DLMF.Legendre.Primitives
public import DLMF.Legendre.LocalTheory
public import DLMF.Legendre.SourceChecks
public import DLMF.Legendre.ParameterLimits
public import DLMF.Legendre.FirstKindProperties
public import DLMF.Legendre.Ferrers
public import DLMF.Legendre.Integer
public import DLMF.Legendre.Laplace
public import DLMF.Legendre.Neumann
public import DLMF.Legendre.Recurrences
public import DLMF.Legendre.PrincipalDegreeNormalization
public import DLMF.Legendre.SecondKind
public import DLMF.Legendre.MathlibCoverage
public import DLMF.Legendre.ZeroTools
public import DLMF.Legendre.ZeroCounts
public import DLMF.Legendre.FourierCoefficients
public import DLMF.Legendre.AdditionTools
public import DLMF.Legendre.QAdditionTools
public import DLMF.Legendre.FourierTools
public import DLMF.Legendre.ZonalSeries
public import DLMF.Legendre.ZonalSeries.Endpoint

public import DLMF.Legendre.ToroidalSeparation

public import DLMF.Legendre.SimplePoleExpansion

public import DLMF.Legendre.AnalyticNeumannExpansion

/-!
# Legendre and related functions (DLMF Chapter 14; Temme Chapter 8)

This umbrella module collects the Legendre functions of DLMF Chapter 14: the degree-only
Legendre functions `P_ν`, `Q_ν` and Ferrers functions, the associated Legendre functions
`P^μ_ν`, `Q^μ_ν` and Olver's `𝑸^μ_ν`, the Ferrers functions `𝖯^μ_ν`, `𝖰^μ_ν`, their
recurrences, connections, integral representations, integrals, series, addition theorems,
zeros, asymptotic and uniform approximations, conical and toroidal functions, continuation
beyond the principal sheet, and spherical harmonics.

Mathlib's shifted Legendre polynomials and their Rodrigues formula are referenced in
`DLMF.Legendre.IntegerTheory`.
-/
