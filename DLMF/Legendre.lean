/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.Associated
public import DLMF.Legendre.SpecialValues
public import DLMF.Legendre.Connections
public import DLMF.Legendre.AssociatedRecurrences
public import DLMF.Legendre.Hypergeometric
public import DLMF.Legendre.IntegralRepresentations
public import DLMF.Legendre.IntegralTools
public import DLMF.Legendre.BoundaryAsymptotics
public import DLMF.Legendre.Integrals
public import DLMF.Legendre.SeriesTools
public import DLMF.Legendre.Series
public import DLMF.Legendre.Singularities
public import DLMF.Legendre.IntegerTheory
public import DLMF.Legendre.Toroidal
public import DLMF.Legendre.Conical
public import DLMF.Legendre.UniformCoordinates
public import DLMF.Legendre.Uniform
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
public import DLMF.Legendre.Basic
public import DLMF.Legendre.Ferrers
public import DLMF.Legendre.Integer
public import DLMF.Legendre.Laplace
public import DLMF.Legendre.Neumann
public import DLMF.Legendre.Recurrences
public import DLMF.Legendre.SecondKind
public import DLMF.Legendre.MathlibCoverage
public import DLMF.Legendre.ZeroTools
public import DLMF.Legendre.ZeroCounts
public import DLMF.Legendre.AdditionTools
public import DLMF.Legendre.QAdditionTools
public import DLMF.Legendre.FourierTools

/-!
# Legendre and related functions (Temme Chapter 8; DLMF Chapter 14)

The original seven modules retain their proved degree-only P/Q and Ferrers P
APIs. The additional modules acquire associated P/Q, regularized Olver Q,
Ferrers Q, parameter derivatives, integrals, series, uniform approximations,
toroidal and conical functions, continuation by ODE transport and normalized
spherical harmonics. Their remaining `sorry` declarations are admissions.

Mathlib's shifted Legendre Rodrigues formula is referenced in IntegerTheory;
its normalization bridge already exists in OrthogonalPolynomials.Classical.
`DLMF111214Acquisition.md` records every equation, source counterexamples,
remaining domain extensions and the current proof and axiom audits.
-/
