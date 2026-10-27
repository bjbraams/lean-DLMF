/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.HahnMoments
public import DLMF.OrthogonalPolynomials.ScalarSeries
public import DLMF.OrthogonalPolynomials.Mehler
public import DLMF.OrthogonalPolynomials.General
public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.OrthogonalPolynomials.Topics
public import DLMF.OrthogonalPolynomials.MathlibCoverage
public import DLMF.OrthogonalPolynomials.GeneralIdentities
public import DLMF.OrthogonalPolynomials.Explicit
public import DLMF.OrthogonalPolynomials.Differential
public import DLMF.OrthogonalPolynomials.JacobiDiscriminant
public import DLMF.OrthogonalPolynomials.ClassicalInstances
public import DLMF.OrthogonalPolynomials.SoninePolyaApplications
public import DLMF.OrthogonalPolynomials.HermiteFixedX
public import DLMF.OrthogonalPolynomials.HermiteZeroBounds
public import DLMF.OrthogonalPolynomials.BinomialSeries
public import DLMF.OrthogonalPolynomials.GegenbauerSeries
public import DLMF.OrthogonalPolynomials.LaguerreSeries
public import DLMF.OrthogonalPolynomials.Limits
public import DLMF.OrthogonalPolynomials.Integrals
public import DLMF.OrthogonalPolynomials.Legendre
public import DLMF.OrthogonalPolynomials.LegendreAddition
public import DLMF.OrthogonalPolynomials.LegendreSingular
public import DLMF.OrthogonalPolynomials.ChebyshevExpansion
public import DLMF.OrthogonalPolynomials.Series
public import DLMF.OrthogonalPolynomials.BoundsZeros
public import DLMF.OrthogonalPolynomials.JacobiZeroBounds
public import DLMF.OrthogonalPolynomials.ContinuedFractions
public import DLMF.OrthogonalPolynomials.Hahn
public import DLMF.OrthogonalPolynomials.DiscreteAddition
public import DLMF.OrthogonalPolynomials.DiscreteRodrigues
public import DLMF.OrthogonalPolynomials.HahnRodrigues
public import DLMF.OrthogonalPolynomials.Wilson
public import DLMF.OrthogonalPolynomials.QFamilies
public import DLMF.OrthogonalPolynomials.Associated
public import DLMF.OrthogonalPolynomials.UnitCircle
public import DLMF.OrthogonalPolynomials.Multivariate
public import DLMF.OrthogonalPolynomials.InequalityTools

/-!
# Orthogonal polynomials (AAR Chapters 5–7)

Mathlib already has Chebyshev polynomials `T,U,C,S` (including `T_n(cos θ) = cos(nθ)`,
orthogonality of `T` on `[-1,1]` with weight `(1-x²)^{-1/2}`, Chebyshev–Gauss quadrature, and
extrema), the probabilists' Hermite polynomials, and the shifted Legendre polynomials. The
modules below record the remaining AAR Chapters 5–7 material: general orthogonal polynomial
theory, the classical families (physicists' Hermite, Laguerre, Jacobi, Gegenbauer), and the
Chapter 7 topics (connection coefficients, Turán, Apéry's theorem).

The additional modules collect DLMF Chapter 18 statements, each recording its equation
number in a `@[dlmf]` attribute.

Two modules follow Temme, *Special Functions*, §§6.8–6.9: `Legendre` (bounds from Laplace's
integral, mean-square optimality of Legendre expansions, Bessel's inequality and the
Laplace–Heine asymptotic formula) and `ChebyshevExpansion` (convergence of Chebyshev series,
coefficient decay in Bernstein ellipses, truncation error and Clenshaw's algorithm).
-/
