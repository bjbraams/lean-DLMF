/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.Integrals.LaguerreHankel

public import DLMF.OrthogonalPolynomials.OrderMinimality

public import DLMF.OrthogonalPolynomials.LegendreSeries
public import DLMF.OrthogonalPolynomials.CharlierCoefficientNormalization
public import DLMF.OrthogonalPolynomials.General
public import DLMF.OrthogonalPolynomials.GeneralRodrigues
public import DLMF.OrthogonalPolynomials.GegenbauerNorm
public import DLMF.OrthogonalPolynomials.GeneralRecurrenceCoefficients

public import DLMF.OrthogonalPolynomials.Basic
public import DLMF.OrthogonalPolynomials.HahnMoments
public import DLMF.OrthogonalPolynomials.ScalarSeries
public import DLMF.OrthogonalPolynomials.Mehler
public import DLMF.OrthogonalPolynomials.MeasureConstruction
public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.OrthogonalPolynomials.Topics
public import DLMF.OrthogonalPolynomials.Beukers
public import DLMF.OrthogonalPolynomials.HermiteUncertainty
public import DLMF.OrthogonalPolynomials.MatchingIntegrals
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
public import DLMF.OrthogonalPolynomials.LegendreIntegralRepresentations
public import DLMF.OrthogonalPolynomials.JacobiFractionalTransforms
public import DLMF.OrthogonalPolynomials.LegendreAddition
public import DLMF.OrthogonalPolynomials.LegendreSingular
public import DLMF.OrthogonalPolynomials.ChebyshevExpansion
public import DLMF.OrthogonalPolynomials.ChebyshevUniformSeries
public import DLMF.OrthogonalPolynomials.Series
public import DLMF.OrthogonalPolynomials.BoundsZeros
public import DLMF.OrthogonalPolynomials.JacobiZeroBounds
public import DLMF.OrthogonalPolynomials.JacobiParameterZeros
public import DLMF.OrthogonalPolynomials.ContinuedFractions
public import DLMF.OrthogonalPolynomials.Hahn
public import DLMF.OrthogonalPolynomials.DiscreteAddition
public import DLMF.OrthogonalPolynomials.DiscreteRodrigues
public import DLMF.OrthogonalPolynomials.HahnRodrigues
public import DLMF.OrthogonalPolynomials.Wilson
public import DLMF.OrthogonalPolynomials.WilsonRecurrences
public import DLMF.OrthogonalPolynomials.WilsonHahnNorms
public import DLMF.OrthogonalPolynomials.WilsonContourNorms
public import DLMF.OrthogonalPolynomials.QFamilies
public import DLMF.OrthogonalPolynomials.Associated
public import DLMF.OrthogonalPolynomials.ExceptionalOrthogonality
public import DLMF.OrthogonalPolynomials.QFamilies.ContinuousQHermite
public import DLMF.OrthogonalPolynomials.UnitCircle
public import DLMF.OrthogonalPolynomials.Multivariate
public import DLMF.OrthogonalPolynomials.InequalityTools
public import DLMF.OrthogonalPolynomials.SzegoAskeyOrthogonality
public import DLMF.OrthogonalPolynomials.QuadratureAndKernels
public import DLMF.OrthogonalPolynomials.SecondKindContinuedFraction
public import DLMF.OrthogonalPolynomials.QuadratureError
public import DLMF.OrthogonalPolynomials.SpectralMoments
public import DLMF.OrthogonalPolynomials.SummableRecurrencePerturbation
public import DLMF.OrthogonalPolynomials.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.Darboux
public import DLMF.OrthogonalPolynomials.ConnectionCoefficients
public import DLMF.OrthogonalPolynomials.JacobiContinuation
public import DLMF.OrthogonalPolynomials.JacobiMultiplication
public import DLMF.OrthogonalPolynomials.LaguerreContinuation
public import DLMF.OrthogonalPolynomials.PositivityCriteria

public import DLMF.OrthogonalPolynomials.JacobiContours

public import DLMF.OrthogonalPolynomials.PrescribedLeadingCoefficients
public import DLMF.OrthogonalPolynomials.LeastSquaresProjection
public import DLMF.OrthogonalPolynomials.LegendreComplexLaplace

public import DLMF.OrthogonalPolynomials.LegendreDarbouxLeading

public import DLMF.OrthogonalPolynomials.JacobiBesselZeroLimit

public import DLMF.OrthogonalPolynomials.LaguerreDualSeries

public import DLMF.OrthogonalPolynomials.NormProducts

public import DLMF.OrthogonalPolynomials.ClassicalCoefficientIdentities

/-!
# Orthogonal polynomials (DLMF Chapter 18, AAR Chapters 5–7)

Mathlib already has Chebyshev polynomials `T,U,C,S` (including `T_n(cos θ) = cos(nθ)`,
orthogonality of `T` on `[-1,1]` with weight `(1-x²)^{-1/2}`, Chebyshev–Gauss quadrature, and
extrema), the probabilists' Hermite polynomials, and the shifted Legendre polynomials. The
modules below contain general orthogonal polynomial theory, the classical families
(physicists' Hermite, Laguerre, Jacobi, Gegenbauer), the topics of AAR Chapter 7 (connection
coefficients, Turán, Apéry's theorem), and the DLMF Chapter 18 material: Hahn, Wilson and
`q`-families, associated and other polynomials, orthogonal polynomials on the unit circle and
in several variables, bounds, zeros, integrals and series.

Two modules follow Temme, *Special Functions*, §§6.8–6.9: `Legendre` (bounds from Laplace's
integral, mean-square optimality of Legendre expansions, Bessel's inequality and the
Laplace–Heine asymptotic formula) and `ChebyshevExpansion` (convergence of Chebyshev series,
coefficient decay in Bernstein ellipses, truncation error and Clenshaw's algorithm).
-/
