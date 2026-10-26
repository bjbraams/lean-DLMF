/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ScalarSeries
public import DLMFMathlib.Analysis.SpecialFunctions.ChebyshevSeries
public import DLMFMathlib.Analysis.SpecialFunctions.Complex.LogBoundary
public import DLMFMathlib.NumberTheory.EulerPolynomials
public import DLMFMathlib.NumberTheory.EulerNumbers
public import DLMFMathlib.NumberTheory.BernoulliTaylor
public import DLMFMathlib.NumberTheory.T27aPrimeNumberTheorem
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.PartialFractions
public import DLMFMathlib.Analysis.EulerMaclaurin
public import DLMFMathlib.Analysis.BooleSummation
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import DLMFMathlib.Analysis.Asymptotics.Watson
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
public import DLMFMathlib.Analysis.Asymptotics.StationaryPhase
public import ToMathlib.Analysis.Integral.Laplace
public import DLMFMathlib.Analysis.Integral.Improper
public import ToMathlib.Analysis.Complex.Carlson
public import DLMFMathlib.Analysis.Complex.FactorialSeries
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.Complex.TaylorParameter
public import DLMFMathlib.Analysis.Complex.SegmentPrimitive
public import DLMFMathlib.Analysis.Complex.StarPrimitive
public import DLMFMathlib.Analysis.Complex.BarnesResidue
public import DLMFMathlib.Analysis.Complex.ZeroLocalization
public import DLMFMathlib.Analysis.ContinuedFraction.Convergence
public import DLMFMathlib.Analysis.SpecificLimits.Pincherle
public import DLMFMathlib.Analysis.ODE.SturmComparison
public import DLMFMathlib.Analysis.ODE.SymmetricSquare
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import DLMFMathlib.Analysis.ODE.P1oEntireLinear
public import DLMFMathlib.Analysis.ODE.P1oLinearGlobal
public import DLMFMathlib.Analysis.ODE.P1oParamHolomorphic
public import DLMFMathlib.Analysis.Fourier.P1a2EntirePeriodic
public import DLMFMathlib.Analysis.ODE.SoninePolya
public import DLMFMathlib.Analysis.ODE.Volterra
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenVolterra
public import DLMFMathlib.Analysis.ODE.LiouvilleGreen
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenExpansion
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenComparison
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenFinite
public import DLMFMathlib.Topology.Order.ZeroEnumeration
public import DLMFMathlib.Analysis.Calculus.DoubleZeroSqrt
public import DLMFMathlib.Analysis.Complex.MellinBarnesSeries
public import DLMFMathlib.Analysis.Complex.LagrangeBurmann
public import DLMFMathlib.Analysis.Complex.TrigR4SeriesExtension
public import DLMFMathlib.Analysis.Integral.PrincipalValue
public import DLMFMathlib.Analysis.ODE.SturmCount
public import DLMFMathlib.Analysis.ODE.SturmDeformation
public import DLMFMathlib.Analysis.Asymptotics.StieltjesRemainder
public import DLMFMathlib.Analysis.Asymptotics.LaplaceSaddle
public import DLMFMathlib.Analysis.Calculus.InverseSeries

public import DLMFMathlib.Analysis.ODE.Singularities

public import DLMFMathlib.Analysis.Complex.SeparatingContour
public import DLMFMathlib.Combinatorics.Q26bSurjections
public import DLMFMathlib.Combinatorics.R26aFinpartition
public import DLMFMathlib.Combinatorics.S26aQuadraticSeries
public import DLMFMathlib.Combinatorics.S26aSeriesTransform
public import DLMFMathlib.RingTheory.R27PowerSeriesEval
public import DLMFMathlib.Analysis.ODE.P2lSturmLiouville
public import DLMFMathlib.Analysis.ODE.P2sSturmSpectrum
public import DLMFMathlib.Analysis.ODE.P2sOscillation
public import DLMFMathlib.Analysis.ODE.P2sGrowth
public import DLMFMathlib.Analysis.ODE.P2sSturmOsc

/-!
# Supporting results for Mathlib

General results used by the special-function library but not specific to it, written in
the namespaces of the Mathlib APIs they extend. These modules import Mathlib only.

* `DLMFMathlib.Analysis.Complex.SegmentPrimitive`: straight-segment primitives and their derivatives.
* `DLMFMathlib.Analysis.Complex.StarPrimitive`: primitives of holomorphic functions on star-convex
  open sets.
* `DLMFMathlib.Analysis.Complex.BarnesResidue`: shifting a vertical-line integral across a simple
  pole (one-pole residue theorem on a strip).
* `DLMFMathlib.Analysis.Complex.ZeroLocalization`: existence and uniqueness of a zero near an
  approximate zero (contraction form of Newton–Kantorovich), with a filter version.
* `DLMFMathlib.Analysis.ContinuedFraction.Convergence`: convergence of generalized continued fractions
  through three-term recurrences (Pincherle, a ratio criterion, bracketing for positive elements).
* `DLMFMathlib.Analysis.SpecificLimits.Pincherle`: divergence of sums with ratio limit outside the unit
  disc, and convergence of a continued fraction from a backward solution with such a ratio limit.
* `DLMFMathlib.Analysis.Complex.FactorialSeries`: convergence and entireness of sparse factorial series.
* `DLMFMathlib.Analysis.Complex.TrigR4SeriesExtension`: uniqueness of power-series coefficients on a ball,
  extension of a power-series identity to the full disc of holomorphy, and even/odd coefficient criteria.
* `DLMFMathlib.Analysis.Complex.ParametricHolomorphy`: holomorphy of dominated parametric series and
  integrals in finite-dimensional complex parameters, and the continuous Osgood lemma.
* `DLMFMathlib.Topology.Order.ZeroEnumeration`: unique zeros of strictly monotone functions and the
  enumeration of zeros separated by a sequence of points.
* `DLMFMathlib.NumberTheory.EulerPolynomials`: Euler polynomials and Euler numbers.
* `DLMFMathlib.Analysis.ODE.P1oEntireLinear`, `P1oLinearGlobal`, `P1oParamHolomorphic`: entire
  solutions of linear second-order ODEs with entire coefficients, global solutions on ℝ for
  continuous coefficients, and holomorphic dependence on a linear parameter.
* `DLMFMathlib.Analysis.Fourier.P1a2EntirePeriodic`: an entire 2π-periodic function is the sum of
  its Fourier series on all of ℂ; cosine and sine series and Parseval for even and odd functions.
* `DLMFMathlib.Analysis.ODE.P2sSturmSpectrum`, `P2sGrowth`, `P2sOscillation`: spectra of real
  Sturm–Liouville problems through entire boundary functions, energy estimates, and infinitely
  many zeros when the coefficient tends to +∞.
* `DLMFMathlib.Analysis.ODE.P2lSturmLiouville`: separated Sturm–Liouville theory for
  `w'' = (V - h) w` on `[0, L]` (spectrum, discreteness, parity, comparison, enumeration).
* `DLMFMathlib.Analysis.ODE.P2sSturmOsc`: the Sturm oscillation theorem, Dirichlet and Neumann
  eigenvalue counts and their interlacing, and the sign of eigenfunctions at the endpoint.
* `DLMFMathlib.NumberTheory.T27aPrimeNumberTheorem`: the prime number theorem π(x) ~ x/log x,
  p_n ~ n log n, θ(x) ~ x, ψ(x) ~ x and primes in progressions, from TauCeti's prime ideal and
  Chebotarev theorems for ℚ.
* `DLMFMathlib.Analysis.EulerMaclaurin`: the Euler–Maclaurin summation formula with remainder.
* `DLMFMathlib.Analysis.BooleSummation`: Boole's alternating summation formula.
* `DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion`: Poincaré asymptotic expansions.
* `DLMFMathlib.Analysis.Asymptotics.Watson`: Watson's lemma for Laplace transforms.
* `DLMFMathlib.Analysis.Asymptotics.LaplaceSaddle`: all-orders Laplace expansions at an interior
  quadratic saddle through an analytic substitution (two-sided Gaussian form).
* `DLMFMathlib.Analysis.Asymptotics.StationaryPhase`: oscillatory integrals with a cubic stationary
  point at an endpoint.
* `DLMFMathlib.Analysis.Asymptotics.WatsonRotated`: rotation of Laplace rays, Watson's lemma along
  rotated rays, and gluing of asymptotic expansions on overlapping sectors.
* `ToMathlib.Analysis.Integral.Laplace`: quantitative Laplace asymptotics with a quadratic
  phase (a copy of the `lean-codes` module of the same path).
* `DLMFMathlib.Analysis.ODE.SturmComparison`: Sturm's comparison and separation theorems for
  `(p y')' + q y = 0`.
* `DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness`: uniqueness for second-order linear ODEs
  (analytic, via the Taylor recurrence; real-variable, via Gronwall) and 2×2 linear systems.
* `DLMFMathlib.Analysis.ODE.SoninePolya`: the Sonine–Pólya theorem on relative maxima.
* `DLMFMathlib.Analysis.ODE.Volterra`: the Volterra integral equation and Gronwall-type
  perturbation estimate for `u'' + ω² u = g u`.
* `DLMFMathlib.Combinatorics.Q26bSurjections`: counting surjections `Fin n → Fin k` (k!·S(n, k)
  and the alternating sum), and quotients of maps by permutations, for the twelvefold way.
* `DLMFMathlib.Combinatorics.R26aFinpartition`: finpartitions as fibres of surjections; surjections
  onto `Fin k` with a fibre-size condition number `k!` times the finpartitions with `k` parts.
* `DLMFMathlib.Combinatorics.S26aQuadraticSeries`: the Catalan series and the solution of
  `F = 1 + aXF + X^eF²` with its coefficients (Touchard, large Schröder numbers), binomial inversion.
* `DLMFMathlib.Combinatorics.S26aSeriesTransform`: summing `Σ c_k x^{ek} (1 - bx)^{-(2k+1)}` by
  diagonals; the central binomial series `Σ C(2k, k) y^k = 1/√(1 - 4y)`.
* `DLMFMathlib.RingTheory.R27PowerSeriesEval`: absolutely convergent evaluation of integer power
  series at a complex point, with its algebra (products, powers, `1 - X^k`, geometric series).
-/
