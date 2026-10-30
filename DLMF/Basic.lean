/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Airy.Basic
public import DLMF.AlgebraicAnalytic.Algebra.Basic
public import DLMF.AlgebraicAnalytic.Calculus.Basic
public import DLMF.AlgebraicAnalytic.Complex.Basic
public import DLMF.AlgebraicAnalytic.ContinuedFractions.Basic
public import DLMF.AlgebraicAnalytic.Distributions.Basic
public import DLMF.AlgebraicAnalytic.Fourier.Basic
public import DLMF.AlgebraicAnalytic.ODE.Basic
public import DLMF.AlgebraicAnalytic.Polynomials.Basic
public import DLMF.AlgebraicAnalytic.Spectral.Basic
public import DLMF.AlgebraicAnalytic.Summability.Basic
public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import DLMF.AsymptoticApproximations.Basics.Basic
public import DLMF.AsymptoticApproximations.Distributional.Basic
public import DLMF.AsymptoticApproximations.Integrals.Basic
public import DLMF.AsymptoticApproximations.Mellin.Basic
public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMF.AsymptoticApproximations.Remainders.Basic
public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.BernoulliEuler.Basic
public import DLMF.Bessel.Basic
public import DLMF.CoalescingSaddles.Basic
public import DLMF.Combinatorics.Basic
public import DLMF.Confluent.Basic
public import DLMF.Coulomb.Basic
public import DLMF.Coulomb.Energy.Basic
public import DLMF.Elliptic.Basic
public import DLMF.EllipticIntegrals.Basic
public import DLMF.ErrorFunctions.Basic
public import DLMF.ExpIntegrals.Basic
public import DLMF.Gamma.Basic
public import DLMF.GeneralizedHypergeometric.Appell.Basic
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Heun.Basic
public import DLMF.Hypergeometric.Basic
public import DLMF.IncompleteGamma.Basic
public import DLMF.JacobiElliptic.Basic
public import DLMF.Lame.Basic
public import DLMF.Lame.Polynomials.Basic
public import DLMF.Legendre.Basic
public import DLMF.Mathieu.Basic
public import DLMF.Mathieu.Hill.Basic
public import DLMF.Mathieu.Modified.Basic
public import DLMF.Mathieu.Noninteger.Basic
public import DLMF.MatrixArgument.Basic
public import DLMF.OrthogonalPolynomials.Basic
public import DLMF.Painleve.Basic
public import DLMF.ParabolicCylinder.Basic
public import DLMF.Polylog.Basic
public import DLMF.QHypergeometric.Basic
public import DLMF.QSeries.Basic
public import DLMF.RiemannTheta.Basic
public import DLMF.Selberg.Basic
public import DLMF.SphericalHarmonics.Basic
public import DLMF.Spheroidal.Basic
public import DLMF.Statistical.Basic
public import DLMF.Struve.Basic
public import DLMF.Theta.Basic
public import DLMF.Weierstrass.Basic
public import DLMF.WignerSymbols.Basic

/-!
# The foundational DLMF collection

This entry point imports all `Basic.lean` entry points and their foundational `Basic/`
submodules. It exposes the organized definitions and their minimal supporting APIs;
substantive differential, integral, asymptotic and transformation developments remain in
separate theorem modules. External libraries, `DLMFMathlib` and `DLMF.Core.*` provide the
general mathematical framework. The definitions inventories document further DLMF
correspondences, including auxiliary constructions in theorem developments.
-/
