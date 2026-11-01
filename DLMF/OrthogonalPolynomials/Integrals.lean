/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations
public import DLMF.OrthogonalPolynomials.Integrals.GegenbauerAndLegendre
public import DLMF.OrthogonalPolynomials.Integrals.LaguerreAndHermite
public import DLMF.OrthogonalPolynomials.Integrals.ConvolutionsAndFourier
public import DLMF.OrthogonalPolynomials.Integrals.BesselAndLaguerreTransforms
public import DLMF.OrthogonalPolynomials.Integrals.DoubleLaplaceAndGaussian

/-!
# Integrals of classical orthogonal polynomials

Integral identities for the classical orthogonal polynomials from DLMF Chapter 18:
orthogonality and norms (§18.3), Rodrigues formulas (§18.5), Dirichlet–Mehler integrals
(§18.10), and the integrals and transforms of §18.17 (product formulas, convolutions,
fractional integrals, Fourier, Laplace, Mellin and Bessel-type transforms).

Jacobi and Gegenbauer statements keep regularity hypotheses because the hypergeometric
definitions used here are not continued in singular parameters. Integrable endpoint
singularities are retained wherever the integrals converge.
-/
