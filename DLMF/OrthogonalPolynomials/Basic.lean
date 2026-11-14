/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation

public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import DLMF.OrthogonalPolynomials.Basic.Classical
public import DLMF.OrthogonalPolynomials.Basic.General
public import DLMF.OrthogonalPolynomials.Basic.NormsAndKernels
public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme
public import DLMF.OrthogonalPolynomials.Basic.QFamilies
public import DLMF.OrthogonalPolynomials.Basic.Associated

/-!
# Orthogonal polynomials: the foundational layer

The foundational entry point for orthogonal polynomials (DLMF Chapter 18).

* `OrthogonalPolynomials.Basic.Definitions`: the physicists' Hermite, Laguerre, Jacobi,
  Legendre, Gegenbauer and Chebyshev `V`, `W` polynomials.
* `OrthogonalPolynomials.Basic.Classical`: initial values, endpoint values, parity and the
  bridges to Mathlib's Hermite, shifted Legendre and Chebyshev polynomials.
* `OrthogonalPolynomials.Basic.General`: orthogonal polynomials with respect to a measure, the
  three-term recurrence and the Christoffel–Darboux formula (DLMF §18.2).
* `OrthogonalPolynomials.Basic.NormsAndKernels`: squared norms, kernels, moments and Hankel
  determinants (DLMF §18.2).
* `OrthogonalPolynomials.Basic.AskeyScheme`: the Hahn and Wilson classes (DLMF §§18.19–18.26).
* `OrthogonalPolynomials.Basic.QFamilies`: the `q`-families (DLMF §§18.27–18.28).
* `OrthogonalPolynomials.Basic.Associated`: associated, Bessel and Pollaczek polynomials
  (DLMF §§18.30, 18.34, 18.35).
-/
