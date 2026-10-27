/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Theta.Basic
public import DLMF.Theta.ZeroValues
public import DLMF.Theta.Products
public import DLMF.Theta.PowerSeries
public import DLMF.Theta.Identities
public import DLMF.Theta.Relations
public import DLMF.Theta.Integrals
public import DLMF.Theta.Generalizations
public import DLMF.Theta.MathlibCoverage

/-!
# Theta functions (DLMF Chapter 20)

The Jacobi theta functions `θⱼ(z|τ)` are `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`
(DLMF normalization, from Mathlib's `jacobiTheta₂`). This area acquires DLMF §§20.2, 20.4–20.11:

* `Basic`: nome forms `θⱼ(z,q)`, theta constants, Fourier series, quasi-periodicity, half-period
  translations and zeros (§§20.1–20.2);
* `ZeroValues`: values and derivatives at `z = 0` (§20.4);
* `Products`: single and double products, triple product, logarithmic derivatives (§20.5);
* `PowerSeries`: exponential power series and lattice sums (§20.6);
* `Identities`: sums of squares, addition, duplication, Landen, Watson, lattice-parameter
  transformations (§20.7) and Watson's expansion (§20.8);
* `Relations`: elliptic integrals, Jacobi's inversion problem, the modular function (§20.9);
* `Integrals`: Mellin and Laplace transforms in the lattice parameter (§20.10);
* `Generalizations`: Gauss sums, Ramanujan's `f(a,b)`, change of base, Carlson's combined theta
  functions (§20.11);
* `MathlibCoverage`: checked pointers to Mathlib.

The ledger is `DLMF20Acquisition.md`.
-/
