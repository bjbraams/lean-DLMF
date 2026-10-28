/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Theta.Products.InfiniteProducts
public import DLMF.Theta.Products.LogDerivativesAndDoubleProducts

/-!
# Theta functions: infinite products and related results (DLMF §20.5)

Single products (20.5.1–20.5.8), Jacobi's triple product in theta form (20.5.9), the
logarithmic derivatives (20.5.10–20.5.13) and the Eisenstein-ordered double products
(20.5.14–20.5.17). Throughout `q = e^{iπτ}`, `q^{1/4} = e^{iπτ/4}` and `Im τ > 0`.
Products over `n ≥ 1` are `HasProd` statements over `k : ℕ` with `n = k + 1`.

The triple product `DLMF.QSeries.jacobi_triple_product` (DLMF 17.8.1) is the source of the
product formulas.

In 20.5.10 and 20.5.11 the left-hand sides are meromorphic with removable singularities at the
real zeros of `θ₁`, resp. `θ₂`; with Lean's conventions `x / 0 = 0` both sides vanish there, so
the statements hold on the whole strip.
-/
