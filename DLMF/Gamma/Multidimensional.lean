/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.Multidimensional.SelbergLimits
public import DLMF.Gamma.Multidimensional.Dyson
public import DLMF.Gamma.Multidimensional.Liouville

/-!
# Multidimensional integrals (DLMF §5.14)

This umbrella imports Dirichlet's simplex integrals 5.14.1–5.14.2 (from the solid-simplex
evaluation of the multivariate Beta function in lean-codes, `Dirichlet.Beta.Complex.Integral`),
the Laguerre and Hermite forms 5.14.5–5.14.6 of the Selberg integral, obtained as limits of the
Selberg integral, and Dyson's circular integral 5.14.7, obtained from Good's proof of Dyson's
constant-term identity and Carlson's theorem. `Δ` is the Vandermonde product 5.14.3. The
Selberg and Aomoto identities 5.14.4 are in `DLMF.Selberg.Basic`.
-/
