/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.EllipticIntegrals.Connection.CompleteIntegrals
public import DLMF.EllipticIntegrals.Connection.ModulusChanges
public import DLMF.EllipticIntegrals.Connection.ParameterChanges

/-!
# Connection formulas for Legendre's integrals (DLMF §19.7)

This umbrella collects DLMF 19.7.1–19.7.10: Legendre's relation and the modulus changes of the
complete integrals, the reciprocal- and imaginary-modulus transformations of the incomplete
integrals, and the imaginary-argument and parameter changes. Here `k' = jacobiComodulusk k`
(principal), `c = csc²φ` and `R_C = symEllIntRC`.
-/
