/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Basic.Definitions
public import DLMF.JacobiElliptic.Basic.Properties
public import DLMF.JacobiElliptic.Basic.ThetaShifts
public import DLMF.JacobiElliptic.Basic.Inverse
public import DLMF.JacobiElliptic.Basic.Epsilon

/-!
# Jacobian elliptic functions: definitions (DLMF §22.2)

This entry point collects the definitions of the twelve Jacobian elliptic functions `pq(z, k)`
(Glaisher's notation: `p, q ∈ {s, c, d, n}`, `pp = 1`) as quotients of theta functions with
nome `q = exp(-π K'(k)/K(k))` and argument `ζ = π z/(2K(k))`, in lattice and modulus form,
with Glaisher's relations, parity and the quarter-period shifts of the theta functions; the
inverse functions of DLMF §22.15 with their principal ranges; and Jacobi's Epsilon and Zeta
functions (DLMF §22.16).
-/
