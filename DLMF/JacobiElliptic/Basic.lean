/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Basic.Definitions

/-!
# Jacobian elliptic functions: definitions (DLMF §22.2)

This entry point collects the definitions of the twelve Jacobian elliptic functions `pq(z, k)`
(Glaisher's notation: `p, q ∈ {s, c, d, n}`, `pp = 1`) as quotients of theta functions with
nome `q = exp(-π K'(k)/K(k))` and argument `ζ = π z/(2K(k))`, in lattice and modulus form.
-/
