/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.Continuation.LogarithmicBranches
public import DLMF.Legendre.Continuation.SquareHypergeometric
public import DLMF.Legendre.Continuation.Monodromy
public import DLMF.Legendre.Continuation.ContinuityAndConnections

/-!
# Legendre boundary values and continuation by ODE transport

This umbrella module collects the boundary values of the Legendre functions on the cut
`(-1, 1)` (DLMF §14.23) and their analytic continuation beyond the principal sheet by
transport along paths (DLMF §14.24): continuation around ellipses and around the singular
point `1`.
-/
