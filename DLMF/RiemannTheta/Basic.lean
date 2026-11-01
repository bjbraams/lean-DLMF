/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.RiemannTheta.Basic.Definitions

/-!
# Riemann theta functions (DLMF §§21.1–21.2)

This file collects the foundational definitions of the Riemann theta functions
(`DLMF.RiemannTheta.Basic.Definitions`): Riemann matrices and the Siegel upper half-space, the
theta series `θ(z|Ω)`, its scaled form and the theta functions with characteristics. The
analytic properties are in `DLMF.RiemannTheta.Convergence`, and the scaled functions and
characteristic identities in `DLMF.RiemannTheta.Scaled` and
`DLMF.RiemannTheta.Characteristics`.
-/
