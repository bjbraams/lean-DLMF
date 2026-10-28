/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Derivatives.ThetaWronskians
public import DLMF.JacobiElliptic.Derivatives.ComplexEquations
public import DLMF.JacobiElliptic.Derivatives.RealEquations

/-!
# Derivatives and differential equations of the Jacobian elliptic functions (DLMF §22.13)

* **Table 22.13.1** (`22.13.T1`): each derivative `d pq(z,k)/dz` is a constant multiple of the
  product of the two copolar functions. For complex `z` and `k ∈ jacobiModulusDomain` these are
  stated for the theta-quotient functions `jacobiSnk … jacobiCsk` of `DLMF.JacobiElliptic.Basic`
  away from the poles (the theta function in the denominator is nonzero). They are proved from
  the theta-function Wronskians `θ_p'θ_q - θ_pθ_q' = const · θ_rθ_s`, obtained by differentiating
  the mixed product identities of `DLMF.JacobiElliptic.Addition` at `v = 0` and using
  `θ₁'(0) = θ₂(0)θ₃(0)θ₄(0)`, together with `K = (π/2)θ₃²(0)` (22.2.2).
  For real argument and real parameter `m = k² < 1` the nine quotient functions
  `sd, cd, nd, dc, nc, sc, ns, ds, cs` are proved from the existing real `sn, cn, dn`
  (`DLMF.Elliptic.Real.hasDerivAt_jacobiSnm` …); the three basic entries for real argument are
  `Real.hasDerivAt_jacobiSnm`, `Real.hasDerivAt_jacobiCnm`, `Real.hasDerivAt_jacobiDnm` in
  `DLMF.Elliptic.Jacobi`.
* **First-order equations** 22.13.1–22.13.12 and **second-order equations** 22.13.13–22.13.24:
  complex forms proved from Table 22.13.1 and the sums of squares (22.6.1–22.6.4);
  real-argument forms proved for the nine quotient functions (first order) and for `cd, sd, nd`
  (second order, no real poles). For `sn, cn, dn` the real forms are
  `Real.jacobiSnm_deriv_sq` … and `Real.iteratedDeriv_two_jacobiSnm` …
  in `DLMF.Elliptic.JacobiIdentities`.

Poles carry Lean's junk value `x / 0 = 0`, so every complex statement assumes that `z` is not a
pole of the function concerned (the theta function of the second letter does not vanish at
`ζ = πz/(2K)`); real statements assume `cn x ≠ 0` or `sn x ≠ 0` where DLMF divides.
In the real forms `k'² = 1 - m`.
-/
