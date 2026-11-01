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

This umbrella module collects Table 22.13.1 of derivatives and the first- and second-order
differential equations 22.13.1–22.13.24, for complex `z` and `k ∈ jacobiModulusDomain` and for
real argument and real parameter `m = k² < 1`.

The complex derivatives are proved from the theta-function Wronskians
`θ_p'θ_q - θ_pθ_q' = const · θ_rθ_s`, obtained by differentiating the mixed product identities
of the addition theorems at `v = 0` and using `θ₁'(0) = θ₂(0)θ₃(0)θ₄(0)` and
`K = (π/2)θ₃²(0)` (22.2.2); the differential equations follow with the sums of squares
(22.6.1–22.6.4). The real forms for the nine quotient functions are proved from the real
`sn, cn, dn` of `DLMF.Elliptic.Jacobi` and `DLMF.Elliptic.JacobiIdentities`, where the real
forms for `sn, cn, dn` themselves live.

Poles carry Lean's junk value `x / 0 = 0`, so every complex statement assumes that `z` is not a
pole of the function concerned (the theta function of the second letter does not vanish at
`ζ = πz/(2K)`); real statements assume `cn x ≠ 0` or `sn x ≠ 0` where DLMF divides.
In the real forms `k'² = 1 - m`.
-/
