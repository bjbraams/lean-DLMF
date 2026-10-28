/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Addition.ThetaAndQuotients
public import DLMF.JacobiElliptic.Addition.SymmetricAndThreePoint

/-!
# Jacobian elliptic functions: addition theorems (DLMF §22.8)

The addition theorems 22.8.1–22.8.18 are stated pointwise for complex `u`, `v` where the
functions involved are finite (`jacobiRegulark`) and the printed denominator is nonzero. They
are proved from the theta-function product identities of §20.7: each formula reduces, after
`k = θ₂²(0)/θ₃²(0)`, `k' = θ₄²(0)/θ₃²(0)` (22.2.2) and clearing denominators, to one identity
`θ_p(0)θ_q(0) θ_p(u+v)θ_q(u-v) = …` (derived from Watson's formulas 20.7.13 and the
Landen-type products) and one identity of the form 20.7.6–20.7.9. The four-point identities
22.8.19–22.8.23 are admitted; 22.8.24–22.8.25 are proved from the values at `2K/3` and the
addition theorem, and 22.8.27 follows from Table 22.4.3.

**Correction.** DLMF 22.8.23 as printed (columns `sn cn, cn dn, cn, dn` with
`z₁ + z₂ + z₃ + z₄ = 2K`) fails numerically (e.g. `k = 0.6`, determinant `≈ -0.107 + 0.033i`).
Replacing the third column by `sn`, or the second by `sn dn`, gives true identities; both are
acquired (`jacobi_det_sum_two_K`, `jacobi_det_sum_two_K'`).
-/
