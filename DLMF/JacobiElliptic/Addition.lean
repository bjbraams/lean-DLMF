/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Addition.SymmetricAndThreePoint
public import DLMF.JacobiElliptic.Addition.ThetaAndQuotients

/-!
# Jacobian elliptic functions: addition theorems (DLMF §22.8)

This umbrella module collects the addition theorems DLMF 22.8.1–22.8.27 for the Jacobian
elliptic functions: the theta-function proofs of the basic addition theorems and their quotient
forms, and the symmetric, four-point and three-point identities.

The addition theorems are stated pointwise for complex `u`, `v` where the functions involved
are finite and the printed denominator is nonzero. They are proved from the theta-function
product identities of §20.7: each formula reduces, after `k = θ₂²(0)/θ₃²(0)`,
`k' = θ₄²(0)/θ₃²(0)` (22.2.2) and clearing denominators, to one identity
`θ_p(0)θ_q(0) θ_p(u+v)θ_q(u-v) = …` (derived from Watson's formulas 20.7.13 and the
Landen-type products) and one identity of the form 20.7.6–20.7.9. DLMF 22.8.23 as printed is
false; corrected forms are stated in the symmetric-identities module.
-/
