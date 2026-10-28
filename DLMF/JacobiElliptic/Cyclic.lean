/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Cyclic.QuarterPeriodAndThreePoint
public import DLMF.JacobiElliptic.Cyclic.TripleProducts
public import DLMF.JacobiElliptic.Cyclic.MixedTripleProducts

/-!
# Jacobian elliptic functions: cyclic identities (DLMF §22.9)

The notation 22.9.1–22.9.6 (`s_{m,p}^{(N)} = sn(z + N p⁻¹(m - 1)K, k)` for `N = 2, 4`) and
`κ = dn(2K/3, k)` (22.9.7) are definitions; the cyclic identities 22.9.8–22.9.23 are proved
(stated at points where all functions involved are finite). For the shifts by `K` and `K/2`
(`p = 2, 4`) they follow from Table 22.4.3; for `p = 3` the points `z + 2K/3`, `z + 4K/3` are
expanded by the addition theorem, and the identities reduce to polynomial identities modulo
`sn² + cn² = 1`, `k² sn² + dn² = 1` and the duplication relations at `2K/3`
(`sn(4K/3) = sn(2K/3)`, `cn(4K/3) = -cn(2K/3)`), with certificates computed by Singular.

**Correction.** In 22.9.23 the right-hand side repeats `s_{2,3}^{(4)} d_{2,3}^{(4)}`; the
numerically correct last summand is `s_{3,3}^{(4)} d_{3,3}^{(4)}` (e.g. `k = 0.6`,
`z = 0.37 + 0.21i`: printed right side `≈ 4.208 - 0.036i`, left side `≈ 0.552 + 0.183i`,
corrected right side equal to the left side).
-/
