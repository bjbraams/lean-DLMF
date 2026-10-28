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

Statements of DLMF 19.7.1–19.7.10. Legendre's relation (19.7.1) is proved for real `0 < k < 1`
from the existing real `DLMF.Elliptic.legendre_relation`. On the complex domain it follows by the
identity theorem on `Re k > 0`, by evenness in `k` for `Re k < 0`, and on the imaginary axis by a
one-sided limit from `Re k > 0` (dominated convergence across the cut of `K(k')` and `E(k')`).
19.7.2 is proved by the identity theorem from the real substitution `θ ↦ π/2 - θ`.
The modulus transformations 19.7.2–19.7.3 are stated for complex `k`; the transformations
19.7.4–19.7.7 for the real amplitudes on which DLMF states them (19.7.7 with complex `k`); the
parameter changes 19.7.8–19.7.10 for real data, with Cauchy principal values. Here
`k' = jacobiComodulusk k` (principal), `c = csc²φ` and `R_C = symEllIntRC`.

**Convention note.** DLMF prints the second and fourth formulas of 19.7.2,
`K(-ik'/k) = kK(k')` and `E(-ik'/k) = (1/k)E(k')`, without a condition; their left sides are even
in `k` (they depend on `k²` only) and the right sides odd, so they hold for `Re k > 0` (as in
19.7.3, which DLMF states for `Re k > 0`) and change sign for `Re k < 0`; checked numerically
with mpmath at `k = 0.6, 0.5 + 0.3i, 1.3 + 0.5i, 0.3 - 0.9i` (valid) and `k = -0.4 + 0.7i,
-1.3 + 0.5i, -0.3 - 2i` (sign reversed). They are acquired with `0 < Re k`.
-/
