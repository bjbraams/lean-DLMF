/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.SpecialValues.ThetaValues
public import DLMF.JacobiElliptic.SpecialValues.DerivativesAndResidues
public import DLMF.JacobiElliptic.SpecialValues.RealAndHalfPeriods
public import DLMF.JacobiElliptic.SpecialValues.ModulusLimits

/-!
# Jacobian elliptic functions: special values (DLMF §22.5)

The values in Table 22.5.1 follow from the values at `z = 0` (`θ₁(0) = 0`, nonvanishing theta
constants) and the shift Table 22.4.3; they are proved (in the modulus form, via the inversion
22.2.2). The derivatives and residues of Table 22.5.1 are proved from the derivatives of
Table 22.13.1 at `z = 0` and the shift Table 22.4.3. The values at quarter- and
three-quarter-periods of Table 22.5.2 are proved: their squares follow from Table 22.4.3 and
the addition theorem, and the principal square roots are selected by the identity theorem in
`k` from the real case `0 < k < 1` (via the real bridges `jacobiSnk_ofReal` etc., proved here
by ODE uniqueness); the `iK'/2` values use Jacobi's imaginary transformation. The limits
`K(k) → ∞`, `K'(k) → ∞` (§22.5(ii)) are proved from `K(1 - δ²) ≥ log(π/(2δ))/√2`. The limiting
forms of Table 22.5.3 (`k → 0+`) are proved from `Im τ(k) → ∞`, `πz/(2K) → z` and the
limits of the normalized theta functions (dominated convergence of the theta series); those of
Table 22.5.4 (`k → 1-`) follow from them by Jacobi's imaginary transformation.

**Correction.** Table 22.5.1 prints `0, k` for `dc` at `z = K + iK'`; the derivative is `-k`
(from `dc(z) = ns(z + K)`, `ns(z + 2K) = -ns z` and `ns'(iK') = k`, and numerically).
-/
