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

This umbrella module collects the special values of the Jacobian elliptic functions: the values,
derivatives and residues of Table 22.5.1 at the lattice points, the quarter- and
three-quarter-period values of Table 22.5.2, the limits of `K` and `K'` (§22.5(ii)), the
limiting forms of Tables 22.5.3–22.5.4, and the bridges to the real-variable `sn, cn, dn`.

**Correction.** Table 22.5.1 prints `0, k` for `dc` at `z = K + iK'`; the derivative is `-k`
(from `dc(z) = ns(z + K)`, `ns(z + 2K) = -ns z` and `ns'(iK') = k`, and numerically).
-/
