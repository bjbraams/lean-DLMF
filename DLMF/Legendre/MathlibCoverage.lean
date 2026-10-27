/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# DLMF Chapter 14 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations,
deliberately not duplicate local theorems. The affine normalization between Mathlib's
shifted Legendre polynomial and `P_n` is the project theorem
`DLMF.OrthogonalPolynomials.aeval_shiftedLegendre_eq_legendrePolyP`.
-/

-- DLMF 14.7.13: Rodrigues' formula, for the shifted Legendre polynomial `P_n(1-2x)`.
dlmf_upstream 14.7.E13 Polynomial.factorial_mul_shiftedLegendre_eq
  "different convention: Rodrigues' formula for P̃_n(x) = P_n(1-2x), \
  n! P̃_n = dⁿ/dxⁿ (xⁿ(1-x)ⁿ), in ℤ[X]"
