/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.GaussSum

/-!
# DLMF §§25.11–25.15: results already in Mathlib

Upstream pointers for the Hurwitz zeta function (Mathlib's parameter is in `ℝ/ℤ`, so it is DLMF's
`ζ(s, a)` only for `0 < a ≤ 1`), the periodic zeta function (`HurwitzZeta.expZeta`, DLMF's
`F(x, s)`) and Dirichlet `L`-functions (`DirichletCharacter.LFunction`). The pointers for 25.11.1
and 25.11.2 are in `DLMF.Core.UpstreamElementary`.
-/

/-! ### §25.11 Hurwitz zeta function -/

dlmf_upstream 25.11.i HurwitzZeta.differentiableAt_hurwitzZeta
  "partial: holomorphic in s ≠ 1, for Mathlib's real parameter a ∈ ℝ/ℤ"
dlmf_upstream 25.11.i HurwitzZeta.hurwitzZeta_residue_one
  "partial: simple pole at s = 1 with residue 1, real parameter a ∈ ℝ/ℤ"
dlmf_upstream 25.11.E14 HurwitzZeta.hurwitzZeta_neg_nat
  "special case: n ≥ 1, real 0 ≤ a ≤ 1 (Mathlib's parameter mod 1)"
dlmf_upstream 25.11.E33 harmonic "exact: Hₙ as a rational number"

/-! ### §25.13 Periodic zeta function -/

dlmf_upstream 25.13.E1 HurwitzZeta.hasSum_expZeta_of_one_lt_re
  "special case: Re s > 1, all real x; DLMF also has 0 < Re s ≤ 1 for x ∉ ℤ"
dlmf_upstream 25.13 HurwitzZeta.expZeta_zero "partial: F(0, s) = ζ(s)"
dlmf_upstream 25.13.E2 HurwitzZeta.expZeta_one_sub
  "stronger: functional equation for every s ≠ 1 - n, every real x mod 1, with s ↦ 1 - s"
dlmf_upstream 25.13.E3 HurwitzZeta.hurwitzZeta_one_sub
  "stronger: valid for s ≠ -n and (x ≢ 0 or s ≠ 1), every real x mod 1; (2π)^{-s} form"

/-! ### §25.15 Dirichlet `L`-functions -/

dlmf_upstream 25.15.E1 DirichletCharacter.LFunction_eq_LSeries
  "exact: Re s > 1, as Mathlib's LSeries (the tsum of χ(n)/n^s)"
dlmf_upstream 25.15.i DirichletCharacter.differentiable_LFunction "partial: entire for χ ≠ χ₁"
dlmf_upstream 25.15.i DirichletCharacter.differentiableAt_LFunction
  "partial: holomorphic at every s ≠ 1"
dlmf_upstream 25.15.i DirichletCharacter.LFunctionTrivChar_residue_one
  "partial: residue ∏_{p ∣ k} (1 - 1/p) at s = 1, which is φ(k)/k (DLMF.Zeta.LFunction_one_residue)"
dlmf_upstream 25.15.E2 DirichletCharacter.LSeries_eulerProduct_hasProd
  "exact: Re s > 1, as HasProd over the primes"
dlmf_upstream 25.15.E2 DirichletCharacter.LFunction_ne_zero_of_one_le_re
  "stronger: L(s, χ) ≠ 0 for Re s ≥ 1 (χ ≠ χ₁ or s ≠ 1)"
dlmf_upstream 25.15.E4 DirichletCharacter.LFunction_changeLevel
  "stronger: for any character χ₀ mod d with d ∣ k (not only primitive); needs χ₀ ≠ 1 or s ≠ 1"
dlmf_upstream 25.15.E5 DirichletCharacter.IsPrimitive.completedLFunction_one_sub
  "different convention: completed L-functions with the root number"
dlmf_upstream 25.15.E6 gaussSum
  "different convention: sum over all of ZMod k with an additive character; with ZMod.stdAddChar \
  it is DLMF's G(χ) for k ≥ 2 (DLMF.Zeta.gaussSum_stdAddChar_eq_sum)"
dlmf_upstream 25.15.E7 DirichletCharacter.Even.LFunction_neg_two_mul_nat
  "partial: n ≥ 1, for every even character (not only primitive)"
dlmf_upstream 25.15.E8 DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one
  "stronger: every odd character (not only primitive)"
dlmf_upstream 25.15.E9 DirichletCharacter.LFunction_apply_one_ne_zero "exact"
