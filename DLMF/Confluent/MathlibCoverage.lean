/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# DLMF Chapter 13 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations,
deliberately not duplicate local theorems; Mathlib's cross-reference attribute cannot modify
documentation on imported declarations.

Mathlib does not define named Kummer `M`, Tricomi `U`, or Whittaker `M_{κ,μ}`,
`W_{κ,μ}`. Olver's regularized `𝐌(a,b,z)` is `regularizedHGFun {a} {b}`.

Not recorded as pointers, because Mathlib does not state the DLMF equation itself:
* DLMF 13.2.4, `M(a,b,z) = Γ(b) 𝐌(a,b,z)` at regular `b`, is the project theorem
  `kummerM_eq_mul_regularizedHGFun`.
* DLMF 13.6.21: Mathlib's `regularizedHGFun {a, a - b + 1} ∅` supplies the (terminating)
  regularized `{}_2F_0` series used there, but Mathlib has no `U`.
* DLMF 13.10.3 (and 13.10.7, 13.23.1, 13.23.4) uses Mathlib's Gaussian `{}_2F_1`
  (`ordinaryHypergeometric` / `Complex.regularizedGaussHGFun`); the Laplace transforms
  themselves are project theorems.
-/

-- `regularizedHGFun {a} {b}` is Olver's `𝐌(a,b,z)`.
dlmf_upstream 13.2.E3 Complex.regularizedHGFun
  "exact: 𝐌(a,b,z) = regularizedHGFun {a} {b} z, the sum of the entire series; the \
  coefficient 1/Γ(b+s) is 0 at the poles, as in DLMF"

-- The series coefficients of `𝐌`; project: `regularizedHGFunCoeff_singleton`.
dlmf_upstream 13.2.E3 Complex.regularizedHGFunCoeff
  "partial: the coefficients (a)_s/(s! Γ(b+s)) of 13.2.3, as regularizedHGFunCoeff {a} {b} s"

-- Infinite radius of the regularized confluent series.
dlmf_upstream 13.2.E3 Complex.radius_regularizedHGFunSeries_eq_top
  "partial: the series of 13.2.3 converges for all z (case p = q = 1 of p ≤ q)"
