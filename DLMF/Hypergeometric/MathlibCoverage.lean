/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# DLMF Chapter 15 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations,
deliberately not duplicate local theorems (see also `DLMF.Hypergeometric.AnalyticProperties`).
Mathlib's `ordinaryHypergeometric` (`₂F₁`) and `Complex.regularizedGaussHGFun` are sums of
formal power series: outside the disk of convergence they are not DLMF's analytic
continuations, and `₂F₁` divides by `(c)_s`, so it is totalized (terms with `(c)_s = 0`
vanish) when `c ∈ -ℕ`. For the same reason
`ordinaryHypergeometric_radius_top_of_neg_nat₃` (the totalized negative-denominator series) is
not recorded as a DLMF pointer. Mathlib's value at zero (`ordinaryHypergeometric_zero`) and
numerator symmetry (`ordinaryHypergeometricSeries_symm`, `Complex.regularizedGaussHGFun_symm`)
are immediate from 15.2.1–15.2.2 and have no DLMF equation number of their own.
-/

-- DLMF 15.2.1: the Gauss series.
dlmf_upstream 15.2.E1 ordinaryHypergeometric_eq_tsum
  "partial: first equality on |z| < 1, c ∉ -ℕ; Mathlib's ₂F₁ is the sum of the series, not \
  the continuation, and is totalized for c ∈ -ℕ"
dlmf_upstream 15.2.E1 ordinaryHypergeometricSeries_apply_eq
  "partial: the s-th term (a)_s (b)_s / ((c)_s s!) z^s of the Gauss series"

-- DLMF 15.2.2: Olver's regularized function `𝐅`.
dlmf_upstream 15.2.E2 Complex.regularizedGaussHGFun
  "exact: on |z| < 1 the sum of the series, for all c (1/Γ(c+s) is 0 at the poles); \
  Mathlib has no continuation to |z| ≥ 1"
dlmf_upstream 15.2.E2 Complex.coeff_regularizedGaussHGFunSeries
  "partial: the coefficients (a)_s (b)_s / (Γ(c+s) s!)"
dlmf_upstream 15.2.E2 Complex.ordinaryHypergeometric_div_Gamma_eq
  "partial: 𝐅(a,b;c;z) = F(a,b;c;z)/Γ(c) for c ∉ -ℕ, relating 15.2.2 to 15.2.1"

-- §15.2(i): the radius of convergence of the Gauss series.
dlmf_upstream 15.2.i ordinaryHypergeometricSeries_radius_eq_one
  "partial: the Gauss series has radius of convergence 1 when none of a, b, c is in -ℕ"
dlmf_upstream 15.2.i ordinaryHypergeometric_radius_top_of_neg_nat₁
  "partial: terminating case a ∈ -ℕ, infinite radius (polynomial)"
dlmf_upstream 15.2.i ordinaryHypergeometric_radius_top_of_neg_nat₂
  "partial: terminating case b ∈ -ℕ, infinite radius (polynomial)"

-- DLMF 15.12.6, used directly in `large_opposite_parameters_bessel`.
dlmf_upstream 15.12.E6 Real.arcosh
  "special case: real z ≥ 1, where Real.arcosh z = log(z + √(z²-1)) is the principal arccosh"
