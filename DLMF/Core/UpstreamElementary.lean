/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import DLMF.Elementary.MathlibCoverage
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF Chapters 24 and 25: central results already in Mathlib

The former selected Chapter 4 pointers now live in
`DLMF.Elementary.MathlibCoverage`, publicly imported here for compatibility.
This file retains the Bernoulli and zeta pointers. Mathlib's `bernoulli` uses
`B₁=-1/2`, `bernoulli'` uses `B'₁=+1/2`, and its Hurwitz-zeta parameter is in `ℝ/ℤ`.
-/

/-! ### Chapter 24: Bernoulli numbers and polynomials -/

dlmf_upstream 24.2.E2 bernoulli_eq_zero_of_odd "partial: first relation B_{2n+1} = 0, n ≥ 1"
dlmf_upstream 24.2.E3 Polynomial.bernoulli_generating_function
  "different convention: identity of formal power series over a ℚ-algebra, \
  (Σ B_n(t) Xⁿ/n!)(e^X - 1) = X e^{tX}; no convergence statement for |t| < 2π"
dlmf_upstream 24.2.E4 Polynomial.bernoulli_eval_zero "exact"
dlmf_upstream 24.2.E5 Polynomial.bernoulli "exact: definition, in ℚ[X]"
dlmf_upstream 24.4.E1 Polynomial.bernoulli_comp_one_add_X
  "exact: as the polynomial identity B_n(1+X) = B_n(X) + n X^{n-1} in ℚ[X]"
dlmf_upstream 24.4.E3 Polynomial.bernoulli_comp_one_sub_X
  "exact: as the polynomial identity B_n(1-X) = (-1)ⁿ B_n(X) in ℚ[X]"
dlmf_upstream 24.4.E7 Polynomial.sum_range_pow_eq_bernoulli_sub
  "exact: n ≥ 1, as (n+1) Σ_{k=0}^{m} kⁿ = B_{n+1}(m+1) - B_{n+1}; for n = 0 Mathlib's sum \
  includes 0⁰ = 1, while the printed sum from k = 1 is off by one"
dlmf_upstream 24.4.E18 bernoulliFun_mul "exact: real x, m ≥ 1"
dlmf_upstream 24.4.E25 Polynomial.bernoulli_eval_zero "partial: B_n(0) = B_n"
dlmf_upstream 24.4.E25 Polynomial.bernoulli_eval_one
  "different convention: B_n(1) = bernoulli' n, Mathlib's B'_n = (-1)ⁿ B_n"
dlmf_upstream 24.4.E27 bernoulliFun_eval_half "exact: in the form (2/2ⁿ - 1) B_n"
dlmf_upstream 24.4.E34 Polynomial.derivative_bernoulli "exact: as polynomials over ℚ"
dlmf_upstream 24.8.E1 hasSum_one_div_nat_pow_mul_cos
  "exact: n ≥ 1, 0 ≤ x ≤ 1, as the sum of the cosine series"
dlmf_upstream 24.8.E2 hasSum_one_div_nat_pow_mul_sin
  "special case: n ≥ 1, 0 ≤ x ≤ 1 (DLMF also allows n = 0 for 0 < x < 1)"
dlmf_upstream 24.8.E3 hasSum_one_div_pow_mul_fourier_mul_bernoulliFun
  "special case: n ≥ 2, 0 ≤ x ≤ 1 (DLMF also allows n = 1 for 0 < x < 1); the k = 0 term is \
  Mathlib's 1/0 = 0"
dlmf_upstream 24.13.E1 antideriv_bernoulliFun "exact: real t, as HasDerivAt of B_{n+1}(t)/(n+1)"
dlmf_upstream 24.13.E2 integral_bernoulliFun_eq_zero "special case: x = 0, n ≥ 1"

/-! ### Chapter 25: Riemann and Hurwitz zeta functions -/

dlmf_upstream 25.2.E1 zeta_eq_tsum_one_div_nat_cpow
  "exact: Re s > 1 (the n = 0 term is Mathlib's 0^s = 0)"
dlmf_upstream 25.2.i riemannZeta_residue_one "partial: the simple pole at s = 1 has residue 1"
dlmf_upstream 25.2.i differentiableAt_riemannZeta
  "partial: ζ is holomorphic on ℂ \\ {1}; Mathlib's value at s = 1 is totalized"
dlmf_upstream 25.2.E4 tendsto_riemannZeta_sub_one_div
  "partial: constant term γ₀ = γ of the Laurent expansion at s = 1"
dlmf_upstream 25.2.E11 riemannZeta_eulerProduct_tprod "exact: Re s > 1"
dlmf_upstream 25.4.E1 riemannZeta_one_sub
  "exact: s ∉ {1, 0, -1, -2, …}, where every factor is defined"
dlmf_upstream 25.4.E3 completedRiemannZeta_one_sub
  "different convention: Λ(s) = π^{-s/2} Γ(s/2) ζ(s), without the factor s(s-1)/2 of ξ(s)"
dlmf_upstream 25.6.E1 riemannZeta_zero "partial: ζ(0) = -1/2"
dlmf_upstream 25.6.E1 riemannZeta_two "partial: ζ(2) = π²/6"
dlmf_upstream 25.6.E2 riemannZeta_two_mul_nat
  "exact: n ≥ 1, with (-1)^{n+1} B_{2n} in place of |B_{2n}| (equal by 24.2.2)"
dlmf_upstream 25.6.E3 riemannZeta_neg_nat_eq_bernoulli
  "stronger: ζ(-n) = (-1)ⁿ B_{n+1}/(n+1), valid also for n = 0"
dlmf_upstream 25.11.E1 HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
  "special case: real 0 ≤ a ≤ 1, Re s > 1; Mathlib's a lives in ℝ/ℤ and the a = 0 series \
  (n = 0 term 0^{-s} = 0) is ζ(s, 1)"
dlmf_upstream 25.11.E2 HurwitzZeta.hurwitzZeta_zero
  "different convention: Mathlib's parameter is a mod 1, so a = 1 is hurwitzZeta 0"
