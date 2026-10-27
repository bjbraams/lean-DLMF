/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.QSeries.Identities
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# DLMF Chapter 18 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations,
deliberately not duplicate local theorems; Mathlib's cross-reference attribute cannot modify
documentation on imported declarations. Some polynomial normalizations differ; notably
Mathlib's shifted Legendre is `P_n(1 - 2x)`, and `hermite` is the probabilists' family `He_n`.
Mathlib's Chebyshev polynomials `T R n`, `U R n` are indexed by `n : ℤ` over a commutative ring.

DLMF items that Mathlib already tags with `@[dlmf]` get no pointer here: 18.5.1
(`T_real_cos`, `T_real_cosh`; also `T_complex_cos`), 18.5.2 (`U_real_cos`, `U_real_cosh`; also
`U_complex_cos`), 18.9.9 (`two_mul_T_eq_U_sub_U`), 18.9.21 (`T_derivative_eq_U`) and 18.18.21
(`T_mul_T`). The untagged rearrangement `U_eq_two_mul_T_add_U` of 18.9.9 does get a pointer.

`Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff` (`|T_n(x)| = 1` iff `x = cos(kπ/n)`) was
formerly listed under Table 18.6.1, which does not contain it; it has no DLMF pointer.

DLMF 18.1(i) repeats the q-Pochhammer definitions from Chapter 17; the single project
definitions `qPochhammer`, `qPochhammerInf` are in DLMF/QSeries/Pochhammer.lean. DLMF 18.28.13
is the Laurent form `qGegenbauer` already defined in DLMF/QSeries/Identities.lean.
-/

/- §18.1(ii): the rescaled Chebyshev polynomials `C_n`, `S_n`. -/
dlmf_upstream 18.1.E3 Polynomial.Chebyshev.C_eq_two_mul_T_comp_half_mul_X
  "partial: first equality C_n(x) = 2T_n(x/2), over a ring with 2 invertible, n ∈ ℤ"
dlmf_upstream 18.1.E3 Polynomial.Chebyshev.S_eq_U_comp_half_mul_X
  "partial: second equality S_n(x) = U_n(x/2), over a ring with 2 invertible, n ∈ ℤ"
dlmf_upstream 18.1.E3 Polynomial.Chebyshev.C_comp_two_mul_X
  "partial: first equality in the form C_n(2x) = 2T_n(x), over any commutative ring, n ∈ ℤ"
dlmf_upstream 18.1.E3 Polynomial.Chebyshev.S_comp_two_mul_X
  "partial: second equality in the form S_n(2x) = U_n(x), over any commutative ring, n ∈ ℤ"

/- Table 18.3.1: leading coefficients and the Chebyshev-T orthogonality data. -/
dlmf_upstream 18.3.T1 Polynomial.Chebyshev.leadingCoeff_T
  "partial: k_n of T_n (2^{n-1} for n > 0, 1 for n = 0), over a domain with 2 ≠ 0"
dlmf_upstream 18.3.T1 Polynomial.Chebyshev.leadingCoeff_U_natCast
  "partial: k_n = 2^n of U_n, over a domain with 2 ≠ 0"
dlmf_upstream 18.3.T1 Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne
  "partial: orthogonality of T_n on (-1,1) with weight (1-x²)^{-1/2} (measureT)"
dlmf_upstream 18.3.T1 Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
  "partial: h_0 = π for T_n"
dlmf_upstream 18.3.T1 Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero
  "partial: h_n = π/2 for T_n, n > 0"
dlmf_upstream 18.3.T1 Polynomial.leadingCoeff_hermite
  "partial: k_n = 1 of He_n (Mathlib's hermite, over ℤ)"
dlmf_upstream 18.3.T1 Polynomial.hermite_monic
  "partial: k_n = 1 of He_n, as monicity"
dlmf_upstream 18.3.T1 Polynomial.degree_hermite
  "partial: He_n has degree n (implicit in the k_n column)"

/- Explicit representations and the first polynomials (§18.5). -/
dlmf_upstream 18.5.E7 Polynomial.coeff_shiftedLegendre
  "special case: α = β = 0 of the first sum, in the variable t = (1-x)/2; Mathlib's \
  shiftedLegendre n is P_n(1-2t), with coefficient (-1)^k C(n,k) C(n+k,n)"
dlmf_upstream 18.5.E14 Polynomial.Chebyshev.T_zero "partial: T_0(x) = 1"
dlmf_upstream 18.5.E14 Polynomial.Chebyshev.T_one "partial: T_1(x) = x"
dlmf_upstream 18.5.E14 Polynomial.Chebyshev.T_two "partial: T_2(x) = 2x² - 1"
dlmf_upstream 18.5.E15 Polynomial.Chebyshev.U_zero "partial: U_0(x) = 1"
dlmf_upstream 18.5.E15 Polynomial.Chebyshev.U_one "partial: U_1(x) = 2x"
dlmf_upstream 18.5.E15 Polynomial.Chebyshev.U_two "partial: U_2(x) = 4x² - 1"
dlmf_upstream 18.5.E19 Polynomial.hermite_zero "partial: He_0(x) = 1"
dlmf_upstream 18.5.E19 Polynomial.hermite_one "partial: He_1(x) = x"
dlmf_upstream 18.5.E19 Polynomial.coeff_hermite
  "stronger: the general coefficient formula of He_n, from which the listed He_0, …, He_6 follow"

/- Table 18.5.1: Rodrigues formula for `He_n` (w = e^{-x²/2}, F = 1, κ_n = (-1)^n). -/
dlmf_upstream 18.5.T1 Polynomial.hermite_eq_deriv_gaussian
  "partial: He_n row, He_n(x) = (-1)^n e^{x²/2} dⁿ/dxⁿ e^{-x²/2}, real x"
dlmf_upstream 18.5.T1 Polynomial.deriv_gaussian_eq_hermite_mul_gaussian
  "partial: He_n row, in the form dⁿ/dxⁿ e^{-x²/2} = (-1)^n He_n(x) e^{-x²/2}"

/- Table 18.6.1: symmetry and special values. -/
dlmf_upstream 18.6.T1 Polynomial.Chebyshev.T_eval_one "partial: T_n(1) = 1, n ∈ ℤ"
dlmf_upstream 18.6.T1 Polynomial.Chebyshev.T_eval_neg_one
  "partial: T_n(-1) = (-1)^n, combining the p_n(-x) and p_n(1) entries of the T_n row"
dlmf_upstream 18.6.T1 Polynomial.Chebyshev.T_eval_neg "partial: T_n(-x) = (-1)^n T_n(x), n ∈ ℤ"
dlmf_upstream 18.6.T1 Polynomial.Chebyshev.U_eval_one "partial: U_n(1) = n + 1, n ∈ ℤ"
dlmf_upstream 18.6.T1 Polynomial.Chebyshev.U_eval_neg_one
  "partial: U_n(-1) = (-1)^n (n+1), combining the p_n(-x) and p_n(1) entries of the U_n row"
dlmf_upstream 18.6.T1 Polynomial.Chebyshev.U_eval_neg "partial: U_n(-x) = (-1)^n U_n(x), n ∈ ℕ"
dlmf_upstream 18.6.T1 Polynomial.coeff_hermite_of_odd_add
  "partial: He_n(-x) = (-1)^n He_n(x), in the equivalent coefficient form (coefficients of \
  parity opposite to n vanish)"
dlmf_upstream 18.6.T1 Polynomial.shiftedLegendre_eval_symm
  "different convention: P_n(-x) = (-1)^n P_n(x) in the shifted variable, \
  P̃_n(x) = (-1)^n P̃_n(1-x) with P̃_n(x) = P_n(1-2x)"

/- Table 18.8.1: differential equations. -/
dlmf_upstream 18.8.T1 Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
  "partial: T_n row, (1-x²)T_n'' = xT_n' - n²T_n as a polynomial identity, n ∈ ℤ"
dlmf_upstream 18.8.T1 Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
  "partial: U_n row, (1-x²)U_n'' = 3xU_n' - n(n+2)U_n as a polynomial identity, n ∈ ℤ"

/- Table 18.9.1 and §18.9(ii): recurrences and contiguous relations. -/
dlmf_upstream 18.9.T1 Polynomial.Chebyshev.T_add_two
  "partial: T_n row, T_{n+2} = 2xT_{n+1} - T_n, n ∈ ℤ"
dlmf_upstream 18.9.T1 Polynomial.Chebyshev.U_add_two
  "partial: U_n row, U_{n+2} = 2xU_{n+1} - U_n, n ∈ ℤ"
dlmf_upstream 18.9.E10 Polynomial.Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T
  "exact: in the equivalent form (1-x²)U_n = xT_{n+1} - T_{n+2}, which with T_add_two is \
  -(T_{n+2} - T_n)/2; n ∈ ℤ"
dlmf_upstream 18.9.E9 Polynomial.Chebyshev.U_eq_two_mul_T_add_U
  "exact: in the equivalent form U_{n+2} = 2T_{n+2} + U_n; n ∈ ℤ"
dlmf_upstream 18.9.E22 Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U
  "equivalent form: (n+1)T_{n+1} = xU_n - (1-x²)U_n' as a polynomial identity, which is \
  18.9.22 multiplied by (1-x²)^{1/2}; n ∈ ℤ"

/- §18.14(i): the bound `|T_n(x)| ≤ 1` is (18.14.1) for α = β = -1/2, since
`T_n = P_n^{(-1/2,-1/2)} / P_n^{(-1/2,-1/2)}(1)`. -/
dlmf_upstream 18.14.E1 Polynomial.Chebyshev.abs_eval_T_real_le_one
  "special case: α = β = -1/2, normalized as |T_n(x)| ≤ T_n(1) = 1 on [-1,1], n ∈ ℤ"

/- §18.16(iii): the zeros of the Chebyshev polynomials can be read from (18.5.1)–(18.5.4). -/
dlmf_upstream 18.16.iii Polynomial.Chebyshev.roots_T_real
  "partial: zeros cos((2k+1)π/(2n)), k < n, of T_n, as the root multiset"
dlmf_upstream 18.16.iii Polynomial.Chebyshev.roots_U_real
  "partial: zeros cos((k+1)π/(n+1)), k < n, of U_n, as the root multiset"
dlmf_upstream 18.16.iii Polynomial.Chebyshev.rootMultiplicity_T_real
  "partial: the zeros of T_n are simple"
dlmf_upstream 18.16.iii Polynomial.Chebyshev.rootMultiplicity_U_real
  "partial: the zeros of U_n are simple"
