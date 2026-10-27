/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# DLMF §1.11 results already in Mathlib

Checked pointers from DLMF §1.11 (zeros of polynomials) to Mathlib declarations, instead of
duplicate local theorems. Mathlib's polynomials are `R[X]`; `f.coeff k` is DLMF's `a_k`,
`f.roots` the multiset of zeros (with multiplicity), and `Polynomial.discr` the discriminant,
defined through the Sylvester matrix of `f` and `f'` with a sign so that it agrees with
DLMF 1.11.9 (stated as a local theorem, `DLMF.AlgebraicAnalytic.discr_eq_prod_roots`).
-/

/- §1.11(i): division algorithm. -/
dlmf_upstream 1.11.E1 Polynomial.as_sum_range
  "exact: f = ∑_{k ≤ n} a_k z^k"
dlmf_upstream 1.11.E2 Polynomial.modByMonic_add_div
  "exact: f = (f mod (z - α)) + (z - α) q, with q = f /ₘ (z - α); see eval_eq_horner"
dlmf_upstream 1.11.E4 Polynomial.modByMonic_X_sub_C_eq_C_eval
  "exact: the remainder of f on division by z - α is f(α) (remainder theorem)"
dlmf_upstream 1.11.E7 EuclideanDomain.div_add_mod
  "exact: f = g q + r for polynomials over a field (q = f / g, r = f % g)"
dlmf_upstream 1.11.E7 Polynomial.degree_mod_lt
  "exact: deg r < deg g for g ≠ 0"

/- §1.11(ii): elementary properties. -/
dlmf_upstream 1.11.ii IsAlgClosed.card_roots_eq_natDegree
  "exact: a complex polynomial of degree n has n zeros counting multiplicity (ℂ is
  algebraically closed, Complex.isAlgClosed)"
dlmf_upstream 1.11.ii Polynomial.roots_countP_pos_le_signVariations
  "partial: Descartes' rule of signs, the inequality (positive zeros with multiplicity ≤ sign
  changes); the parity part is the local signVariations_sub_countP_pos_even"
dlmf_upstream 1.11.ii Polynomial.roots_comp_neg_X
  "exact: the zeros of f(-z) are the negatives of those of f"
dlmf_upstream 1.11.ii Polynomial.eval₂_reverse_eq_zero_iff
  "exact: the zeros of z^n f(1/z) (Polynomial.reverse) are the reciprocals of those of f"
dlmf_upstream 1.11.E9 Polynomial.discr
  "different convention: defined as a signed determinant of the Sylvester matrix of f, f';
  the product form 1.11.9 is the local discr_eq_prod_roots"
dlmf_upstream 1.11.E9 Polynomial.discr_of_degree_eq_two
  "special case: n = 2, D = b² - 4ac"
dlmf_upstream 1.11.E9 Cubic.discr_eq_prod_three_roots
  "special case: n = 3, D = (a₃² (z₁-z₂)(z₁-z₃)(z₂-z₃))²"
dlmf_upstream 1.11.E10 Polynomial.coeff_eq_esymm_roots_of_splits
  "exact: Vieta's formulas a_k = a_n (-1)^{n-k} e_{n-k}(z₁, …, z_n) for split f"
dlmf_upstream 1.11.E10 Polynomial.Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  "exact: z₁ + ⋯ + z_n = -a_{n-1}/a_n, in the form a_{n-1} = -a_n ∑ z_j"
dlmf_upstream 1.11.E10 Polynomial.Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots
  "exact: z₁ ⋯ z_n = (-1)^n a₀/a_n, in the form a₀ = (-1)^n a_n ∏ z_j"

/- §1.11(iii): quadratic equations. -/
dlmf_upstream 1.11.E11 quadratic_eq_zero_iff
  "exact: the roots of az² + bz + c are (-b ± s)/(2a) for any s with s² = b² - 4ac"
dlmf_upstream 1.11.E11 discrim
  "exact: D = b² - 4ac"

/- §1.11(iv): roots of unity. -/
dlmf_upstream 1.11.E21 geom_sum_mul
  "exact: (∑_{i<n} z^i)(z - 1) = z^n - 1"
dlmf_upstream 1.11.E21 Complex.mem_rootsOfUnity
  "exact: the n-th roots of unity are exp(2πik/n), k = 0, …, n-1"
