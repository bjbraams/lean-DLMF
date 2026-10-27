/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Vandermonde
public import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# DLMF §§1.2–1.3 results already upstream

The `dlmf_upstream` commands below are checked pointers to Mathlib (and one TauCeti) declarations
for DLMF §§1.2–1.3 (elementary algebra, matrices, determinants, linear operators), deliberately
not duplicate local theorems. Conventions:

* the binomial coefficient of 1.2.1 is `Nat.choose`, the one of 1.2.6 for complex `z` is
  `Ring.choose`;
* matrices are `Matrix m n R`; DLMF's `Aᴴ` is `Matrix.conjTranspose`, `\overline{A}` is
  `A.map star`, `etr(A)` is `exp (trace A)`;
* DLMF's scalar product `⟨u, v⟩` (linear in `u`) is Mathlib's `⟪v, u⟫` (linear in the second
  argument), see `DLMF/AlgebraicAnalytic/Algebra/Matrices.lean`;
* the matrix norm 1.2.67 is the `l²` operator norm, a scoped instance
  (`open scoped Matrix.Norms.L2Operator`);
* Mathlib's `Matrix.adjugate` is the transposed cofactor matrix: `adjugate A k j = A_{jk}`.
-/

/- §1.2(i): binomial coefficients. -/
dlmf_upstream 1.2.E1 Nat.cast_choose
  "exact: (C(n,k) : K) = n!/(k!(n-k)!) in a division ring of characteristic zero, for k ≤ n"
dlmf_upstream 1.2.E1 Nat.choose_eq_factorial_div_factorial
  "exact: C(n,k) = n!/(k!(n-k)!) with exact natural division, for k ≤ n"
dlmf_upstream 1.2.E1 Nat.choose_symm
  "exact: C(n,n-k) = C(n,k) for k ≤ n"
dlmf_upstream 1.2.E2 add_pow
  "stronger: (x+y)^n = ∑ x^m y^(n-m) C(n,m) in a commutative semiring, also for n = 0"
dlmf_upstream 1.2.E2 Commute.add_pow
  "stronger: the binomial theorem for commuting elements of a semiring"
dlmf_upstream 1.2.E3 Nat.sum_range_choose
  "exact: ∑_{k ≤ n} C(n,k) = 2^n"
dlmf_upstream 1.2.E4 Int.alternating_sum_range_choose_of_ne
  "exact: ∑_{k ≤ n} (-1)^k C(n,k) = 0 for n ≠ 0"
dlmf_upstream 1.2.E6 Ring.descPochhammer_eq_factorial_smul_choose
  "exact: k! C(z,k) = z(z-1)⋯(z-k+1) in a binomial ring"
dlmf_upstream 1.2.E6 Ring.choose_neg
  "exact: C(-r,k) = (-1)^k C(r+k-1,k), the last form of 1.2.6 with r = -z"
dlmf_upstream 1.2.E7 Ring.choose_succ_succ
  "exact: C(z+1,k+1) = C(z,k) + C(z,k+1) (1.2.7 for k ≥ 1; k = 0 is C(z,-1) = 0)"
dlmf_upstream 1.2.E7 Nat.choose_succ_succ
  "exact: Pascal's rule for natural numbers"

/- §1.2(ii): finite series. -/
dlmf_upstream 1.2.E10 Finset.sum_range_id_mul_two
  "special case: a = 0, d = 1, (∑_{i<n} i)·2 = n(n-1) in ℕ"
dlmf_upstream 1.2.E11 geom_sum_eq
  "special case: a = 1, ∑_{i<n} x^i = (x^n - 1)/(x - 1) for x ≠ 1 in a division ring"

/- §1.2(iii): partial fractions. -/
dlmf_upstream 1.2.E12 Lagrange.eval_interpolate_not_at_node
  "partial: the barycentric form of Lagrange interpolation, from which 1.2.12 follows"
dlmf_upstream 1.2.E16 Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod
  "stronger: f = q ∏ g_i + ∑ r_i ∏_{k≠i} g_k with deg r_i < deg g_i, for monic pairwise coprime
  g_i over a commutative ring"
dlmf_upstream 1.2.E16 Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow
  "stronger: the complete decomposition into powers g_i^j"

/- §1.2(iv): means. -/
dlmf_upstream 1.2.iv Real.geom_mean_le_arith_mean_weighted
  "partial: the weighted AM-GM inequality (DLMF 1.7.E7)"

/- §1.2(v): matrices, vectors, scalar products and norms. -/
dlmf_upstream 1.2.E27 Matrix
  "exact: Matrix m n α is the type of m × n matrices, A i j the entry a_{ij}"
dlmf_upstream 1.2.E28 Matrix.transpose_apply
  "exact: Aᵀ i j = A j i"
dlmf_upstream 1.2.E29 Matrix.map_apply
  "exact: the complex conjugate matrix is A.map star, (A.map star) i j = star (A i j)"
dlmf_upstream 1.2.E30 Matrix.conjTranspose_apply
  "exact: Aᴴ i j = star (A j i)"
dlmf_upstream 1.2.E31 Matrix.smul_apply
  "exact: (α • A) i j = α • A i j"
dlmf_upstream 1.2.E31 op_smul_eq_smul
  "exact: A α = α A, the right action MulOpposite.op α • A equals α • A"
dlmf_upstream 1.2.E32 Matrix.add_apply
  "exact: (A + B) i j = A i j + B i j"
dlmf_upstream 1.2.E32 add_comm
  "exact: A + B = B + A"
dlmf_upstream 1.2.E33 add_assoc
  "exact: (A + B) + C = A + (B + C)"
dlmf_upstream 1.2.E34 Matrix.mul_apply
  "exact: (A * B) i k = ∑ j, A i j * B j k"
dlmf_upstream 1.2.E35 Matrix.mul_assoc
  "exact: A (B C) = (A B) C for rectangular matrices"
dlmf_upstream 1.2.E36 Matrix.mul_add
  "exact: A (B + C) = A B + A C"
dlmf_upstream 1.2.E37 Matrix.transpose_mul
  "exact: (A B)ᵀ = Bᵀ Aᵀ"
dlmf_upstream 1.2.E38 Matrix.replicateCol
  "exact: a column vector n → α as an n × 1 matrix"
dlmf_upstream 1.2.E39 Matrix.replicateRow
  "exact: a row vector n → α as a 1 × n matrix"
dlmf_upstream 1.2.E39 Matrix.transpose_replicateCol
  "exact: the transpose of a column vector is the row vector"
dlmf_upstream 1.2.E40 EuclideanSpace.inner_eq_star_dotProduct
  "different convention: ⟪x, y⟫ = y ⬝ᵥ star x, so DLMF's ⟨u, v⟩ is ⟪v, u⟫"
dlmf_upstream 1.2.E41 inner_conj_symm
  "exact: conj ⟪y, x⟫ = ⟪x, y⟫ in any inner product space"
dlmf_upstream 1.2.E42 inner_smul_left
  "different convention: ⟪r • x, y⟫ = conj r * ⟪x, y⟫ (Mathlib is conjugate-linear on the left)"
dlmf_upstream 1.2.E42 inner_smul_right
  "different convention: ⟪x, r • y⟫ = r * ⟪x, y⟫"
dlmf_upstream 1.2.E43 dotProduct_self_star_eq_zero
  "exact: v ⬝ᵥ star v = 0 ↔ v = 0 (DLMF's ⟨v, v⟩ = 0 iff v = 0)"
dlmf_upstream 1.2.E43 inner_self_eq_zero
  "exact: ⟪x, x⟫ = 0 ↔ x = 0 in any inner product space"
dlmf_upstream 1.2.E44 inner_eq_zero_symm
  "exact: orthogonality ⟪u, v⟫ = 0 is symmetric; Mathlib has no separate predicate for vectors"
dlmf_upstream 1.2.E45 PiLp.norm_eq_sum
  "stronger: ‖f‖ = (∑ ‖f i‖^p)^(1/p) on PiLp p for 0 < p < ∞ (DLMF: p ≥ 1)"
dlmf_upstream 1.2.E46 EuclideanSpace.norm_eq
  "exact: ‖x‖ = √(∑ ‖x i‖²) on EuclideanSpace"
dlmf_upstream 1.2.E46 norm_eq_sqrt_re_inner
  "exact: ‖x‖ = √(re ⟪x, x⟫)"
dlmf_upstream 1.2.E47 PiLp.norm_eq_of_L1
  "exact: ‖x‖ = ∑ ‖x i‖ on PiLp 1"
dlmf_upstream 1.2.E48 PiLp.norm_eq_ciSup
  "exact: ‖f‖ = ⨆ i, ‖f i‖ on PiLp ∞"
dlmf_upstream 1.2.E49 Real.HolderConjugate
  "exact: p.HolderConjugate q means 1 < p, 1 < q, 1/p + 1/q = 1 (DLMF 1.2.49)"
dlmf_upstream 1.2.E50 Real.inner_le_Lp_mul_Lq
  "special case: Hölder's inequality for real finite sums"
dlmf_upstream 1.2.E51 norm_inner_le_norm
  "exact: the Cauchy-Schwarz inequality ‖⟪x, y⟫‖ ≤ ‖x‖ ‖y‖"
dlmf_upstream 1.2.E51 norm_inner_eq_norm_iff
  "partial: the equality case for nonzero x, y"
dlmf_upstream 1.2.E52 norm_add_le
  "exact: the triangle inequality"
dlmf_upstream 1.2.v norm_smul_inv_norm
  "exact: ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 for x ≠ 0 (normalization v → v/‖v‖)"

/- §1.2(vi): square matrices. -/
dlmf_upstream 1.2.E53 Matrix.one_apply
  "exact: (1 : Matrix n n α) i j = if i = j then 1 else 0"
dlmf_upstream 1.2.E54 Matrix.IsDiag
  "exact: a matrix is diagonal if its off-diagonal entries vanish"
dlmf_upstream 1.2.E55 Matrix.IsSymm
  "exact: Aᵀ = A; real symmetric is IsSymm for Matrix n n ℝ"
dlmf_upstream 1.2.E56 Matrix.IsHermitian
  "exact: Aᴴ = A"
dlmf_upstream 1.2.vi Matrix.IsUpperTriangular
  "exact: a_{ij} = 0 for i > j"
dlmf_upstream 1.2.vi Matrix.IsLowerTriangular
  "exact: a_{ij} = 0 for i < j"
dlmf_upstream 1.2.E58 Matrix.det
  "exact: the determinant of a square matrix"
dlmf_upstream 1.2.E59 Matrix.det_apply
  "exact: the Leibniz formula, with factors a_{σ(i),i}"
dlmf_upstream 1.2.E60 Matrix.mul_nonsing_inv
  "exact: A A⁻¹ = 1 when det A is a unit"
dlmf_upstream 1.2.E60 Matrix.nonsing_inv_mul
  "exact: A⁻¹ A = 1 when det A is a unit"
dlmf_upstream 1.2.E60 Matrix.inv_eq_left_inv
  "exact: uniqueness of the inverse"
dlmf_upstream 1.2.E61 Matrix.exists_mulVec_eq_zero_iff
  "partial: A b = 0 has a nonzero solution iff det A = 0"
dlmf_upstream 1.2.E62 Matrix.trace
  "exact: tr A = ∑ i, A i i"
dlmf_upstream 1.2.E63 Matrix.trace_smul
  "exact: tr(α A) = α tr A"
dlmf_upstream 1.2.E64 Matrix.trace_add
  "exact: tr(A + B) = tr A + tr B"
dlmf_upstream 1.2.E65 Matrix.trace_mul_comm
  "stronger: tr(A B) = tr(B A) for rectangular A, B"
dlmf_upstream 1.2.E66 Ring.lie_def
  "exact: the commutator ⁅A, B⁆ = A B - B A"
dlmf_upstream 1.2.E66 lie_skew
  "exact: -⁅B, A⁆ = ⁅A, B⁆"
dlmf_upstream 1.2.E67 Matrix.l2_opNorm_def
  "exact: the l² operator norm ‖A‖ = ‖toEuclideanLin A‖ (scoped Matrix.Norms.L2Operator)"
dlmf_upstream 1.2.E67 Matrix.l2_opNorm_mulVec
  "partial: ‖A x‖ ≤ ‖A‖ ‖x‖"
dlmf_upstream 1.2.E68 Matrix.l2_opNorm_mul
  "exact: ‖A B‖ ≤ ‖A‖ ‖B‖ for the l² operator norm"
dlmf_upstream 1.2.E69 Matrix.instL2OpNormedAddCommGroup
  "exact: the l² operator norm is a norm, so ‖A + B‖ ≤ ‖A‖ + ‖B‖ (norm_add_le)"
dlmf_upstream 1.2.E70 Module.End.HasEigenvector
  "exact: an eigenvector of the linear map Matrix.toLin' A"
dlmf_upstream 1.2.E71 Module.End.hasEigenvalue_iff_isRoot_charpoly
  "different convention: eigenvalues are the roots of charpoly A = det(X I - A)"
dlmf_upstream 1.2.E73 Matrix.linearIndependent_col_iff_isUnit
  "partial: the columns of S are linearly independent iff S is invertible"
dlmf_upstream 1.2.E74 Matrix.det_eq_prod_roots_charpoly
  "stronger: det A = ∏ of the eigenvalues for every matrix over an algebraically closed field"
dlmf_upstream 1.2.E74 Matrix.det_conj'
  "exact: det(S⁻¹ A S) = det A"
dlmf_upstream 1.2.E75 Matrix.trace_eq_sum_roots_charpoly
  "stronger: tr A = ∑ of the eigenvalues for every matrix over an algebraically closed field"
dlmf_upstream 1.2.E75 Matrix.trace_conj'
  "exact: tr(S⁻¹ A S) = tr A"
dlmf_upstream 1.2.E76 NormedSpace.exp_eq_tsum
  "exact: exp A = ∑' n, (n!)⁻¹ • A^n"
dlmf_upstream 1.2.E76 NormedSpace.exp_series_hasSum_exp'
  "exact: the exponential series converges in a complete normed algebra"
dlmf_upstream 1.2.E77 Matrix.det_exp
  "stronger: det(exp A) = exp(tr A) for every square matrix over ℝ or ℂ (TauCeti)"

/- §1.3(i): determinants, elementary properties. -/
dlmf_upstream 1.3.E1 Matrix.det_fin_two
  "exact: the 2 × 2 determinant"
dlmf_upstream 1.3.E2 Matrix.det_fin_three
  "exact: the 3 × 3 determinant"
dlmf_upstream 1.3.E2 Matrix.det_succ_row_zero
  "exact: expansion by the first row"
dlmf_upstream 1.3.E3 Matrix.adjugate_fin_succ_eq_det_submatrix
  "different convention: adjugate A i j = (-1)^(j+i) det(A without row j, column i) = A_{ji}"
dlmf_upstream 1.3.E4 Matrix.det_succ_row
  "exact: expansion by the jth row"
dlmf_upstream 1.3.E4 Matrix.det_succ_column
  "exact: expansion by a column"
dlmf_upstream 1.3.i Matrix.det_permute
  "exact: permuting the rows multiplies det by the sign (an interchange changes the sign)"
dlmf_upstream 1.3.i Matrix.det_permute'
  "exact: permuting the columns multiplies det by the sign"
dlmf_upstream 1.3.i Matrix.det_zero_of_row_eq
  "exact: two equal rows give det = 0"
dlmf_upstream 1.3.i Matrix.det_zero_of_column_eq
  "exact: two equal columns give det = 0"
dlmf_upstream 1.3.i Matrix.det_updateRow_smul
  "exact: multiplying a row by μ multiplies det by μ"
dlmf_upstream 1.3.i Matrix.det_updateCol_smul
  "exact: multiplying a column by μ multiplies det by μ"
dlmf_upstream 1.3.i Matrix.det_updateRow_add_smul_self
  "exact: adding μ times a row to another row leaves det unchanged"
dlmf_upstream 1.3.i Matrix.det_updateCol_add_smul_self
  "exact: adding μ times a column to another column leaves det unchanged"
dlmf_upstream 1.3.i Matrix.det_of_isUpperTriangular
  "exact: det of an upper triangular matrix is the product of the diagonal"
dlmf_upstream 1.3.i Matrix.det_of_isLowerTriangular
  "exact: det of a lower triangular matrix is the product of the diagonal"
dlmf_upstream 1.3.i Matrix.det_diagonal
  "exact: det of a diagonal matrix is the product of the diagonal"
dlmf_upstream 1.3.E5 Matrix.det_transpose
  "exact: det Aᵀ = det A"
dlmf_upstream 1.3.E6 Matrix.det_nonsing_inv
  "exact: det A⁻¹ = Ring.inverse (det A)"
dlmf_upstream 1.3.E7 Matrix.det_mul
  "exact: det(A B) = det A det B"

/- §1.3(ii): special determinants. -/
dlmf_upstream 1.3.E11 Matrix.det_permute
  "exact: an alternant changes sign under an interchange of two variables (rows)"
dlmf_upstream 1.3.E13 Matrix.det_vandermonde
  "exact: det[x_j^k] = ∏_{j<k} (x_k - x_j)"

/- §1.3(iv): matrices as linear operators. -/
dlmf_upstream 1.3.iv Matrix.mulVecLin
  "exact: A as a linear map; A(αa + βb) = αAa + βAb (Matrix.mulVec_add, Matrix.mulVec_smul)"
dlmf_upstream 1.3.iv Matrix.toEuclideanLin_conjTranspose_eq_adjoint
  "exact: the adjoint of A on EuclideanSpace is Aᴴ"
dlmf_upstream 1.3.iv Matrix.isSymmetric_toEuclideanLin_iff
  "exact: A is self-adjoint on EuclideanSpace iff A is Hermitian"
dlmf_upstream 1.3.iv LinearMap.IsSymmetric.conj_eigenvalue_eq_self
  "exact: eigenvalues of a self-adjoint operator are real"
dlmf_upstream 1.3.iv Matrix.IsHermitian.eigenvalues
  "exact: the (real) eigenvalues of a Hermitian matrix"
dlmf_upstream 1.3.iv Matrix.IsHermitian.eigenvectorBasis
  "exact: an orthonormal basis of eigenvectors of a Hermitian matrix"
dlmf_upstream 1.3.iv Matrix.IsHermitian.mulVec_eigenvectorBasis
  "exact: A a_j = λ_j a_j for the eigenvector basis"
dlmf_upstream 1.3.iv Matrix.IsHermitian.eigenvectorUnitary
  "exact: the unitary matrix S of eigenvectors, S⁻¹ = Sᴴ"
dlmf_upstream 1.3.iv Matrix.IsHermitian.spectral_theorem
  "exact: A = S diag(λ) Sᴴ, equivalently Sᴴ A S = diag(λ)"
dlmf_upstream 1.3.iv LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
  "stronger: commuting self-adjoint operators have a joint eigenspace decomposition"
dlmf_upstream 1.3.E20 OrthonormalBasis.sum_repr'
  "exact: u = ∑ ⟪a_i, u⟫ a_i, DLMF's c_i = ⟨u, a_i⟩ = ⟪a_i, u⟫"
dlmf_upstream 1.3.E21 OrthonormalBasis.sum_sq_norm_inner_right
  "exact: Parseval's equality ∑ ‖⟪a_i, u⟫‖² = ‖u‖²"
