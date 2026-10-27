/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Algebra.Defs
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Determinants (DLMF §1.3(i)–(iii))

The elementary properties of determinants (1.3.1–1.3.7, the row and column rules of §1.3(i),
triangular matrices) and the Vandermonde determinant 1.3.13 are in Mathlib; the pointers are in
`DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean`. This file has the DLMF forms of 1.3.6, the
alternant property 1.3.11–1.3.12, Hadamard's inequality 1.3.8–1.3.10, the Cauchy determinant
1.3.14, the circulant 1.3.15, Krattenthaler's formula 1.3.16–1.3.17 and the convergence of
infinite determinants of Hill's type (1.3.19); the truncations `D_n` (1.3.18) are defined in
`DLMF/AlgebraicAnalytic/Algebra/Defs.lean`.

DLMF's circulant (1.3.15) has rows `(a₁, …, aₙ)`, `(aₙ, a₁, …, a_{n-1})`, …, that is the entry
`a_{k-j}` (indices mod `n`) in row `j`, column `k`; it is the transpose of Mathlib's
`Matrix.circulant a` (entry `a (j - k)`). Indices run over `Fin n` from `0`, so DLMF's `a₁` is
`a 0`, and the `n`th roots of unity are `ω_k = e^{2πik/n}`, `k = 0, …, n-1`.

The formulas 1.3.14, 1.3.15 and 1.3.17 were checked numerically (mpmath, `n ≤ 6`, random
real data) before acquisition.
-/

@[expose] public noncomputable section

open Finset Matrix Filter Topology InnerProductSpace Module Polynomial

namespace DLMF.AlgebraicAnalytic

/-! ### Elementary properties (§1.3(i)) -/

/-- DLMF 1.3.6: `det(A⁻¹) = 1/det(A)`. Over a field this holds for every square matrix, with
Lean's conventions `A⁻¹ = 0` and `1/0 = 0` for singular `A` (stronger than DLMF). -/
@[dlmf 1.3.E6]
theorem det_inv_eq_one_div {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (A : Matrix n n K) : A⁻¹.det = 1 / A.det := by
  rw [det_nonsing_inv, Ring.inverse_eq_inv', one_div]

/-! ### Hadamard's inequality (§1.3(i)) -/

/-- DLMF 1.3.8: Hadamard's inequality for real `2 × 2` determinants,
`det² ≤ (a₁₁² + a₁₂²)(a₂₁² + a₂₂²)`. -/
@[dlmf 1.3.E8]
theorem det_fin_two_sq_le (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det ^ 2 ≤ (A 0 0 ^ 2 + A 0 1 ^ 2) * (A 1 0 ^ 2 + A 1 1 ^ 2) := by
  rw [det_fin_two]
  nlinarith [sq_nonneg (A 0 0 * A 1 0 + A 0 1 * A 1 1)]

/-- Helper: `‖v‖² = ∑ v_k²` for the vector of a matrix row. -/
lemma g1a_norm_sq_eq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ ^ 2 = ∑ k, v k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- Helper: the real inner product of two vectors of `EuclideanSpace`. -/
lemma g1a_inner_eq {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v w = ∑ l, v l * w l := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- Helper: Gram–Schmidt form of the determinant of the matrix with rows `v_j`:
`|det| = ∏ |⟪b_j, v_j⟫|` for the Gram–Schmidt orthonormal basis `b` of the `v_j`. -/
lemma g1a_abs_det_eq {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      |(Matrix.of fun j k => v j k).det| = ∏ j, |inner ℝ (b j) (v j)| := by
  set std := EuclideanSpace.basisFun (Fin n) ℝ
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  set b := gramSchmidtOrthonormalBasis hcard v
  have h1 : std.toBasis.det v = (Matrix.of fun j k => v j k).det := by
    rw [Basis.det_apply, ← det_transpose]
    congr 1
  have h2 : std.toBasis.det v = std.toBasis.det b * b.toBasis.det v := by
    have := AlternatingMap.eq_smul_basis_det b.toBasis std.toBasis.det
    conv_lhs => rw [this]
    simp
  have h3 : |std.toBasis.det b| = 1 := by
    rcases std.det_to_matrix_orthonormalBasis_real b with h | h <;> simp [h]
  refine ⟨b, ?_⟩
  rw [← h1, h2, abs_mul, h3, one_mul, gramSchmidtOrthonormalBasis_det, abs_prod]

/-- Helper: `|⟪b, v⟫| ≤ ‖v‖` for a unit vector `b`. -/
lemma g1a_abs_inner_le {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (j : Fin n) (v : EuclideanSpace ℝ (Fin n)) : |inner ℝ (b j) v| ≤ ‖v‖ := by
  calc |inner ℝ (b j) v| ≤ ‖b j‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by rw [b.orthonormal.1 j, one_mul]

/-- Helper: termwise equality from equality of products of nonnegative factors bounded by
positive ones. -/
lemma g1a_eq_of_prod_eq {ι : Type*} [Fintype ι] {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hxy : ∀ i, x i ≤ y i) (hy : ∀ i, 0 < y i) (h : ∏ i, x i = ∏ i, y i) (i : ι) :
    x i = y i := by
  by_contra hne
  have hlt : x i < y i := lt_of_le_of_ne (hxy i) hne
  by_cases hpos : ∀ j, 0 < x j
  · exact absurd h (ne_of_lt (prod_lt_prod₀ (fun j _ => hpos j) (fun j _ => hxy j)
      ⟨i, mem_univ i, hlt⟩))
  · push Not at hpos
    obtain ⟨j, hj⟩ := hpos
    have : x j = 0 := le_antisymm hj (hx j)
    rw [prod_eq_zero (mem_univ j) this] at h
    exact absurd h (ne_of_lt (prod_pos fun k _ => hy k))

/-- DLMF 1.3.9: Hadamard's inequality for a real determinant,
`det[a_{jk}]² ≤ ∏_j ∑_k a_{jk}²`. Proved by Gram–Schmidt orthonormalization of the rows
(`InnerProductSpace.gramSchmidtOrthonormalBasis_det`). -/
@[dlmf 1.3.E9]
theorem det_sq_le_prod_sum_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det ^ 2 ≤ ∏ j, ∑ k, A j k ^ 2 := by
  set v : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (A j)
  have hA : A = Matrix.of fun j k => v j k := rfl
  have hsq : ∀ j, ∑ k, A j k ^ 2 = ‖v j‖ ^ 2 := fun j => (g1a_norm_sq_eq (v j)).symm
  obtain ⟨b, hb⟩ := g1a_abs_det_eq v
  simp only [hsq, prod_pow]
  rw [← sq_abs, hA, hb]
  exact pow_le_pow_left₀ (prod_nonneg fun i _ => abs_nonneg _)
    (prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => g1a_abs_inner_le b i (v i)) 2

/-- DLMF 1.3.10: equality holds in Hadamard's inequality 1.3.9 iff the rows are pairwise
orthogonal, `a_{j1}a_{k1} + ⋯ + a_{jn}a_{kn} = 0` for `j ≠ k`, or one of the factors
`∑_k a_{jk}²` vanishes. -/
@[dlmf 1.3.E10]
theorem det_sq_eq_prod_sum_sq_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det ^ 2 = ∏ j, ∑ k, A j k ^ 2 ↔
      (∀ j k, j ≠ k → ∑ l, A j l * A k l = 0) ∨ ∃ j, ∑ k, A j k ^ 2 = 0 := by
  set v : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (A j)
  have hA : A = Matrix.of fun j k => v j k := rfl
  have hsq : ∀ j, ∑ k, A j k ^ 2 = ‖v j‖ ^ 2 := fun j => (g1a_norm_sq_eq (v j)).symm
  constructor
  · intro h
    by_cases h0 : ∃ j, ∑ k, A j k ^ 2 = 0
    · exact Or.inr h0
    left
    push Not at h0
    have hne : ∀ j, v j ≠ 0 := fun j hj => h0 j (by rw [hsq, hj, norm_zero]; ring)
    have hnpos : ∀ j, 0 < ‖v j‖ := fun j => norm_pos_iff.2 (hne j)
    obtain ⟨b, hb⟩ := g1a_abs_det_eq v
    have habs : |A.det| = ∏ j, ‖v j‖ := by
      have h' : |A.det| ^ 2 = (∏ j, ‖v j‖) ^ 2 := by
        rw [sq_abs, h, ← prod_pow]; simp only [hsq]
      exact (pow_left_inj₀ (abs_nonneg _) (prod_nonneg fun j _ => norm_nonneg _)
        two_ne_zero).1 h'
    rw [hA, hb] at habs
    have heq := g1a_eq_of_prod_eq (fun j => abs_nonneg _) (fun j => g1a_abs_inner_le b j (v j))
      hnpos habs
    have hpar : ∀ j, ∃ r : ℝ, v j = r • b j := fun j => by
      have hbj : b j ≠ 0 := fun h => by simpa [h] using b.orthonormal.1 j
      obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) hbj (hne j)).1 (by
        rw [Real.norm_eq_abs, heq j, b.orthonormal.1 j, one_mul])
      exact ⟨r, hr⟩
    intro j k hjk
    have hjk' : ∑ l, A j l * A k l = inner ℝ (v j) (v k) := (g1a_inner_eq (v j) (v k)).symm
    rw [hjk']
    obtain ⟨r, hr⟩ := hpar j
    obtain ⟨s, hs⟩ := hpar k
    rw [hr, hs, inner_smul_left, inner_smul_right, b.orthonormal.2 hjk]
    simp
  · rintro (h | ⟨j, hj⟩)
    · have hD : A * Aᵀ = diagonal fun j => ∑ k, A j k ^ 2 := by
        ext j k
        rw [Matrix.mul_apply]
        by_cases hjk : j = k
        · subst hjk; simp [sq]
        · rw [diagonal_apply_ne _ hjk]
          simpa using h j k hjk
      have := congrArg det hD
      rw [det_mul, det_transpose, det_diagonal] at this
      rw [sq, this]
    · have hrow : A j = 0 := by
        ext k
        have := (sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (A j k)).1 hj k (mem_univ k)
        simpa using this
      rw [det_eq_zero_of_row_eq_zero j (fun k => by simp [hrow]), prod_eq_zero (mem_univ j) hj]
      ring

/-! ### Special determinants (§1.3(ii)) -/

/-- DLMF 1.3.11: the alternant `det[f_k(x_j)]` changes sign when two of the variables `x_i`,
`x_{i'}` are interchanged. -/
@[dlmf 1.3.E11]
theorem det_alternant_swap {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] {X : Type*}
    (f : n → X → R) (x : n → X) {i i' : n} (h : i ≠ i') :
    (Matrix.of fun j k => f k (x (Equiv.swap i i' j))).det =
      -(Matrix.of fun j k => f k (x j)).det := by
  rw [show (Matrix.of fun j k => f k (x (Equiv.swap i i' j))) =
      (Matrix.of fun j k => f k (x j)).submatrix (Equiv.swap i i') id from rfl,
    det_permute, Equiv.Perm.sign_swap h]
  simp

/-- DLMF 1.3.12: the alternant `det[f(x_j, y_k)]` changes sign when two of the variables `x_i`,
`x_{i'}` are interchanged. -/
@[dlmf 1.3.E12]
theorem det_alternant₂_swap {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {X Y : Type*} (f : X → Y → R) (x : n → X) (y : n → Y) {i i' : n} (h : i ≠ i') :
    (Matrix.of fun j k => f (x (Equiv.swap i i' j)) (y k)).det =
      -(Matrix.of fun j k => f (x j) (y k)).det :=
  det_alternant_swap (fun k t => f t (y k)) x h

/-- Helper: `∏_j ∏_{l ≠ j} (b_j - b_l) = (-1)^{n(n-1)/2} (∏_{j<k} (b_k - b_j))²`. -/
lemma g1a_prod_erase_sub {n : ℕ} {K : Type*} [CommRing K] (b : Fin n → K) :
    ∏ j, ∏ l ∈ univ.erase j, (b j - b l) =
      (-1) ^ (n * (n - 1) / 2) * (∏ j, ∏ k ∈ Ioi j, (b k - b j)) ^ 2 := by
  have hsplit : ∀ j : Fin n, ∏ l ∈ univ.erase j, (b j - b l) =
      (∏ l ∈ Ioi j, (b j - b l)) * ∏ l ∈ Iio j, (b j - b l) := by
    intro j
    rw [← prod_filter_mul_prod_filter_not (univ.erase j) (fun l => j < l)]
    congr 1
    · congr 1; ext l; simp [lt_iff_le_and_ne, ne_comm, and_comm]
    · congr 1; ext l; simp [lt_iff_le_and_ne]; omega
  have hneg : ∀ j : Fin n, ∏ l ∈ Ioi j, (b j - b l) =
      (-1) ^ #(Ioi j) * ∏ l ∈ Ioi j, (b l - b j) := by
    intro j
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun l _ => by ring
  have hswap : ∏ j : Fin n, ∏ l ∈ Iio j, (b j - b l) = ∏ l : Fin n, ∏ j ∈ Ioi l, (b j - b l) :=
    prod_comm' fun j l => by simp
  have hcard : ∑ j : Fin n, #(Ioi j) = n * (n - 1) / 2 := by
    simp only [Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i), ← sum_range_id]
    rw [← sum_range_reflect]
    exact sum_congr rfl fun i hi => by have := mem_range.1 hi; omega
  simp only [hsplit, prod_mul_distrib, hneg, hswap]
  rw [prod_pow_eq_pow_sum, hcard]
  ring

/-- DLMF 1.3.14: the Cauchy determinant
`det[1/(a_j - b_k)] = (-1)^{n(n-1)/2} ∏_{j<k}(a_k - a_j)(b_k - b_j) / ∏_{j,k}(a_j - b_k)`,
for `a_j ≠ b_k` for all `j, k`. -/
@[dlmf 1.3.E14]
theorem det_cauchy {n : ℕ} {K : Type*} [Field K] (a b : Fin n → K)
    (hab : ∀ j k, a j ≠ b k) :
    (Matrix.of fun j k => 1 / (a j - b k)).det =
      (-1) ^ (n * (n - 1) / 2) *
        (∏ j, ∏ k ∈ Ioi j, (a k - a j) * (b k - b j)) / ∏ j, ∏ k, (a j - b k) := by
  by_cases hb : Function.Injective b
  swap
  · obtain ⟨j, k, hjk, hne⟩ : ∃ j k, b j = b k ∧ j ≠ k := by
      simpa [Function.Injective, not_forall] using hb
    rw [det_zero_of_column_eq hne (fun i => by simp [hjk])]
    have h0 : ∏ j, ∏ k ∈ Ioi j, (a k - a j) * (b k - b j) = 0 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact prod_eq_zero (mem_univ j) (prod_eq_zero (mem_Ioi.2 h) (by simp [hjk]))
      · exact prod_eq_zero (mem_univ k) (prod_eq_zero (mem_Ioi.2 h) (by simp [hjk]))
    rw [h0]; simp
  set q : Fin n → K[X] := fun k => ∏ l ∈ univ.erase k, (X - C (b l)) with hq
  have hqdeg : ∀ k, (q k).natDegree < n := by
    intro k
    rw [hq, natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C (b l)]
    simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one, card_erase_of_mem (mem_univ k),
      card_univ, Fintype.card_fin]
    have := k.isLt
    omega
  set T : Matrix (Fin n) (Fin n) K := Matrix.of fun i k => (q k).coeff i
  have hM : ∀ x : Fin n → K, (Matrix.of fun j k => (q k).eval (x j)) = vandermonde x * T := by
    intro x
    ext j k
    rw [Matrix.mul_apply, of_apply, eval_eq_sum_range' (hqdeg k),
      ← Fin.sum_univ_eq_sum_range (fun i => (q k).coeff i * x j ^ i)]
    simp [T, vandermonde_apply, mul_comm]
  have hC : (Matrix.of fun j k => 1 / (a j - b k)) =
      diagonal (fun j => (∏ k, (a j - b k))⁻¹) * Matrix.of fun j k => (q k).eval (a j) := by
    ext j k
    rw [diagonal_mul, of_apply, of_apply, hq, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [← mul_prod_erase univ (fun l => a j - b l) (mem_univ k)]
    have h1 : a j - b k ≠ 0 := sub_ne_zero.2 (hab j k)
    have h2 : ∏ l ∈ univ.erase k, (a j - b l) ≠ 0 :=
      prod_ne_zero_iff.2 fun l _ => sub_ne_zero.2 (hab j l)
    field_simp
  have hMb : (Matrix.of fun j k => (q k).eval (b j)) =
      diagonal (fun j => ∏ l ∈ univ.erase j, (b j - b l)) := by
    ext j k
    rw [of_apply, hq, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [diagonal_apply_ne _ hjk]
      exact prod_eq_zero (mem_erase.2 ⟨hjk, mem_univ j⟩) (sub_self _)
  have hVb : (vandermonde b).det ≠ 0 := det_vandermonde_ne_zero_iff.2 hb
  have hT : T.det = (-1) ^ (n * (n - 1) / 2) * (vandermonde b).det := by
    have h := congrArg det (hM b)
    rw [hMb, det_diagonal, det_mul, g1a_prod_erase_sub, det_vandermonde] at h
    rw [det_vandermonde] at hVb ⊢
    apply mul_left_cancel₀ hVb
    rw [← h]; ring
  have hPa : ∏ j, ∏ k, (a j - b k) ≠ 0 :=
    prod_ne_zero_iff.2 fun j _ => prod_ne_zero_iff.2 fun k _ => sub_ne_zero.2 (hab j k)
  rw [hC, det_mul, det_diagonal, hM a, det_mul, hT, det_vandermonde, det_vandermonde,
    prod_inv_distrib]
  simp only [prod_mul_distrib]
  field_simp

/-- DLMF 1.3.15: the circulant determinant
`det[a_{k-j}] = ∏_{k} (a₁ + a₂ω_k + ⋯ + aₙω_k^{n-1})`, the product over the `n`th roots of
unity `ω_k = e^{2πik/n}`. DLMF's circulant is the transpose of Mathlib's `Matrix.circulant`. -/
@[dlmf 1.3.E15]
theorem det_circulant {n : ℕ} [NeZero n] (a : Fin n → ℂ) :
    (Matrix.of fun j k : Fin n => a (k - j)).det =
      ∏ k : Fin n, ∑ l : Fin n,
        a l * Complex.exp (2 * Real.pi * Complex.I * k / n) ^ (l : ℕ) := by
  have hn : n ≠ 0 := NeZero.ne n
  set ω := Complex.exp (2 * Real.pi * Complex.I / n) with hω
  have hprim : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n hn
  have hζ : ∀ k : Fin n, Complex.exp (2 * Real.pi * Complex.I * k / n) = ω ^ (k : ℕ) := by
    intro k
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [hζ]
  set ζ : Fin n → ℂ := fun k => ω ^ (k : ℕ) with hζdef
  have hζn : ∀ k, ζ k ^ n = 1 := fun k => by
    rw [hζdef]; simp only; rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hinj : Function.Injective ζ := fun i j hij =>
    Fin.ext (hprim.pow_inj i.isLt j.isLt hij)
  set F : Matrix (Fin n) (Fin n) ℂ := (vandermonde ζ)ᵀ with hF
  set C : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j k : Fin n => a (k - j)
  set μ : Fin n → ℂ := fun k => ∑ l : Fin n, a l * ζ k ^ (l : ℕ)
  have hCF : C * F = F * diagonal μ := by
    ext j k
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [C, F, μ, of_apply, transpose_apply, vandermonde_apply]
    rw [mul_sum]
    refine (Fintype.sum_equiv (Equiv.addLeft j) _ _ fun l => ?_).symm
    simp only [Equiv.coe_addLeft, add_sub_cancel_left, Fin.val_add]
    rw [← pow_eq_pow_mod _ (hζn k), pow_add]
    ring
  have hdetF : F.det ≠ 0 := by
    rw [hF, det_transpose]
    exact det_vandermonde_ne_zero_iff.2 hinj
  have := congrArg det hCF
  rw [det_mul, det_mul, det_diagonal, mul_comm] at this
  exact mul_left_cancel₀ hdetF this

/-- Helper: the column polynomials of Krattenthaler's determinant. -/
lemma g1a_kpoly_natDegree {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R] (a b : Fin n → R)
    (k : Fin n) :
    ((∏ i ∈ Ioi k, (X + C (a i))) *
      ∏ i ∈ (Iic k).filter (fun i : Fin n => 0 < (i : ℕ)), (X + C (b i))).natDegree < n := by
  rw [(monic_prod_of_monic _ _ fun i _ => monic_X_add_C (a i)).natDegree_mul
    (monic_prod_of_monic _ _ fun i _ => monic_X_add_C (b i)),
    natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C (a i),
    natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C (b i)]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
  have h : ((Iic k).filter (fun i : Fin n => 0 < (i : ℕ))).card ≤ k := by
    have : (Iic k).filter (fun i : Fin n => 0 < (i : ℕ)) ⊆ (Iic k).erase ⟨0, Fin.pos k⟩ := by
      intro i hi
      simp only [mem_filter, mem_Iic] at hi
      simp only [mem_erase, mem_Iic, ne_eq, Fin.ext_iff]
      omega
    calc _ ≤ ((Iic k).erase ⟨0, Fin.pos k⟩).card := card_le_card this
      _ = k := by
        rw [card_erase_of_mem (by simp [Fin.le_def]), Fin.card_Iic]; omega
  have := k.isLt
  omega

/-- Helper: `∏_{j<k} (x_j - x_k) = (-1)^{n(n-1)/2} ∏_{j<k} (x_k - x_j)`. -/
lemma g1a_prod_Ioi_sub_swap {n : ℕ} {R : Type*} [CommRing R] (x : Fin n → R) :
    ∏ j, ∏ k ∈ Ioi j, (x j - x k) = (-1) ^ (n * (n - 1) / 2) * ∏ j, ∏ k ∈ Ioi j, (x k - x j) := by
  have hneg : ∀ j : Fin n, ∏ k ∈ Ioi j, (x j - x k) =
      (-1) ^ #(Ioi j) * ∏ k ∈ Ioi j, (x k - x j) := by
    intro j
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun l _ => by ring
  have hcard : ∑ j : Fin n, #(Ioi j) = n * (n - 1) / 2 := by
    simp only [Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i), ← sum_range_id, ← sum_range_reflect]
    exact sum_congr rfl fun i hi => by have := mem_range.1 hi; omega
  simp only [hneg, prod_mul_distrib]
  rw [prod_pow_eq_pow_sum, hcard]

/-- Helper: if every `p_k` has degree less than `n`, then
`det[p_k(x_j)] = det(vandermonde x) · det[coeff_i p_k]`. -/
lemma g1a_det_eval_eq_vandermonde_mul {n : ℕ} {R : Type*} [CommRing R] (p : Fin n → R[X])
    (hp : ∀ k, (p k).natDegree < n) (x : Fin n → R) :
    (Matrix.of fun j k => (p k).eval (x j)).det =
      (vandermonde x).det * (Matrix.of fun (i k : Fin n) => (p k).coeff i).det := by
  rw [← det_mul]
  congr 1
  ext j k
  rw [Matrix.mul_apply, of_apply, eval_eq_sum_range' (hp k),
    ← Fin.sum_univ_eq_sum_range (fun i => (p k).coeff i * x j ^ i)]
  simp [vandermonde_apply, mul_comm]

/-- DLMF 1.3.16 and 1.3.17: Krattenthaler's formula. For
`t_{jk} = (x_j + a_n)(x_j + a_{n-1})⋯(x_j + a_{k+1}) (x_j + b_k)(x_j + b_{k-1})⋯(x_j + b₂)`,
`det[t_{jk}] = ∏_{1≤j<k≤n}(x_j - x_k) ∏_{2≤j≤k≤n}(b_j - a_k)`. Indices are DLMF's, shifted
to `Fin n` (DLMF's index `j` is `j + 1`): `t_{jk} = ∏_{k<i<n} (x_j + a_i) ∏_{0<i≤k} (x_j + b_i)`. -/
@[dlmf 1.3.E16, dlmf 1.3.E17]
theorem det_krattenthaler {n : ℕ} {R : Type*} [CommRing R] (x a b : Fin n → R) :
    (Matrix.of fun j k : Fin n =>
        (∏ i ∈ Ioi k, (x j + a i)) *
          ∏ i ∈ (Iic k).filter (fun i : Fin n => 0 < (i : ℕ)), (x j + b i)).det =
      (∏ j, ∏ k ∈ Ioi j, (x j - x k)) *
        ∏ j ∈ univ.filter (fun j : Fin n => 0 < (j : ℕ)), ∏ k ∈ Ici j, (b j - a k) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  set N := n * (n - 1) / 2
  have hsq : ((-1 : R) ^ N) * (-1) ^ N = 1 := by
    rw [← mul_pow]; simp
  -- the generic case
  set R₀ := MvPolynomial (Fin n ⊕ Fin n) ℤ
  set A₀ : Fin n → R₀ := fun i => MvPolynomial.X (Sum.inl i) with hA₀
  set B₀ : Fin n → R₀ := fun i => MvPolynomial.X (Sum.inr i) with hB₀
  set p₀ : Fin n → R₀[X] := fun k => (∏ i ∈ Ioi k, (X + C (A₀ i))) *
    ∏ i ∈ (Iic k).filter (fun i : Fin n => 0 < (i : ℕ)), (X + C (B₀ i)) with hp₀
  set p : Fin n → R[X] := fun k => (∏ i ∈ Ioi k, (X + C (a i))) *
    ∏ i ∈ (Iic k).filter (fun i : Fin n => 0 < (i : ℕ)), (X + C (b i)) with hp
  set D₀ : R₀ := ∏ j ∈ univ.filter (fun j : Fin n => 0 < (j : ℕ)), ∏ k ∈ Ici j, (B₀ j - A₀ k)
  set D : R := ∏ j ∈ univ.filter (fun j : Fin n => 0 < (j : ℕ)), ∏ k ∈ Ici j, (b j - a k)
  set V₀ : R₀ := ∏ k, ∏ i ∈ Ioi k, (A₀ i - A₀ k)
  have htri : (Matrix.of fun j k => (p₀ k).eval (-A₀ j)).det = V₀ * D₀ := by
    rw [det_of_isUpperTriangular]
    · simp only [of_apply, hp₀, eval_mul, eval_prod, eval_add, eval_X, eval_C, prod_mul_distrib]
      congr 1
      · exact prod_congr rfl fun k _ => prod_congr rfl fun i _ => by ring
      · rw [prod_comm' (t' := univ.filter (fun j : Fin n => 0 < (j : ℕ)))
          (s' := fun j => Ici j) (fun k i => by simp)]
        exact prod_congr rfl fun i _ => prod_congr rfl fun k _ => by ring
    · intro j k hkj
      simp only [of_apply, hp₀, eval_mul, eval_prod, eval_add, eval_X, eval_C]
      rw [prod_eq_zero (i := j) (mem_Ioi.2 (by simpa using hkj)) (by simp), zero_mul]
  have hfac₀ := g1a_det_eval_eq_vandermonde_mul p₀ (fun k => g1a_kpoly_natDegree A₀ B₀ k)
    (fun j => -A₀ j)
  have hV : (vandermonde fun j => -A₀ j).det = (-1) ^ N * V₀ := by
    rw [det_vandermonde]
    have := g1a_prod_Ioi_sub_swap A₀
    simp only [neg_sub_neg]
    rw [this]
  have hVne : V₀ ≠ 0 := by
    refine prod_ne_zero_iff.2 fun k _ => prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 ?_
    intro h
    have := MvPolynomial.X_injective h
    simp only [Sum.inl.injEq] at this
    exact (ne_of_gt (mem_Ioi.1 hi)) this
  have hT₀ : (-1) ^ N * (Matrix.of fun (i k : Fin n) => (p₀ k).coeff i).det = D₀ := by
    refine mul_left_cancel₀ hVne ?_
    rw [← htri, hfac₀, hV]
    ring
  -- specialization
  set φ : R₀ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim a b)
  have hφA : ∀ i, φ (A₀ i) = a i := fun i => MvPolynomial.eval₂_X _ _ _
  have hφB : ∀ i, φ (B₀ i) = b i := fun i => MvPolynomial.eval₂_X _ _ _
  have hpmap : ∀ k, (p₀ k).map φ = p k := fun k => by
    simp only [hp₀, hp, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_add, map_X,
      map_C, hφA, hφB]
  have hT : (Matrix.of fun (i k : Fin n) => (p k).coeff i) =
      φ.mapMatrix (Matrix.of fun (i k : Fin n) => (p₀ k).coeff i) := by
    ext i k
    simp [← hpmap, coeff_map]
  have hD : φ D₀ = D := by simp only [D₀, D, map_prod, map_sub, hφA, hφB]
  have hTR : (-1) ^ N * (Matrix.of fun (i k : Fin n) => (p k).coeff i).det = D := by
    rw [hT, ← RingHom.map_det, ← hD, ← hT₀, map_mul, map_pow, map_neg, map_one]
  have hM : (Matrix.of fun j k : Fin n =>
        (∏ i ∈ Ioi k, (x j + a i)) *
          ∏ i ∈ (Iic k).filter (fun i : Fin n => 0 < (i : ℕ)), (x j + b i)) =
      Matrix.of fun j k => (p k).eval (x j) := by
    ext j k
    simp [hp, eval_prod]
  rw [hM, g1a_det_eval_eq_vandermonde_mul p (fun k => g1a_kpoly_natDegree a b k) x,
    det_vandermonde, g1a_prod_Ioi_sub_swap x, ← hTR]
  linear_combination (-(∏ i, ∏ j ∈ Ioi i, (x j - x i)) *
    (Matrix.of fun (i k : Fin n) => (p k).coeff i).det) * hsq

/-! ### Infinite determinants (§1.3(iii)) -/

/-- DLMF §1.3(iii): infinite determinants of Hill's type (1.3.19) converge. -/
@[dlmf 1.3.iii, dlmf 1.3.E19]
theorem IsHillType.exists_hasInfiniteDet {a : ℤ → ℤ → ℂ} (ha : IsHillType a) :
    ∃ L, HasInfiniteDet a L := by
  sorry

end DLMF.AlgebraicAnalytic
