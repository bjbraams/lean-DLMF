/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.Ring

/-!
# Polynomial moment determinants

A change from monomials to monic polynomials has determinant one. Hence a Hankel
moment determinant equals the product of the squared norms of any monic orthogonal
polynomial basis, for an arbitrary linear functional over a commutative ring.

* `Matrix.det_polynomial_mixed_moment_matrix`: independent monic row and column bases.
* `Matrix.det_polynomial_moment_matrix`: invariance under a monic polynomial basis change.
* `Matrix.det_hankel_eq_prod_of_orthogonal_polynomials`: the orthogonal factorization.

The proof uses Mathlib's `Matrix.det_matrixOfPolynomials` and the polynomial expansion
`Polynomial.as_sum_range_C_mul_X_pow'`.
-/

public noncomputable section

open Polynomial Finset

namespace Matrix

/-- Independent monic polynomial basis changes in the rows and columns preserve
the determinant of a polynomial moment matrix. -/
lemma det_polynomial_mixed_moment_matrix {R : Type*} [CommRing R] {n : ℕ}
    (L : R[X] →ₗ[R] R) (p q : Fin n → R[X])
    (hdeg : ∀ i, (p i).natDegree = i) (hmonic : ∀ i, (p i).Monic)
    (hqdeg : ∀ i, (q i).natDegree = i) (hqmonic : ∀ i, (q i).Monic) :
    (Matrix.of (fun i j => L (p i * q j))).det =
      (Matrix.of (fun i j : Fin n => L (X ^ ((i : ℕ) + j)))).det := by
  classical
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (p j).coeff i
  let B : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (q j).coeff i
  let H : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => L (X ^ ((i : ℕ) + j))
  have hA : A.det = 1 := det_matrixOfPolynomials p hdeg hmonic
  have hB : B.det = 1 := det_matrixOfPolynomials q hqdeg hqmonic
  have hrep (r : Fin n → R[X]) (hr : ∀ i, (r i).natDegree = i) (i : Fin n) :
      r i = ∑ j : Fin n, C ((r i).coeff j) * X ^ (j : ℕ) := by
    calc
      r i = ∑ j ∈ range n, C ((r i).coeff j) * X ^ j :=
        (r i).as_sum_range_C_mul_X_pow' (by rw [hr]; exact i.isLt)
      _ = ∑ j : Fin n, C ((r i).coeff j) * X ^ (j : ℕ) :=
        (Fin.sum_univ_eq_sum_range (fun j => C ((r i).coeff j) * X ^ j) n).symm
  have hmat : A.transpose * H * B = Matrix.of (fun i j => L (p i * q j)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [A, B, H, Matrix.of_apply]
    calc
      _ = ∑ r : Fin n, ∑ s : Fin n,
          (p i).coeff r * (q j).coeff s * L (X ^ ((r : ℕ) + s)) := by
        simp only [sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro r _
        apply sum_congr rfl
        intro s _
        ring
      _ = L ((∑ r : Fin n, C ((p i).coeff r) * X ^ (r : ℕ)) *
          (∑ s : Fin n, C ((q j).coeff s) * X ^ (s : ℕ))) := by
        rw [sum_mul]
        simp only [mul_sum, map_sum]
        apply sum_congr rfl
        intro r _
        apply sum_congr rfl
        intro s _
        have he : (C ((p i).coeff r) * X ^ (r : ℕ)) *
            (C ((q j).coeff s) * X ^ (s : ℕ)) =
              ((p i).coeff r * (q j).coeff s) • (X ^ ((r : ℕ) + s)) := by
          rw [smul_eq_C_mul, map_mul, pow_add]
          ring
        rw [he, map_smul, smul_eq_mul]
      _ = L (p i * q j) := by rw [← hrep p hdeg i, ← hrep q hqdeg j]
  rw [← hmat, det_mul, det_mul, det_transpose, hA, hB, one_mul, mul_one]

/-- A monic polynomial basis preserves the determinant of a polynomial moment matrix. -/
lemma det_polynomial_moment_matrix {R : Type*} [CommRing R] {n : ℕ}
    (L : R[X] →ₗ[R] R) (p : Fin n → R[X])
    (hdeg : ∀ i, (p i).natDegree = i) (hmonic : ∀ i, (p i).Monic) :
    (Matrix.of (fun i j => L (p i * p j))).det =
      (Matrix.of (fun i j : Fin n => L (X ^ ((i : ℕ) + j)))).det :=
  det_polynomial_mixed_moment_matrix L p p hdeg hmonic hdeg hmonic

/-- A Hankel moment determinant is the product of the squared norms of a monic
orthogonal polynomial basis. -/
lemma det_hankel_eq_prod_of_orthogonal_polynomials {R : Type*} [CommRing R] {n : ℕ}
    (L : R[X] →ₗ[R] R) (p : Fin n → R[X])
    (hdeg : ∀ i, (p i).natDegree = i) (hmonic : ∀ i, (p i).Monic)
    (horth : ∀ i j, i ≠ j → L (p i * p j) = 0) :
    (Matrix.of (fun i j : Fin n => L (X ^ ((i : ℕ) + j)))).det =
      ∏ i, L ((p i) ^ 2) := by
  classical
  rw [← det_polynomial_moment_matrix L p hdeg hmonic]
  have he : Matrix.of (fun i j => L (p i * p j)) = Matrix.diagonal (fun i => L ((p i) ^ 2)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [pow_two]
    · simp [hij, horth i j hij]
  rw [he, det_diagonal]

end Matrix
