/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.Polynomials
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import DLMFMathlib.NumberTheory.BernoulliMoments
import DLMFMathlib.LinearAlgebra.Matrix.PolynomialMoments
import DLMFMathlib.LinearAlgebra.Matrix.HilbertDeterminant

/-!
# The Bernoulli Hankel determinant

Changing the row basis to rising factorials and the column basis to falling factorials
turns the Bernoulli moment matrix into a Hilbert matrix multiplied by signed factorials.
The Hilbert determinant formula then gives DLMF 24.14.11.

The proof uses the generic Bernoulli moment functional and mixed monic basis change
from `DLMFMathlib`, with Mathlib's monic Pochhammer polynomials and determinant scaling APIs.
-/

public noncomputable section

open Finset Polynomial
open scoped Nat

namespace DLMF.BernoulliEuler

/-- DLMF 24.14.11: the Hankel determinant `det[B_{r+s}]_{r,s = 0}^{n}` equals
`(-1)^{n(n+1)/2} (∏_{k = 1}^n k!)⁶ / ∏_{k = 1}^{2n+1} k!`. -/
@[dlmf 24.14.E11]
theorem det_hankel_bernoulli (n : ℕ) :
    (Matrix.of fun r s : Fin (n + 1) => _root_.bernoulli (r + s : ℕ)).det =
      (-1) ^ (n * (n + 1) / 2) * (∏ k ∈ Finset.Icc 1 n, (k ! : ℚ)) ^ 6 /
        ∏ k ∈ Finset.Icc 1 (2 * n + 1), (k ! : ℚ) := by
  obtain ⟨L, hX, hD⟩ := Polynomial.exists_linearMap_pow_eq_bernoulli (K := ℚ)
  let p : Fin (n + 1) → ℚ[X] := fun i => (ascPochhammer ℚ i).comp (X + 1)
  let q : Fin (n + 1) → ℚ[X] := fun j => descPochhammer ℚ j
  have hpdeg (i : Fin (n + 1)) : (p i).natDegree = i := by
    dsimp only [p]
    rw [natDegree_comp, ascPochhammer_natDegree]
    simp
  have hpmonic (i : Fin (n + 1)) : (p i).Monic := by
    exact (monic_ascPochhammer ℚ i).comp
      (by simpa only [map_one] using (monic_X_add_C (1 : ℚ))) (by simp)
  have hqdeg (i : Fin (n + 1)) : (q i).natDegree = i := descPochhammer_natDegree ℚ i
  have hqmonic (i : Fin (n + 1)) : (q i).Monic := monic_descPochhammer ℚ i
  have h := Matrix.det_polynomial_mixed_moment_matrix L p q hpdeg hpmonic hqdeg hqmonic
  simp only [hX, Rat.cast_id] at h
  rw [← h]
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := Matrix.of fun i j => 1 / ((i : ℕ) + (j : ℕ) + 1)
  let u : Fin (n + 1) → ℚ := fun i => ((i : ℕ) ! : ℚ)
  let v : Fin (n + 1) → ℚ := fun j => (-1 : ℚ) ^ (j : ℕ) * ((j : ℕ) ! : ℚ)
  have he : Matrix.of (fun i j => L (p i * q j)) =
      Matrix.of (fun i j => u i * (Matrix.of fun i j => v j * H i j) i j) := by
    ext i j
    simp only [Matrix.of_apply, u, v, H]
    rw [Polynomial.apply_ascPochhammer_mul_descPochhammer L hD]
    ring
  rw [he, Matrix.det_mul_column, Matrix.det_mul_row]
  have hH : H.det = ∏ k ∈ range (n + 1), (k ! : ℚ) ^ 4 / (((2 * k) ! : ℚ) * ((2 * k + 1) ! : ℚ)) :=
    Matrix.det_hilbert (K := ℚ) (n + 1)
  rw [hH]
  dsimp only [u, v]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : (∑ i : Fin (n + 1), (i : ℕ)) = n * (n + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), sum_range_id,
      Nat.add_sub_cancel, Nat.mul_comm]
  rw [hs, Fin.prod_univ_eq_prod_range (fun k => (k ! : ℚ)) (n + 1),
    Finset.prod_div_distrib, Finset.prod_pow]
  have hpairs (N : ℕ) : (∏ k ∈ range N, ((2 * k) ! : ℚ) * ((2 * k + 1) ! : ℚ)) =
      ∏ k ∈ range (2 * N), (k ! : ℚ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [prod_range_succ, show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
        prod_range_succ, prod_range_succ, ← ih]
      ring
  rw [hpairs]
  have hprod (N : ℕ) : (∏ k ∈ range (N + 1), (k ! : ℚ)) = ∏ k ∈ Icc 1 N, (k ! : ℚ) := by
    induction N with
    | zero => simp
    | succ N ih => rw [prod_range_succ, prod_Icc_succ_top (by omega), ih]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, hprod, hprod]
  ring

end DLMF.BernoulliEuler
