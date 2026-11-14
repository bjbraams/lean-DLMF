/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import DLMFMathlib.LinearAlgebra.Matrix.PolynomialMoments
import Carlson.Jacobi.Norm
import Carlson.Jacobi.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The Hilbert matrix determinant

For a characteristic-zero field, the determinant of `1 / (i + j + 1)` is
`∏_{k < N} (k!)⁴ / ((2k)!(2k+1)!)`, including the empty matrix.

* `Matrix.det_hilbert`: the factorial product formula.

The real proof applies the polynomial moment determinant formula to the normalized
shifted Legendre polynomials. It uses Mathlib's shifted Legendre coefficients and the
proved orthogonality and squared norm APIs from lean-codes,
`Polynomial.integral_shiftedJacobi_mul_shiftedJacobi_eq_zero_nat` and
`Polynomial.integral_shiftedLegendre_sq` in `Carlson.Jacobi.Orthogonality` and
`Carlson.Jacobi.Norm`. Rational descent then gives the identity over every characteristic-zero
field. This theorem-layer support module imports lean-codes.
-/

public noncomputable section

open Polynomial Finset
open scoped Nat

namespace Matrix

/-- Orthogonal shifted Legendre polynomials evaluate the real Hilbert determinant. -/
private lemma det_hilbert_real (N : ℕ) :
    (Matrix.of fun i j : Fin N => (1 : ℝ) / ((i : ℕ) + (j : ℕ) + 1)).det =
      ∏ k ∈ range N, (k ! : ℝ) ^ 4 / (((2 * k) ! : ℝ) * ((2 * k + 1) ! : ℝ)) := by
  let S (n : ℕ) : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)
  have hSdeg (n : ℕ) : (S n).natDegree = n := by
    dsimp only [S]
    rw [natDegree_map_eq_of_injective Int.cast_injective, natDegree_shiftedLegendre]
  have hSlc (n : ℕ) : (S n).leadingCoeff = (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) := by
    rw [leadingCoeff, hSdeg]
    dsimp only [S]
    rw [coeff_map, coeff_shiftedLegendre]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, Nat.choose_self,
      Nat.cast_one, mul_one]
    rw [Nat.two_mul]
  have hSlc0 (n : ℕ) : (S n).leadingCoeff ≠ 0 := by
    rw [hSlc]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega : n ≤ 2 * n)).ne')
  let p (n : ℕ) : ℝ[X] := C ((S n).leadingCoeff⁻¹) * S n
  have hpmonic (n : ℕ) : (p n).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (hSlc0 n))
  have hpdeg (n : ℕ) : (p n).natDegree = n := by
    dsimp only [p]
    rw [natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero (hSlc0 n))), hSdeg]
  let L : ℝ[X] →ₗ[ℝ] ℝ := {
    toFun := fun P => ∫ x in (0 : ℝ)..1, P.eval x
    map_add' := fun P Q => by
      simp only [eval_add]
      exact intervalIntegral.integral_add ((P.continuous).intervalIntegrable 0 1)
        ((Q.continuous).intervalIntegrable 0 1)
    map_smul' := fun c P => by
      simp only [eval_smul, smul_eq_mul]
      exact intervalIntegral.integral_const_mul c _ }
  have hL (n : ℕ) : L (X ^ n) = 1 / ((n : ℝ) + 1) := by
    dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [eval_pow, eval_X]
    rw [integral_pow]
    simp
  have horth (i j : Fin N) (hij : i ≠ j) : L (p i * p j) = 0 := by
    have hz (i j : ℕ) (hij : i < j) : (∫ x in (0 : ℝ)..1, (S i).eval x * (S j).eval x) = 0 := by
      have h := integral_shiftedJacobi_mul_shiftedJacobi_eq_zero_nat 0 0 i j hij
      simpa only [Nat.cast_zero, shiftedJacobi_zero_zero, pow_zero, mul_one] using h
    dsimp only [L, p, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [eval_mul, eval_C]
    have he (x : ℝ) : (S i).leadingCoeff⁻¹ * (S i).eval x *
        ((S j).leadingCoeff⁻¹ * (S j).eval x) =
          ((S i).leadingCoeff⁻¹ * (S j).leadingCoeff⁻¹) * ((S i).eval x * (S j).eval x) := by ring
    rw [intervalIntegral.integral_congr (fun x _ => he x), intervalIntegral.integral_const_mul]
    have hval : (∫ x in (0 : ℝ)..1, (S i).eval x * (S j).eval x) = 0 := by
      rcases lt_or_gt_of_ne (show (i : ℕ) ≠ j from fun h => hij (Fin.ext h)) with h | h
      · exact hz i j h
      · rw [show (fun x : ℝ => (S i).eval x * (S j).eval x) =
          fun x : ℝ => (S j).eval x * (S i).eval x by funext x; ring]
        exact hz j i h
    rw [hval, mul_zero]
  have hnorm (n : ℕ) : L ((p n) ^ 2) = (n ! : ℝ) ^ 4 / (((2 * n) ! : ℝ) * ((2 * n + 1) ! : ℝ)) := by
    dsimp only [L, p, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [eval_pow, eval_mul, eval_C, mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_shiftedLegendre_sq, hSlc]
    have hn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2n : ((2 * n) ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))
    have hC : ((2 * n).choose n : ℝ) = ((2 * n) ! : ℝ) / ((n ! : ℝ) * (n ! : ℝ)) := by
      rw [Nat.cast_choose ℝ (by omega : n ≤ 2 * n), show 2 * n - n = n by omega]
    rw [hC, Nat.factorial_succ, mul_inv, mul_pow, inv_pow]
    have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [hs, inv_one, one_mul]
    push_cast
    have hpos : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn, h2n, hpos]
  have h := det_hankel_eq_prod_of_orthogonal_polynomials L (fun i : Fin N => p i)
    (fun i => hpdeg i) (fun i => hpmonic i) horth
  simp only [hL, hnorm] at h
  rw [Fin.prod_univ_eq_prod_range (fun k => (k ! : ℝ) ^ 4/
    (((2 * k) ! : ℝ) * ((2 * k + 1) ! : ℝ))) N] at h
  simpa only [Nat.cast_add] using h

/-- Descend the real Hilbert determinant identity to the rationals. -/
private lemma det_hilbert_rat (N : ℕ) :
    (Matrix.of fun i j : Fin N => (1 : ℚ) / ((i : ℕ) + (j : ℕ) + 1)).det =
      ∏ k ∈ range N, (k ! : ℚ) ^ 4 / (((2 * k) ! : ℚ) * ((2 * k + 1) ! : ℚ)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_det]
  push_cast
  convert det_hilbert_real N using 1
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply]
  push_cast
  rfl

/-- The Hilbert matrix determinant is the product of the monic shifted Legendre norms. -/
lemma det_hilbert {K : Type*} [Field K] [CharZero K] (N : ℕ) :
    (Matrix.of fun i j : Fin N => (1 : K) / ((i : ℕ) + (j : ℕ) + 1)).det =
      ∏ k ∈ range N, (k ! : K) ^ 4 / (((2 * k) ! : K) * ((2 * k + 1) ! : K)) := by
  have h := congrArg (fun q : ℚ => (q : K)) (det_hilbert_rat N)
  rw [Rat.cast_det] at h
  push_cast at h
  convert h using 1
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply]
  push_cast
  rfl

end Matrix
