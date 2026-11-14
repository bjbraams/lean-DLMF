/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Nat.Choose.Multinomial
import DLMFMathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Tactic

/-!
# Multinomial coefficients of polynomial compositions

The multinomial theorem computes coefficients of powers of a sum of monomials.
For a polynomial in a polynomial with zero constant term, the coefficient of degree `n`
is indexed by bounded multiplicities whose weighted sum is `n`.

The proofs use Mathlib's `Finset.sum_pow_eq_sum_piAntidiag` and coefficient API.

* `Polynomial.coeff_pow_sum_monomial`: coefficients of a fixed power.
* `Polynomial.coeff_sum_powers_sum_monomial`: bounded multiplicity indexing.
-/

public noncomputable section

open Finset Polynomial

namespace Polynomial

/-- A product of powers of monomials has the summed degree and the product coefficient. -/
lemma prod_monomial_pow {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (d m : ι → ℕ) (b : ι → R) :
    (∏ j ∈ s, (monomial (d j) (b j) : R[X]) ^ m j) =
      monomial (∑ j ∈ s, d j * m j) (∏ j ∈ s, b j ^ m j) := by
  classical
  simp_rw [monomial_pow]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, ih,
      monomial_mul_monomial]
/-- The coefficient of a power of a sum of monomials is a multinomial sum. -/
lemma coeff_pow_sum_monomial {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) (b : ι → R) (k n : ℕ) :
    ((∑ j ∈ s, (monomial (d j) (b j) : R[X])) ^ k).coeff n =
      ∑ m ∈ piAntidiag s k, (Nat.multinomial s m : R) *
        if n = ∑ j ∈ s, d j * m j then ∏ j ∈ s, b j ^ m j else 0 := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [prod_monomial_pow]
  rw [show (Nat.multinomial s m : R[X]) = C (Nat.multinomial s m : R) by simp]
  simp only [coeff_C_mul, coeff_monomial, eq_comm]
/-- A coefficient of a polynomial in a polynomial with zero constant term is indexed by
the multiplicities of its positive-degree monomials. -/
lemma coeff_sum_powers_sum_monomial {R : Type*} [CommSemiring R]
    (n : ℕ) (A : ℕ → R) (b : Fin n → R) :
    (∑ k ∈ range (n + 1), C (A k) *
      (∑ j : Fin n, (monomial (j.val + 1) (b j) : R[X])) ^ k).coeff n =
      ∑ m ∈ (univ : Finset (Fin n → Fin (n + 1))).filter
          (fun m => ∑ j : Fin n, (j.val + 1) * (m j).val = n),
        A (∑ j, (m j).val) * (Nat.multinomial univ (fun j => (m j).val) : R) *
          ∏ j, b j ^ (m j).val := by
  classical
  rw [finsetSum_coeff]
  simp only [coeff_C_mul]
  have he (k : ℕ) (hk : k ∈ range (n + 1)) :
      ((∑ j : Fin n, (monomial (j.val + 1) (b j) : R[X])) ^ k).coeff n =
        ∑ m ∈ (univ : Finset (Fin n → Fin (n + 1))).filter
            (fun m => ∑ j, (m j).val = k),
          (Nat.multinomial univ (fun j => (m j).val) : R) *
            if n = ∑ j, (j.val + 1) * (m j).val then ∏ j, b j ^ (m j).val else 0 := by
    rw [coeff_pow_sum_monomial]
    exact sum_piAntidiag_eq_sum_bounded n k (by simpa using mem_range.mp hk) _
  rw [Finset.sum_congr rfl (fun k hk => congrArg (A k * ·) (he k hk))]
  simp only [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hw : ∑ j : Fin n, (j.val + 1) * (m j).val = n
  · have hsum : (∑ j : Fin n, (m j).val) ≤ n := by
      calc
        _ ≤ ∑ j : Fin n, (j.val + 1) * (m j).val := by
          apply Finset.sum_le_sum
          intro j _
          exact Nat.le_mul_of_pos_left _ (by omega)
        _ = n := hw
    simp [hw, hsum, mul_assoc]
  · simp [hw, Ne.symm hw]
end Polynomial
