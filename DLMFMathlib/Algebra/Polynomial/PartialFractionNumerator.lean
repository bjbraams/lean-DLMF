/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The polynomial numerator of a sum of simple partial fractions

Multiplying `sum f_i/(z-a_i)` by `prod(z-a_i)` gives the explicit polynomial
`sum C(f_i)*prod_(j != i)(X-C(a_j))`. Its top two coefficients are residue
moments, so a zero sum of residues lowers its degree by one. This is the rational
Fuchsian numerator in Kristensson, *Second Order Differential Equations*,
Chapter 3, Theorem 3.1, p. 32, and Olver, *Asymptotics and Special Functions*,
Chapter 5, §8, pp. 156–158.
-/

@[expose] public noncomputable section

open Finset
open scoped BigOperators

namespace Polynomial

/-- The common-denominator numerator of a finite simple-pole sum. Coincident marked
points and zero residues are allowed in this polynomial definition. -/
def simplePoleNumerator {R : Type*} [CommRing R] {n : ℕ} (a f : Fin n → R) : R[X] :=
  ∑ i, C (f i) * ∏ j ∈ univ.erase i, (X - C (a j))

/-- The defining common-denominator polynomial. -/
theorem simplePoleNumerator_def {R : Type*} [CommRing R] {n : ℕ} (a f : Fin n → R) :
    simplePoleNumerator a f = ∑ i, C (f i) * ∏ j ∈ univ.erase i, (X - C (a j)) := rfl

/-- Evaluation is the corresponding sum of products with one factor omitted.
The numerator used in Kristensson, Theorem 3.1, p. 32. -/
theorem eval_simplePoleNumerator {R : Type*} [CommRing R] {n : ℕ}
    (a f : Fin n → R) (z : R) :
    (simplePoleNumerator a f).eval z = ∑ i, f i * ∏ j ∈ univ.erase i, (z - a j) := by
  simp [simplePoleNumerator, eval_finsetSum, eval_prod]

/-- Dividing the explicit numerator by the common denominator recovers the simple
partial fractions away from the marked points. Kristensson, Theorem 3.1, p. 32. -/
theorem sum_div_sub_eq_eval_simplePoleNumerator_div_prod {K : Type*} [Field K]
    {n : ℕ} (a f : Fin n → K) {z : K} (hz : ∀ i, z ≠ a i) :
    (∑ i, f i / (z - a i)) =
      (simplePoleNumerator a f).eval z / ∏ i, (z - a i) := by
  sorry

/-- The coefficient in the highest possible degree is the sum of the residues.
Kristensson, Chapter 3, Theorem 3.1, p. 32. -/
theorem coeff_simplePoleNumerator_pred {R : Type*} [CommRing R]
    {n : ℕ} (hn : 1 ≤ n) (a f : Fin n → R) :
    (simplePoleNumerator a f).coeff (n - 1) = ∑ i, f i := by
  sorry

/-- The next coefficient is the first residue moment minus the product of the two
zeroth moments. Kristensson, Chapter 3, Theorem 3.1, p. 32. -/
theorem coeff_simplePoleNumerator_sub_two {R : Type*} [CommRing R]
    {n : ℕ} (hn : 2 ≤ n) (a f : Fin n → R) :
    (simplePoleNumerator a f).coeff (n - 2) =
      (∑ i, a i * f i) - (∑ i, a i) * (∑ i, f i) := by
  sorry

/-- If the residues sum to zero, the numerator degree is at most `n-2`.
Kristensson, Chapter 3, Theorem 3.1, p. 32. The zero polynomial is allowed. -/
theorem natDegree_simplePoleNumerator_le_of_sum_eq_zero {R : Type*} [CommRing R]
    {n : ℕ} (hn : 2 ≤ n) (a f : Fin n → R) (hf : ∑ i, f i = 0) :
    (simplePoleNumerator a f).natDegree ≤ n - 2 := by
  sorry

/-- Under the Fuchsian zero-residue-sum constraint, the coefficient of degree
`n-2` is exactly the first residue moment. It need not be a nonzero leading
coefficient if the degree drops further. Kristensson, Theorem 3.1, p. 32. -/
theorem coeff_simplePoleNumerator_sub_two_of_sum_eq_zero {R : Type*} [CommRing R]
    {n : ℕ} (hn : 2 ≤ n) (a f : Fin n → R) (hf : ∑ i, f i = 0) :
    (simplePoleNumerator a f).coeff (n - 2) = ∑ i, a i * f i := by
  rw [coeff_simplePoleNumerator_sub_two hn a f, hf, mul_zero, sub_zero]

end Polynomial
