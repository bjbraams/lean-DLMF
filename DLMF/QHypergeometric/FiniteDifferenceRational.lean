/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.FiniteDifferencePolynomial
public import DLMF.QHypergeometric.BasicSummations.QGauss
public import Mathlib.Algebra.Polynomial.Div

/-!
# Finite q-differences of rational functions

The finite q-Chu–Vandermonde sum evaluates the q-difference of `1/(1-ux)`.
Polynomial division then evaluates the same functional on `P(x)/(1-ux)` when
the degree of `P` does not exceed the difference order. This is the rational
finite-difference identity used in Wang–Chu, *Approach of q-Derivative Operators
to Terminating q-Series Formulae*, equation (3), https://doi.org/10.2478/cm-2018-0007.
-/

@[expose] public noncomputable section

open Complex Finset Polynomial
open DLMF.QSeries

namespace DLMF.QHypergeometric.FiniteDifferencePolynomial

/-- The finite q-difference of a simple pole is the terminating q-Chu–Vandermonde sum. -/
lemma sum_coefficient_div_one_sub {q u : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ)
    (hu : qPochhammer u q (n + 1) ≠ 0) :
    ∑ k ∈ range (n + 1), coefficient q n k / (1 - u * q ^ k) =
      u ^ n * qPochhammer q q n / qPochhammer u q (n + 1) := by
  have hu0 : 1 - u ≠ 0 := by
    have H := qPochhammer_ne_zero_of_le hu (by omega : 1 ≤ n + 1)
    simpa [qPochhammer_succ] using H
  have huq : qPochhammer (u * q) q n ≠ 0 := by
    rw [qPochhammer_succ'] at hu
    exact right_ne_zero_of_mul hu
  have huqk (k : ℕ) (hk : k ≤ n) : qPochhammer (u * q) q k ≠ 0 :=
    qPochhammer_ne_zero_of_le huq hk
  have huk (k : ℕ) (hk : k ≤ n) : 1 - u * q ^ k ≠ 0 := by
    have H := qPochhammer_ne_zero_of_le hu (by omega : k + 1 ≤ n + 1)
    rw [qPochhammer_succ] at H
    exact right_ne_zero_of_mul H
  have hd : QDenominatorRegularThrough [u * q] q n := by
    simpa [QDenominatorRegularThrough, qPochhammerList] using huq
  have H := q_chu_vandermonde_second (a := u) hq0 hq n hd
  rw [qPhi_two_one_comm, qPhi_terminates hq0 n, qPhiPartial] at H
  have hp : (∏ j ∈ range n, (u - u * q * q ^ j)) =
      u ^ n * qPochhammer q q n := by
    rw [qPochhammer_eq_prod, show u ^ n = ∏ _j ∈ range n, u by simp,
      ← prod_mul_distrib]
    apply prod_congr rfl
    intro j hj
    ring
  rw [hp] at H
  have ht (k : ℕ) (hk : k ∈ range (n + 1)) :
      qPhiTerm [q ^ (-(n : ℤ)), u] [u * q] q q k =
        (1 - u) * (coefficient q n k / (1 - u * q ^ k)) := by
    have hkn : k ≤ n := by simp at hk; omega
    have hqq := qPochhammer_self_ne_zero hq k
    have hshift := qPochhammer_succ' u q k
    rw [qPochhammer_succ] at hshift
    have he : qPhiExponent [q ^ (-(n : ℤ)), u] [u * q] = 0 := by
      simp [qPhiExponent]
    simp only [qPhiTerm, he, zpow_zero, mul_one, qPochhammerList, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, coefficient]
    field_simp [hqq, huqk k hkn, huk k hkn]
    linear_combination qPochhammer (q ^ (-(n : ℤ))) q k * hshift
  rw [sum_congr rfl ht, ← mul_sum] at H
  rw [qPochhammer_succ']
  apply (mul_left_cancel₀ hu0)
  calc
    _ = u ^ n * qPochhammer q q n / qPochhammer (u * q) q n := H
    _ = _ := by field_simp

/-- The finite q-difference evaluates a polynomial divided by a simple pole from the
polynomial's value at the pole. The degree is bounded by the positive difference order. -/
lemma sum_coefficient_eval_div_one_sub {q u : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hu0 : u ≠ 0) (n : ℕ) (hn : 0 < n) (P : Polynomial ℂ) (hP : P.natDegree ≤ n)
    (hu : qPochhammer u q (n + 1) ≠ 0) :
    ∑ k ∈ range (n + 1), coefficient q n k * P.eval (q ^ k) / (1 - u * q ^ k) =
      u ^ n * qPochhammer q q n / qPochhammer u q (n + 1) * P.eval u⁻¹ := by
  let Q := P /ₘ (X - C u⁻¹)
  have hQ : Q.natDegree < n := by
    rw [show Q = P /ₘ (X - C u⁻¹) from rfl,
      natDegree_divByMonic P (monic_X_sub_C u⁻¹), natDegree_X_sub_C]
    omega
  have hsum := sum_eval_eq_zero_of_natDegree_lt hq0 hq Q hQ
  have hden (k : ℕ) (hk : k ∈ range (n + 1)) : 1 - u * q ^ k ≠ 0 := by
    have hkn : k + 1 ≤ n + 1 := by simp at hk; omega
    have H := qPochhammer_ne_zero_of_le hu hkn
    rw [qPochhammer_succ] at H
    exact right_ne_zero_of_mul H
  have ht (k : ℕ) (hk : k ∈ range (n + 1)) :
      P.eval (q ^ k) / (1 - u * q ^ k) =
        P.eval u⁻¹ / (1 - u * q ^ k) - u⁻¹ * Q.eval (q ^ k) := by
    have H := congrArg (fun R : Polynomial ℂ => R.eval (q ^ k))
      (modByMonic_add_div P (X - C u⁻¹))
    rw [modByMonic_X_sub_C_eq_C_eval] at H
    simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at H
    change P.eval u⁻¹ + (q ^ k - u⁻¹) * Q.eval (q ^ k) = P.eval (q ^ k) at H
    field_simp [hu0, hden k hk] at H ⊢
    linear_combination -H
  calc
    _ = ∑ k ∈ range (n + 1), coefficient q n k *
        (P.eval u⁻¹ / (1 - u * q ^ k) - u⁻¹ * Q.eval (q ^ k)) := by
      apply sum_congr rfl
      intro k hk
      rw [mul_div_assoc, ht k hk]
    _ = P.eval u⁻¹ * (∑ k ∈ range (n + 1), coefficient q n k / (1 - u * q ^ k)) -
        u⁻¹ * (∑ k ∈ range (n + 1), coefficient q n k * Q.eval (q ^ k)) := by
      simp only [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [hsum, sum_coefficient_div_one_sub hq0 hq n hu]; ring

end DLMF.QHypergeometric.FiniteDifferencePolynomial
