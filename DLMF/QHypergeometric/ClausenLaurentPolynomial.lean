/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.ShiftedFactorials
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Laurent-polynomial continuation for terminating q-Clausen sums

The paired upper parameters `βz` and `β/z` give Laurent polynomials after termination.
Multiplication by the truncation power of `z` yields ordinary polynomials, allowing the
square identity to be extended from a geometric sequence to every nonzero argument.
-/

@[expose] public noncomputable section

open Complex Finset Polynomial
open DLMF.QSeries

namespace DLMF.QHypergeometric.ClausenLaurentPolynomial

/-- The polynomial obtained by clearing the negative powers in two opposite Laurent parameters. -/
def pairPolynomial (β q : ℂ) (k : ℕ) : Polynomial ℂ :=
  ∏ j ∈ range k, (X - C (β * q ^ j)) * (1 - C (β * q ^ j) * X)

/-- Evaluation of the paired polynomial recovers its two shifted factorials. -/
lemma eval_pairPolynomial {z : ℂ} (hz : z ≠ 0) (β q : ℂ) (k : ℕ) :
    (pairPolynomial β q k).eval z =
      z ^ k * qPochhammer (β * z) q k * qPochhammer (β / z) q k := by
  simp only [pairPolynomial, eval_prod, eval_mul, eval_sub, eval_X, eval_C, eval_one,
    qPochhammer_eq_prod]
  rw [show z ^ k = ∏ _j ∈ range k, z by simp, ← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro j hj
  field_simp

/-- A finite Laurent sum with its negative powers cleared by the truncation degree. -/
def sumPolynomial (β q : ℂ) (n : ℕ) (w : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1), C (w k) * X ^ (n - k) * pairPolynomial β q k

/-- Evaluation of the cleared finite Laurent sum. -/
lemma eval_sumPolynomial {z : ℂ} (hz : z ≠ 0) (β q : ℂ) (n : ℕ) (w : ℕ → ℂ) :
    (sumPolynomial β q n w).eval z = z ^ n *
      ∑ k ∈ range (n + 1), w k * qPochhammer (β * z) q k * qPochhammer (β / z) q k := by
  simp only [sumPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    eval_pairPolynomial hz, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have hp : z ^ (n - k) * z ^ k = z ^ n := by rw [← pow_add, Nat.sub_add_cancel hkn]
  linear_combination (w k * qPochhammer (β * z) q k * qPochhammer (β / z) q k) * hp

/-- A finite Laurent square identity follows from its values on a geometric sequence. -/
theorem square_eq_of_forall_geometric {β q : ℂ} (hβ : β ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (n : ℕ) (w v : ℕ → ℂ)
    (h : ∀ N : ℕ,
      (∑ k ∈ range (n + 1), w k * qPochhammer (β * (β * q ^ N)) q k *
        qPochhammer (β / (β * q ^ N)) q k) ^ 2 =
      ∑ k ∈ range (2 * n + 1), v k * qPochhammer (β * (β * q ^ N)) q k *
        qPochhammer (β / (β * q ^ N)) q k)
    {z : ℂ} (hz : z ≠ 0) :
    (∑ k ∈ range (n + 1), w k * qPochhammer (β * z) q k *
      qPochhammer (β / z) q k) ^ 2 =
      ∑ k ∈ range (2 * n + 1), v k * qPochhammer (β * z) q k *
        qPochhammer (β / z) q k := by
  have hinj : Function.Injective (fun N : ℕ => β * q ^ N) := by
    intro i j he
    have he' := congrArg norm (mul_left_cancel₀ hβ he)
    simp only [norm_pow] at he'
    exact (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective he'
  have hpoly : (sumPolynomial β q n w) ^ 2 = sumPolynomial β q (2 * n) v := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective hinj).mono
    rintro a ⟨N, rfl⟩
    change ((sumPolynomial β q n w) ^ 2).eval (β * q ^ N) =
      (sumPolynomial β q (2 * n) v).eval (β * q ^ N)
    have hnode := mul_ne_zero hβ (pow_ne_zero N hq0)
    rw [eval_pow, eval_sumPolynomial hnode, eval_sumPolynomial hnode, mul_pow, h N,
      ← pow_mul, Nat.mul_comm n 2]
  have he := congrArg (Polynomial.eval z) hpoly
  rw [eval_pow, eval_sumPolynomial hz, eval_sumPolynomial hz, mul_pow,
    ← pow_mul, Nat.mul_comm n 2] at he
  exact mul_left_cancel₀ (pow_ne_zero (2 * n) hz) he

end DLMF.QHypergeometric.ClausenLaurentPolynomial
