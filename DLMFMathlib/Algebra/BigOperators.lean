/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring

/-!
# Pairing consecutive terms of finite sums

Small general facts about finite sums and signs used throughout the special-function library.

## Main results

* `Finset.sum_range_two_mul`: a sum over `range (2 m)` is the sum of the consecutive pairs
  `f (2 j) + f (2 j + 1)`.
* `Finset.sum_Icc_one_eq_sum_range_add_one`: reindex a positive initial interval.
* `Finset.sum_range_succ_eq_sum_Icc_of_zero`: remove a zero initial term.
* `Finset.sum_Icc_neg_natCast_eq_sum_range`: pair a symmetric integer sum.
* `neg_one_pow_sub_eq_mul`: split powers of `-1` across natural subtraction.
* `neg_one_pow_mul_neg_one_pow_self`: `(-1)ⁿ (-1)ⁿ = 1`.
-/

@[expose] public section

namespace Finset

/-- A sum over `range (2 m)` is the sum over `j < m` of the pairs `f (2 j) + f (2 j + 1)`. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ range (2 * m), f k = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- Reindex a sum on `1, …, n` by the points `k + 1` for `k < n`. -/
lemma sum_Icc_one_eq_sum_range_add_one {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- Dropping a vanishing `k = 0` term: `∑_{k=0}^n f k = ∑_{k=1}^n f k` when `f 0 = 0`. -/
lemma sum_range_succ_eq_sum_Icc_of_zero {M : Type*} [AddCommMonoid M] (n : ℕ) {f : ℕ → M}
    (h : f 0 = 0) : ∑ k ∈ range (n + 1), f k = ∑ k ∈ Icc 1 n, f k := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), h, zero_add]
  rfl

/-- A sum over the symmetric integer interval `[-N,N]` is its central term plus the
positive-negative pairs indexed by `range N`. -/
lemma sum_Icc_neg_natCast_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (N : ℕ) :
    ∑ n ∈ Icc (-(N : ℤ)) N, f n = f 0 +
      ∑ n ∈ range N, (f (n + 1) + f (-(n + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have he : Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Icc (-(N : ℤ)) N)) := by
      ext k
      simp only [mem_insert, mem_Icc]
      push_cast
      omega
    rw [he, sum_insert (by simp; omega), sum_insert (by simp), ih, sum_range_succ]
    push_cast
    abel

end Finset

/-- The square of `(-1)ⁿ` is `1`: `(-1)ⁿ (-1)ⁿ = 1` in any monoid with a distributive
negation. -/
theorem neg_one_pow_mul_neg_one_pow_self {R : Type*} [Monoid R] [HasDistribNeg R] (n : ℕ) :
    (-1 : R) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- `(-1)^{n-k} = (-1)^n (-1)^k` for `k ≤ n`. -/
lemma neg_one_pow_sub_eq_mul {R : Type*} [Monoid R] [HasDistribNeg R]
    {n k : ℕ} (hk : k ≤ n) :
    (-1 : R) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
  have : (-1 : R) ^ n = (-1) ^ (n - k) * (-1) ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
