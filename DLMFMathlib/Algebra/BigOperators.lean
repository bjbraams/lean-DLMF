/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring

/-!
# Pairing consecutive terms of finite sums

Small general facts used throughout the special-function library: a sum over
`range (2 m)` is the sum of the consecutive pairs `f (2 j) + f (2 j + 1)`, and
`(-1)ⁿ (-1)ⁿ = 1`.
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

end Finset

/-- The square of `(-1)ⁿ` is `1`: `(-1)ⁿ (-1)ⁿ = 1` in any monoid with a distributive
negation. -/
theorem neg_one_pow_mul_neg_one_pow_self {R : Type*} [Monoid R] [HasDistribNeg R] (n : ℕ) :
    (-1 : R) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
