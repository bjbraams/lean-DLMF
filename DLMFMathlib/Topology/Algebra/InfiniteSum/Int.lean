/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Splitting integer sums into two natural-index sums

An integer-index family with summable nonnegative and nonpositive halves is
the sum of those halves, with its value at zero subtracted once.
-/

@[expose] public section

/-- The two natural-index halves of an integer sum overlap exactly at zero. -/
theorem tsum_int_eq_tsum_natCast_add_tsum_neg_natCast_sub {E : Type*}
    [NormedAddCommGroup E] {f : ℤ → E}
    (hpos : Summable (fun k : ℕ => f (k : ℤ)))
    (hneg : Summable (fun k : ℕ => f (-(k : ℤ)))) :
    (∑' k : ℤ, f k) = (∑' k : ℕ, f (k : ℤ)) + (∑' k : ℕ, f (-(k : ℤ))) - f 0 := by
  have hs : Summable (fun k : ℕ => f (-((k : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hneg
  have H := Summable.sum_add_tsum_nat_add 1 hneg
  simp only [Finset.sum_range_one, Nat.cast_zero, neg_zero, Nat.cast_add, Nat.cast_one] at H
  rw [tsum_of_nat_of_neg_add_one hpos hs, ← H]
  abel
