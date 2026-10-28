/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Tactic.Linarith

/-!
# A bound for generalized pentagonal numbers

The generalized pentagonal number `k (3k - 1)/2` dominates `|k|`.
-/

@[expose] public section

/-- The generalized pentagonal number of `k` is at least `|k|`. -/
theorem Int.natAbs_le_pentagonal (k : ℤ) : k.natAbs ≤ pentagonal k := by
  have h := two_mul_natCast_pentagonal k
  have : (k.natAbs : ℤ) ≤ pentagonal k := by
    rcases le_or_gt 0 k with hk | hk
    · rw [Int.natAbs_of_nonneg hk]; nlinarith
    · rw [Int.ofNat_natAbs_of_nonpos hk.le]; nlinarith
  exact_mod_cast this
