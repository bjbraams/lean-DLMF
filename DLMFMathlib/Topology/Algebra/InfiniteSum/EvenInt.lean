/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.LinearCombination

/-!
# Pairing even bilateral series

An even summable sequence indexed by the integers is its central term plus twice
its positive-index sum. Olver, *Asymptotics and Special Functions*, Chapter 2,
Exercise 9.2, p. 59, uses this pairing for Bessel squares (synopsis O-2.23).
The proof uses Mathlib's integer-to-natural decomposition of summable series.
-/

@[expose] public noncomputable section

/-- The positive-index sum of an even bilateral series is half the total minus the central term.
Olver, Chapter 2, Exercise 9.2, synopsis O-2.23. -/
theorem HasSum.nat_succ_of_even {K : Type*} [NormedField K] [CharZero K]
    [CompleteSpace K] {f : ℤ → K} {S : K} (hf : HasSum f S)
    (heven : ∀ n : ℤ, f (-n) = f n) :
    HasSum (fun n : ℕ => f (n + 1)) ((S - f 0) / 2) := by
  have hn : Summable (fun n : ℕ => f n) := hf.summable.comp_injective Nat.cast_injective
  have ht : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).mpr hn
  have hsplit := hf.nat_add_neg_add_one.tsum_eq
  simp only [heven] at hsplit
  have hsum := hn.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hsum
  rw [hn.tsum_add] at hsplit
  · have heq : (∑' n : ℕ, f ((n : ℤ) + 1)) = (S - f 0) / 2 := by
      linear_combination (hsplit + hsum) / 2
    simpa only [Nat.cast_add, Nat.cast_one, heq] using ht.hasSum
  · simpa only [Nat.cast_add, Nat.cast_one] using ht
