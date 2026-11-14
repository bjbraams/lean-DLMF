/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sums over canonical modular residues

* `ZMod.sum_univ_val`: summing a function of the canonical representative is the
  sum over the natural range of the modulus.

The proof uses Mathlib's `ZMod.finEquiv` and finite sum reindexing.
-/

public section

open Finset

namespace ZMod

/-- For a nonzero modulus, summing a function of canonical residues agrees with
summing over `0, …, M - 1`. -/
lemma sum_univ_val {A : Type*} [AddCommMonoid A] (M : ℕ) [NeZero M] (f : ℕ → A) :
    (∑ x : ZMod M, f x.val) = ∑ j ∈ range M, f j := by
  rw [← Equiv.sum_comp (ZMod.finEquiv M).toEquiv]
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  congr 1
  rcases M with _ | M
  · exact (NeZero.ne 0 rfl).elim
  · rfl

end ZMod
