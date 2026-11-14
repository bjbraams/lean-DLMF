/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bounded indexing of finite antidiagonals

A finite sum over functions with total `k ≤ n` can be indexed by functions into
`Fin (n + 1)` with the same total. Every coordinate is bounded by the total.
The empty index type is included.

* `Finset.sum_piAntidiag_eq_sum_bounded`: reindexing a finite antidiagonal.
-/

public noncomputable section

open Finset

namespace Finset

/-- Reindex a finite antidiagonal by functions into a common finite interval. -/
lemma sum_piAntidiag_eq_sum_bounded {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid R]
    (n k : ℕ) (hk : k ≤ n) (F : (ι → ℕ) → R) :
    (∑ m ∈ piAntidiag (univ : Finset ι) k, F m) =
      ∑ m ∈ (univ : Finset (ι → Fin (n + 1))).filter (fun m => ∑ j, (m j).val = k),
        F (fun j => (m j).val) := by
  classical
  apply Finset.sum_bij (fun m hm j => (⟨m j, by
    have hm' := (mem_piAntidiag.mp hm).1
    have hb : m j ≤ k := by
      rw [← hm']
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (mem_univ j)
    exact Nat.lt_succ_of_le (hb.trans hk)⟩ : Fin (n + 1)))
  · intro m hm
    simp only [mem_filter, mem_univ, true_and]
    exact (mem_piAntidiag.mp hm).1
  · intro m hm l hl he
    funext j
    exact congrArg Fin.val (congrFun he j)
  · intro m hm
    refine ⟨(fun j => (m j).val), ?_, ?_⟩
    · simp only [mem_piAntidiag, mem_univ, implies_true, and_true]
      exact (mem_filter.mp hm).2
    · ext j
      rfl
  · intro m _
    rfl
end Finset
