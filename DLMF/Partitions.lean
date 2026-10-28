/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

/-!
# Partitions (AAR Chapter 11)

Mathlib already has `Nat.Partition`, the generating-function formalism `Nat.Partition.genFun`,
Euler's theorem `card_odds_eq_card_distincts`, Glaisher's theorem, and the pentagonal number
theorem. This file records Ramanujan's congruences (AAR §11.7), which are absent.
MacMahon's partition analysis (AAR §§11.2–11.3) is an algorithm, not a theorem list, and is
omitted. Graphical methods (§11.6, Ferrers diagrams) are the Mathlib TODO linking partitions
to Young diagrams.
-/

@[expose] public section

open Nat

namespace DLMF.Partitions

/-- The partition function `p(n)`. -/
abbrev partitionFunction (n : ℕ) : ℕ :=
  Fintype.card (Partition n)

/-- `p(0) = 1`. -/
@[dlmf 27.14.E3]
theorem partitionFunction_zero : partitionFunction 0 = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨(∅ : Multiset ℕ), ?_, ?_⟩, fun p => ?_⟩
  · intro i hi
    cases hi
  · simp
  · ext : 1
    refine Multiset.eq_zero_of_forall_notMem fun i hi => ?_
    have := p.parts_pos hi
    have := Partition.le_of_mem_parts hi
    omega

/-- Ramanujan's congruence `p(5n+4) ≡ 0 (mod 5)` (AAR §11.7). -/
@[dlmf 27.14.v]
theorem ramanujan_mod_five (n : ℕ) : 5 ∣ partitionFunction (5 * n + 4) := by
  sorry

/-- Ramanujan's congruence `p(7n+5) ≡ 0 (mod 7)`. -/
@[dlmf 27.14.v]
theorem ramanujan_mod_seven (n : ℕ) : 7 ∣ partitionFunction (7 * n + 5) := by
  sorry

/-- Ramanujan's congruence `p(11n+6) ≡ 0 (mod 11)`. -/
@[dlmf 27.14.v]
theorem ramanujan_mod_eleven (n : ℕ) : 11 ∣ partitionFunction (11 * n + 6) := by
  sorry

end DLMF.Partitions
