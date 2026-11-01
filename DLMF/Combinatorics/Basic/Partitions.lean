/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.ModEq

/-!
# Restricted partition and composition counts (DLMF §§26.9–26.11)

The counting functions of restricted integer partitions (DLMF §26.9(i), §26.10(i)) and of
compositions (DLMF §26.11), on Mathlib's `Nat.Partition` and `Composition`.

## Main definitions

* `partitionCountAtMostParts`: `p_k(n)`, partitions of `n` into at most `k` parts.
* `partitionCountBoxed`: `p_k(≤ m, n)`, those with every part at most `m`.
* `partitionCountDistinct`, `partitionCountOdd`: `p(𝒟, n)` and `p(𝒪, n)`.
* `partitionCountAtMostDistinct`, `partitionCountAtMostDistinctBoxed`: `p_m(𝒟, n)` and
  `p_m(≤ k, 𝒟, n)`.
* `partitionCountDiff`: `p(𝒟k, n)`, any two parts differ by at least `k`
  (`PartsDifferAtLeast`).
* `partitionCountSchur`: `p(𝒟'3, n)` (`SchurCondition`).
* `partitionCountIn`: `p(∈ S, n)`; `residueSetPM j k` is `A_{j,k}` and `setGeTwo` is
  `T = {2, 3, …}`.
* `partitionCountDiffTwoNoOne`: `p(𝒟2, ∈ T, n)`.
* `compositionCount`, `compositionCountLength`, `compositionCountNoOne`: `c(n)`, `c_m(n)` and
  `c(∈ T, n)`.

## Main results

* `card_parts_le`: a partition of `n` has at most `n` parts.
* `partitionCountAtMostParts_zero`, `partitionCountAtMostParts_one`: DLMF 26.9.2, 26.9.3
  (first line).
* `partitionCount_zero`: `p(𝒟, 0) = p(𝒟k, 0) = p(∈ S, 0) = 1` (DLMF 26.10.1).
* `compositionCount_zero`, `compositionCountLength_zero`: DLMF 26.11.1, 26.11.2.
* `compositionCountLength_eq_choose`: `c_m(n) = C(n-1, m-1)` (DLMF 26.11.3).

## Implementation notes

The partition function `p(n)` is `DLMF.Partitions.partitionFunction`. The generating functions
and further identities are in `DLMF.Combinatorics.RestrictedPartitions`,
`DLMF.Combinatorics.PartitionIdentities.RestrictedProducts` and
`DLMF.Combinatorics.Compositions`.
-/

@[expose] public section

noncomputable section

open Finset

namespace DLMF.Combinatorics

/-- `p_k(n)`: the number of partitions of `n` into at most `k` parts (DLMF §26.9(i), §27.14(i)). -/
@[dlmf 26.9.i, dlmf 27.14.i]
def partitionCountAtMostParts (k n : ℕ) : ℕ :=
  #{p : n.Partition | p.parts.card ≤ k}

/-- `p_k(≤ m, n)`: the number of partitions of `n` into at most `k` parts, each at most `m`
(DLMF §26.9(i)). -/
@[dlmf 26.9.i]
def partitionCountBoxed (k m n : ℕ) : ℕ :=
  #{p : n.Partition | p.parts.card ≤ k ∧ ∀ i ∈ p.parts, i ≤ m}

/-- A partition of `n` has at most `n` parts. -/
theorem card_parts_le {n : ℕ} (p : n.Partition) : p.parts.card ≤ n := by
  have h : p.parts.card • 1 ≤ p.parts.sum :=
    Multiset.card_nsmul_le_sum fun x hx => p.parts_pos hx
  simpa [p.parts_sum] using h

/-- (26.9.2): `p_0(n) = 0` for `n > 0`. -/
@[dlmf 26.9.E2]
theorem partitionCountAtMostParts_zero {n : ℕ} (hn : 0 < n) :
    partitionCountAtMostParts 0 n = 0 := by
  unfold partitionCountAtMostParts
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hp
  have h0 : p.parts = 0 := Multiset.card_eq_zero.mp (Nat.le_zero.mp hp)
  have := p.parts_sum
  rw [h0, Multiset.sum_zero] at this
  omega

/-- (26.9.3), first line: `p_1(n) = 1`. -/
@[dlmf 26.9.E3]
theorem partitionCountAtMostParts_one (n : ℕ) : partitionCountAtMostParts 1 n = 1 := by
  unfold partitionCountAtMostParts
  rw [Finset.card_eq_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨0, by simp, by simp⟩, ?_⟩
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _; exact Subsingleton.elim _ _
    · rintro rfl; simp
  · refine ⟨Nat.Partition.indiscrete n, ?_⟩
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hp
      ext1
      have hsum := p.parts_sum
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h | h
      · rw [Multiset.card_eq_zero.mp h, Multiset.sum_zero] at hsum; omega
      · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
        rw [ha, Multiset.sum_singleton] at hsum
        rw [ha, hsum]
        simp [Nat.Partition.indiscrete, Nat.Partition.ofSums, Multiset.filter_singleton, hn.ne']
    · rintro rfl
      simp [Nat.Partition.indiscrete, Nat.Partition.ofSums, Multiset.filter_singleton, hn.ne']

/-- `p(𝒟, n)`: partitions of `n` into distinct parts (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountDistinct (n : ℕ) : ℕ := #(Nat.Partition.distincts n)

/-- `p(𝒪, n)`: partitions of `n` into odd parts (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountOdd (n : ℕ) : ℕ := #(Nat.Partition.odds n)

/-- `p_m(𝒟, n)`: partitions of `n` into at most `m` distinct parts (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountAtMostDistinct (m n : ℕ) : ℕ :=
  #{p ∈ Nat.Partition.distincts n | p.parts.card ≤ m}

/-- `p_m(≤ k, 𝒟, n)`: partitions of `n` into at most `m` distinct parts, each at most `k`
(DLMF (26.10.3)). -/
@[dlmf 26.10.E3]
def partitionCountAtMostDistinctBoxed (m k n : ℕ) : ℕ :=
  #{p ∈ Nat.Partition.distincts n | p.parts.card ≤ m ∧ ∀ i ∈ p.parts, i ≤ k}

/-- Any two parts of `p` (two different occurrences) differ by at least `k`. -/
def PartsDifferAtLeast {n : ℕ} (k : ℕ) (p : n.Partition) : Prop :=
  ∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, a + k ≤ b ∨ b + k ≤ a

/-- The minimum-gap condition on the finitely many parts of a partition is decidable. -/
instance {n : ℕ} (k : ℕ) (p : n.Partition) : Decidable (PartsDifferAtLeast k p) := by
  unfold PartsDifferAtLeast; infer_instance

/-- `p(𝒟k, n)`: partitions of `n` into parts with difference at least `k` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountDiff (k n : ℕ) : ℕ := #{p : n.Partition | PartsDifferAtLeast k p}

/-- Schur's condition: parts differ by at least 3, and multiples of 3 by at least 6. -/
def SchurCondition {n : ℕ} (p : n.Partition) : Prop :=
  PartsDifferAtLeast 3 p ∧
    ∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, 3 ∣ a → 3 ∣ b → a + 6 ≤ b ∨ b + 6 ≤ a

/-- Schur condition on the finitely many parts of a partition is decidable. -/
instance {n : ℕ} (p : n.Partition) : Decidable (SchurCondition p) := by
  unfold SchurCondition; infer_instance

/-- `p(𝒟'3, n)`: partitions of `n` into parts with difference at least 3, except that
multiples of 3 must differ by at least 6 (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountSchur (n : ℕ) : ℕ := #{p : n.Partition | SchurCondition p}

/-- `p(∈ S, n)`: partitions of `n` into parts taken from `S` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountIn (S : Set ℕ) [DecidablePred (· ∈ S)] (n : ℕ) : ℕ :=
  #(Nat.Partition.restricted n (· ∈ S))

/-- `A_{j,k} = {n ≥ 1 | n ≡ ±j (mod k)}` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def residueSetPM (j k : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ ((n : ℤ) ≡ j [ZMOD k] ∨ (n : ℤ) ≡ -j [ZMOD k])}

/-- Membership in the two prescribed residue classes is decidable. -/
instance (j k : ℕ) : DecidablePred (· ∈ residueSetPM j k) := fun n => by
  unfold residueSetPM; simp only [Set.mem_ofPred_eq]; infer_instance

/-- `T = {2, 3, 4, …}` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def setGeTwo : Set ℕ := {n | 2 ≤ n}

/-- Membership in the set of natural parts at least two is decidable. -/
instance : DecidablePred (· ∈ setGeTwo) := fun n => by
  unfold setGeTwo; simp only [Set.mem_ofPred_eq]; infer_instance

/-- `p(𝒟2, ∈ T, n)`: difference at least 2 and no part 1. -/
@[dlmf 26.10.i]
def partitionCountDiffTwoNoOne (n : ℕ) : ℕ :=
  #{p : n.Partition | PartsDifferAtLeast 2 p ∧ ∀ i ∈ p.parts, i ∈ setGeTwo}

/-- Identity under the stated parameter and domain assumptions: `#{p : (0 : ℕ).Partition | P p} =
1`. -/
private lemma combBasic_card_filter_partition_zero (P : (0 : ℕ).Partition → Prop) [DecidablePred P]
    (h : ∀ p, p.parts = 0 → P p) : #{p : (0 : ℕ).Partition | P p} = 1 := by
  rw [Finset.filter_true_of_mem fun p _ => h p (Nat.Partition.partition_zero_parts p), card_univ]
  exact Fintype.card_unique

/-- (26.10.1): `p(𝒟, 0) = p(𝒟k, 0) = p(∈ S, 0) = 1`. -/
@[dlmf 26.10.E1]
theorem partitionCount_zero (k : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)] :
    partitionCountDistinct 0 = 1 ∧ partitionCountDiff k 0 = 1 ∧ partitionCountIn S 0 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold partitionCountDistinct Nat.Partition.distincts
    exact combBasic_card_filter_partition_zero _ fun p hp => by rw [hp]; simp
  · unfold partitionCountDiff
    exact combBasic_card_filter_partition_zero _ fun p hp => by
      unfold PartsDifferAtLeast; rw [hp]; simp
  · unfold partitionCountIn Nat.Partition.restricted
    exact combBasic_card_filter_partition_zero _ fun p hp => by rw [hp]; simp

/-- `c(n)`: the number of compositions of `n` (DLMF §26.11). -/
@[dlmf 26.11]
def compositionCount (n : ℕ) : ℕ := Fintype.card (Composition n)

/-- `c_m(n)`: the number of compositions of `n` into exactly `m` parts (DLMF §26.11). -/
@[dlmf 26.11]
def compositionCountLength (m n : ℕ) : ℕ := #{c : Composition n | c.length = m}

/-- `c(∈ T, n)`: the number of compositions of `n` with no part `1`, `T = {2, 3, …}`
(DLMF §26.11). -/
@[dlmf 26.11]
def compositionCountNoOne (n : ℕ) : ℕ := #{c : Composition n | ∀ i ∈ c.blocks, 2 ≤ i}

/-- (26.11.1): `c(0) = c(∈ T, 0) = 1`. -/
@[dlmf 26.11.E1]
theorem compositionCount_zero : compositionCount 0 = 1 ∧ compositionCountNoOne 0 = 1 := by
  refine ⟨by simp [compositionCount, composition_card], ?_⟩
  unfold compositionCountNoOne
  rw [Finset.filter_true_of_mem, card_univ]
  · simp [composition_card]
  · intro c _ i hi
    have h0 : c.blocks = [] := by
      have := c.blocks_sum; rcases h : c.blocks with _ | ⟨a, l⟩
      · rfl
      · have ha := c.blocks_pos (show a ∈ c.blocks by simp [h]); simp [h] at this; omega
    simp [h0] at hi

/-- (26.11.2): `c_m(0) = δ_{0,m}`. -/
@[dlmf 26.11.E2]
theorem compositionCountLength_zero (m : ℕ) :
    compositionCountLength m 0 = if m = 0 then 1 else 0 := by
  unfold compositionCountLength
  have hlen : ∀ c : Composition 0, c.length = 0 := fun c => (Composition.length_eq_zero c).mpr rfl
  split_ifs with hm
  · subst hm
    rw [Finset.filter_true_of_mem fun c _ => hlen c, card_univ]
    simp [composition_card]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    exact hm (hc ▸ hlen c)

/-- For `n ≥ 1`, the boundary-set model of a composition has one element fewer than its
number of blocks. -/
private lemma combBasic_card_compositionAsSetEquiv_add_one {n : ℕ} (hn : 1 ≤ n)
    (d : CompositionAsSet n) :
    ((compositionAsSetEquiv n) d).card + 1 = d.length := by
  classical
  set T := (compositionAsSetEquiv n) d
  have hT : ∀ i : Fin (n - 1), i ∈ T ↔ (⟨1 + (i : ℕ), by omega⟩ : Fin n.succ) ∈ d.boundaries := by
    intro i
    simp [T, compositionAsSetEquiv]
  let emb : Fin (n - 1) ↪ Fin (n + 1) :=
    ⟨fun i => ⟨1 + (i : ℕ), by omega⟩, fun a b h => by
      simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩
  have hemb : ∀ i, ((emb i : Fin (n + 1)) : ℕ) = 1 + i := fun i => rfl
  have hB : d.boundaries = insert 0 (insert (Fin.last n) (T.map emb)) := by
    ext x
    simp only [mem_insert, mem_map]
    constructor
    · intro hx
      by_cases h0 : x = 0
      · exact Or.inl h0
      by_cases hl : x = Fin.last n
      · exact Or.inr (Or.inl hl)
      right; right
      have h0' : (x : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      have hl' : (x : ℕ) ≠ n := fun h => hl (Fin.ext h)
      have hx' := x.isLt
      refine ⟨⟨(x : ℕ) - 1, by omega⟩, ?_, Fin.ext (by rw [hemb]; simp only; omega)⟩
      rw [hT]
      convert hx using 1
      exact Fin.ext (show 1 + ((x : ℕ) - 1) = x by omega)
    · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
      · exact d.zero_mem
      · exact d.getLast_mem
      · exact (hT i).1 hi
  have hlen : d.length = d.boundaries.card - 1 := rfl
  rw [hlen, hB, card_insert_of_notMem, card_insert_of_notMem, card_map]
  · omega
  · simp only [mem_map, not_exists, not_and]
    intro i _ h
    have := congrArg Fin.val h
    rw [hemb, Fin.val_last] at this
    omega
  · simp only [mem_insert, mem_map, not_or, not_exists, not_and]
    refine ⟨fun h => ?_, fun i _ h => ?_⟩
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; rw [hemb] at this; simp at this

/-- (26.11.3): `c_m(n) = C(n-1, m-1)` for `n ≥ 1`, with DLMF's convention `C(n-1, -1) = 0`
for `m = 0` made explicit. -/
@[dlmf 26.11.E3]
theorem compositionCountLength_eq_choose {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    compositionCountLength m n = if m = 0 then 0 else (n - 1).choose (m - 1) := by
  classical
  unfold compositionCountLength
  have h := Finset.card_equiv ((compositionEquiv n).trans (compositionAsSetEquiv n))
    (s := univ.filter fun c : Composition n => c.length = m)
    (t := univ.filter fun s : Finset (Fin (n - 1)) => s.card + 1 = m) (by
      intro c
      simp only [mem_filter, mem_univ, true_and, Equiv.trans_apply]
      rw [combBasic_card_compositionAsSetEquiv_add_one hn]
      simp [compositionEquiv])
  rw [h]
  split_ifs with hm
  · subst hm
    simp
  · rw [show (univ.filter fun s : Finset (Fin (n - 1)) => s.card + 1 = m) =
        powersetCard (m - 1) univ by
      ext s; simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]; omega]
    simp

end DLMF.Combinatorics

end

end
