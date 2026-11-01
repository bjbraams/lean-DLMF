/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Partitions
public import DLMF.QSeries.QBinomial
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate

/-!
# Integer partitions: restricted number and part size (DLMF §26.9)

Partitions of `n` into at most `k` parts, possibly with every part at most `m`, on Mathlib's
`Nat.Partition`: special values, conjugation, the lattice-path interpretation, generating
functions, recurrences and the asymptotic form. The unrestricted `p(n)` is the project's
`DLMF.Partitions.partitionFunction`, and the Gaussian polynomial `[m n]_q` of (26.9.4) is the
project's `DLMF.QSeries.qBinom` (defined by the `q`-Pascal rule).

## Main definitions

* `partitionCountAtMostParts`: `p_k(n)`, partitions of `n` into at most `k` parts.
* `partitionCountBoxed`: `p_k(≤ m, n)`, those with every part at most `m`.
* `latticePathArea`: the area statistic of a north-east lattice path.

## Main results

* `partitionCountAtMostParts_of_le`, `partitionCountAtMostParts_zero`,
  `partitionCountAtMostParts_one`, `partitionCountAtMostParts_two`,
  `partitionCountAtMostParts_three`: special values (DLMF 26.9.1–26.9.3).
* `partitionCountAtMostParts_eq_card_parts_le`, `card_parts_conjugate`: conjugation
  (DLMF §26.9(i)).
* `partitionCountBoxed_eq_card_latticePaths`: `p_k(≤ m, n)` counts lattice paths by area
  (DLMF §26.9(i)).
* `qBinom_eq_prod`: the product form of the Gaussian polynomial (DLMF 26.9.4).
* `hasSum_partitionCountAtMostParts`, `hasSum_qBinom_mul_pow`: DLMF 26.9.5.
* `hasSum_partitionCountBoxed`: `∑ₙ p_k(≤ m, n) qⁿ = [m+k, k]_q` (DLMF 26.9.6).
* `hasSum_partitionCountBoxed_two`, `hasSum_qBinom_mul_pow_x`: DLMF 26.9.7, corrected.
* `partitionCountAtMostParts_succ`, `partitionCountAtMostParts_recurrence`: the recurrences
  (DLMF 26.9.8, 26.9.9).
* `partitionCountAtMostParts_isEquivalent`: `p_k(n) ∼ n^{k-1}/(k! (k-1)!)` (DLMF 26.9.10).

## Implementation notes

* DLMF evaluates `p_k` at negative arguments as `0` (26.9.8); the Lean statements make the case
  split explicit because natural-number subtraction truncates.
* (26.9.7) as printed sums over `m, n` while the summand and both right-hand sides involve a
  fixed `m` and a free `k`; the sum is over `k, n` (verified numerically). The printed
  convergence condition `|xq| < 1` is insufficient: the `n = 0` terms give `∑_k x^k`, so the
  series needs `|x| < 1` (with `|q| < 1`). The corrected statement is used.
* All generating functions are stated with `HasSum`/`HasProd` over `ℂ` for `|q| < 1`; finite
  (polynomial) identities are stated for every `q`, which is stronger than DLMF.

## References

* NIST DLMF §26.9.
-/

@[expose] public section

noncomputable section

open Finset Filter Asymptotics
open DLMF.QSeries DLMF.Partitions

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

/-- (26.9.1): `p_k(n) = p(n)` for `k ≥ n`. -/
@[dlmf 26.9.E1]
theorem partitionCountAtMostParts_of_le {k n : ℕ} (h : n ≤ k) :
    partitionCountAtMostParts k n = partitionFunction n := by
  unfold partitionCountAtMostParts partitionFunction
  rw [Finset.filter_true_of_mem fun p _ => (card_parts_le p).trans h, card_univ]

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

/-- The largest row length of a Young diagram is the first one. -/
private lemma sup_rowLens (μ : YoungDiagram) : (μ.rowLens : Multiset ℕ).sup = μ.rowLen 0 := by
  apply le_antisymm
  · rw [Multiset.sup_le]
    intro x hx
    rw [Multiset.mem_coe, YoungDiagram.rowLens, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact μ.rowLen_anti 0 i (Nat.zero_le i)
  · rcases Nat.eq_zero_or_pos (μ.rowLen 0) with h | h
    · rw [h]; exact Nat.zero_le _
    · apply Multiset.le_sup
      rw [Multiset.mem_coe, YoungDiagram.rowLens, List.mem_map]
      refine ⟨0, ?_, rfl⟩
      rw [List.mem_range, ← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
      exact h

/-- The number of parts of the conjugate is the largest part. -/
private lemma card_parts_conjugate_eq_sup {n : ℕ} (p : n.Partition) :
    p.conjugate.parts.card = p.parts.sup := by
  rw [Nat.Partition.conjugate_parts, Multiset.coe_card, YoungDiagram.length_rowLens,
    YoungDiagram.colLen_transpose]
  have h := YoungDiagram.rowLens_ofPartition_eq_sort_parts p
  have hp : p.parts = ((YoungDiagram.ofPartition p).rowLens : Multiset ℕ) := by
    rw [h, Multiset.sort_eq]
  rw [hp, sup_rowLens]

/-- §26.9(i) by conjugation (used for (26.9.8)). -/
private lemma partitionCountAtMostParts_eq_card_forall_parts_le (k n : ℕ) :
    partitionCountAtMostParts k n = #{p : n.Partition | ∀ i ∈ p.parts, i ≤ k} := by
  unfold partitionCountAtMostParts
  refine Finset.card_bij (fun p _ => p.conjugate) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    rw [← Multiset.sup_le]
    have := card_parts_conjugate_eq_sup p.conjugate
    rw [Nat.Partition.conjugate_conjugate] at this
    rw [← this]; exact hp
  · intro p _ p' _ h
    rw [← Nat.Partition.conjugate_conjugate p, h, Nat.Partition.conjugate_conjugate]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    refine ⟨p.conjugate, ?_, Nat.Partition.conjugate_conjugate p⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [card_parts_conjugate_eq_sup]
    exact Multiset.sup_le.mpr hp

/-- (26.9.8), used for (26.9.3). -/
private lemma partitionCountAtMostParts_succ_eq (k n : ℕ) :
    partitionCountAtMostParts (k + 1) n =
      (if k + 1 ≤ n then partitionCountAtMostParts (k + 1) (n - (k + 1)) else 0) +
        partitionCountAtMostParts k n := by
  classical
  simp only [partitionCountAtMostParts_eq_card_forall_parts_le]
  rw [← Finset.card_filter_add_card_filter_not (p := fun p : n.Partition => k + 1 ∈ p.parts)]
  rw [Finset.filter_filter, Finset.filter_filter]
  congr 1
  · split_ifs with hkn
    · refine Finset.card_bij (fun p hp => Nat.Partition.partitionWithPartEquiv (by omega) hkn
        ⟨p, (mem_filter.mp hp).2.2⟩) ?_ ?_ ?_
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        intro i hi
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
        exact hp.1 i (Multiset.mem_of_mem_erase hi)
      · intro p _ p' _ h
        have := (Nat.Partition.partitionWithPartEquiv (by omega) hkn).injective h
        exact congrArg Subtype.val this
      · intro q hq
        simp only [mem_filter, mem_univ, true_and] at hq
        set x := (Nat.Partition.partitionWithPartEquiv (n := n) (a := k + 1) (by omega) hkn).symm q
        refine ⟨x.1, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]
          refine ⟨fun i hi => ?_, x.2⟩
          rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts, Multiset.mem_cons] at hi
          rcases hi with rfl | hi
          · exact le_rfl
          · exact hq i hi
        · change Nat.Partition.partitionWithPartEquiv _ hkn ⟨x.1, x.2⟩ = q
          rw [Subtype.coe_eta, Equiv.apply_symm_apply]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hp
      have := Nat.Partition.le_of_mem_parts hp.2
      omega
  · congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      have := h1 i hi
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · omega
      · exact absurd (show i = k + 1 by omega ▸ hi) h2
    · intro h
      exact ⟨fun i hi => (h i hi).trans (Nat.le_succ k), fun hk => by have := h _ hk; omega⟩

/-- (26.9.3), second line: `p_2(n) = 1 + ⌊n/2⌋`. -/
@[dlmf 26.9.E3]
theorem partitionCountAtMostParts_two (n : ℕ) : partitionCountAtMostParts 2 n = 1 + n / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [partitionCountAtMostParts_succ_eq 1 n, partitionCountAtMostParts_one]
    split_ifs with h
    · rw [ih (n - 2) (by omega)]; omega
    · omega

/-- (26.9.3), third line: `p_3(n) = 1 + ⌊(n² + 6n)/12⌋`. -/
@[dlmf 26.9.E3]
theorem partitionCountAtMostParts_three (n : ℕ) :
    partitionCountAtMostParts 3 n = 1 + (n ^ 2 + 6 * n) / 12 := by
  have h2 : ∀ n, partitionCountAtMostParts 2 n = 1 + n / 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [partitionCountAtMostParts_succ_eq 1 n, partitionCountAtMostParts_one]
      split_ifs with h
      · rw [ih (n - 2) (by omega)]; omega
      · omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [partitionCountAtMostParts_succ_eq 2 n, h2]
    split_ifs with h
    · rw [ih (n - 3) (by omega)]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      simp only [Nat.add_sub_cancel]
      obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 12 ∧ m = 12 * q + r :=
        ⟨m / 12, m % 12, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 12).symm⟩
      interval_cases r <;> ring_nf <;> generalize q ^ 2 = Q <;> omega
    · interval_cases n <;> rfl

/-- §26.9(i), conjugation: `p_k(n)` also equals the number of partitions of `n` into parts that
are at most `k` (conjugation of Ferrers graphs, `Nat.Partition.conjugate`). -/
@[dlmf 26.9.i]
theorem partitionCountAtMostParts_eq_card_parts_le (k n : ℕ) :
    partitionCountAtMostParts k n = #{p : n.Partition | ∀ i ∈ p.parts, i ≤ k} := by
  exact partitionCountAtMostParts_eq_card_forall_parts_le k n

/-- §26.9(i), conjugation is a bijection: it exchanges the number of parts and the largest
part (Mathlib's `Nat.Partition.conjugate`, the transpose of the Young diagram). -/
@[dlmf 26.9.i]
theorem card_parts_conjugate {n : ℕ} (p : n.Partition) :
    p.conjugate.parts.card = p.parts.sup ∧ p.conjugate.parts.sup = p.parts.card := by
  refine ⟨card_parts_conjugate_eq_sup p, ?_⟩
  have := card_parts_conjugate_eq_sup p.conjugate
  rw [Nat.Partition.conjugate_conjugate] at this
  exact this.symm

/-- The number of lattice points `(h, j)`, `1 ≤ h ≤ m`, `1 ≤ j ≤ k`, above and to the left of
the north-east lattice path from `(0, 0)` to `(m, k)` coded by `w`: `w i = true` means that the
`i`-th step is a north step. For the `h`-th east step at height `y_h` (the number of earlier
north steps) the points `(h, j)` with `y_h < j ≤ k` lie above the path. -/
def latticePathArea {m k : ℕ} (w : Fin (m + k) → Bool) : ℕ :=
  ∑ i : Fin (m + k), if w i then 0 else k - #{i' : Fin (m + k) | i' < i ∧ w i'}

/-- `p_0(n) = δ_{n,0}`. -/
private lemma partitionCountAtMostParts_zero_left (n : ℕ) :
    partitionCountAtMostParts 0 n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [partitionCountAtMostParts_of_le le_rfl, DLMF.Partitions.partitionFunction_zero]
  · exact partitionCountAtMostParts_zero (Nat.pos_of_ne_zero h)

/-- Boxed partitions by conjugation: `p_k(≤ m, n)` counts the partitions with parts `≤ k` and at
most `m` parts. -/
private lemma partitionCountBoxed_eq_card_conj (k m n : ℕ) :
    partitionCountBoxed k m n =
      #{p : n.Partition | (∀ i ∈ p.parts, i ≤ k) ∧ Multiset.card p.parts ≤ m} := by
  unfold partitionCountBoxed
  have hc : ∀ p : n.Partition, p.conjugate.parts.sup = Multiset.card p.parts := fun p =>
    ((card_parts_conjugate p).2)
  have hc' : ∀ p : n.Partition, Multiset.card p.conjugate.parts = p.parts.sup := fun p =>
    ((card_parts_conjugate p).1)
  refine Finset.card_bij (fun p _ => p.conjugate) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    rw [← Multiset.sup_le, hc, hc']
    exact ⟨hp.1, Multiset.sup_le.mpr hp.2⟩
  · intro p _ p' _ h
    rw [← Nat.Partition.conjugate_conjugate p, h, Nat.Partition.conjugate_conjugate]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    refine ⟨p.conjugate, ?_, Nat.Partition.conjugate_conjugate p⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [hc', ← Multiset.sup_le, hc]
    exact ⟨Multiset.sup_le.mpr hp.1, hp.2⟩

/-- The recurrence `p_{k+1}(≤ m+1, n) = p_k(≤ m+1, n) + p_{k+1}(≤ m, n-k-1)`. -/
private lemma partitionCountBoxed_succ_succ (k m n : ℕ) :
    partitionCountBoxed (k + 1) (m + 1) n = partitionCountBoxed k (m + 1) n +
      (if k + 1 ≤ n then partitionCountBoxed (k + 1) m (n - (k + 1)) else 0) := by
  classical
  simp only [partitionCountBoxed_eq_card_conj]
  rw [← Finset.card_filter_add_card_filter_not (p := fun p : n.Partition => k + 1 ∈ p.parts)]
  rw [Finset.filter_filter, Finset.filter_filter, add_comm]
  congr 1
  · congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h3⟩, h2⟩
      refine ⟨fun i hi => ?_, h3⟩
      have := h1 i hi
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · omega
      · exact absurd (show i = k + 1 by omega ▸ hi) h2
    · rintro ⟨h, h3⟩
      exact ⟨⟨fun i hi => (h i hi).trans (Nat.le_succ k), h3⟩, fun hk => by have := h _ hk; omega⟩
  · split_ifs with hkn
    · refine Finset.card_bij (fun p hp => Nat.Partition.partitionWithPartEquiv (by omega) hkn
        ⟨p, (mem_filter.mp hp).2.2⟩) ?_ ?_ ?_
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
        refine ⟨fun i hi => hp.1.1 i (Multiset.mem_of_mem_erase hi), ?_⟩
        rw [Multiset.card_erase_of_mem hp.2, Nat.pred_eq_sub_one]
        omega
      · intro p _ p' _ h
        have := (Nat.Partition.partitionWithPartEquiv (by omega) hkn).injective h
        exact congrArg Subtype.val this
      · intro q hq
        simp only [mem_filter, mem_univ, true_and] at hq
        set x := (Nat.Partition.partitionWithPartEquiv (n := n) (a := k + 1) (by omega) hkn).symm q
        refine ⟨x.1, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]
          have hx : x.1.parts = (k + 1) ::ₘ q.parts :=
            Nat.Partition.partitionWithPartEquiv_symm_apply_parts _ hkn q
          refine ⟨⟨fun i hi => ?_, ?_⟩, x.2⟩
          · rw [hx, Multiset.mem_cons] at hi
            rcases hi with rfl | hi
            · exact le_rfl
            · exact hq.1 i hi
          · rw [hx, Multiset.card_cons]; omega
        · change Nat.Partition.partitionWithPartEquiv _ hkn ⟨x.1, x.2⟩ = q
          rw [Subtype.coe_eta, Equiv.apply_symm_apply]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hp
      have := Nat.Partition.le_of_mem_parts hp.2
      omega

/-- `p_0(≤ m, n) = δ_{n,0}`. -/
private lemma partitionCountBoxed_zero_left (m n : ℕ) :
    partitionCountBoxed 0 m n = if n = 0 then 1 else 0 := by
  have : partitionCountBoxed 0 m n = partitionCountAtMostParts 0 n := by
    unfold partitionCountBoxed partitionCountAtMostParts
    congr 1; ext p
    simp only [mem_filter, mem_univ, true_and, and_iff_left_iff_imp, Nat.le_zero,
      Multiset.card_eq_zero]
    intro h i hi; rw [h] at hi; simp at hi
  rw [this, partitionCountAtMostParts_zero_left]

/-- `p_k(≤ 0, n) = δ_{n,0}`. -/
private lemma partitionCountBoxed_zero_right (k n : ℕ) :
    partitionCountBoxed k 0 n = if n = 0 then 1 else 0 := by
  rw [partitionCountBoxed_eq_card_conj]
  have : #{p : n.Partition | (∀ i ∈ p.parts, i ≤ k) ∧ Multiset.card p.parts ≤ 0} =
      partitionCountAtMostParts 0 n := by
    unfold partitionCountAtMostParts
    congr 1; ext p
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp, Nat.le_zero,
      Multiset.card_eq_zero]
    intro h i hi; rw [h] at hi; simp at hi
  rw [this, partitionCountAtMostParts_zero_left]

/-- The area statistic of a Boolean word of any length, with `k` the target height. -/
def wordArea {N : ℕ} (k : ℕ) (w : Fin N → Bool) : ℕ :=
  ∑ i : Fin N, if w i then 0 else k - #{i' : Fin N | i' < i ∧ w i'}

/-- Lattice paths of length `N` with `k` north steps and area `n`. -/
def areaPathCount (N k n : ℕ) : ℕ := #{w : Fin N → Bool | #{i | w i} = k ∧ wordArea k w = n}

/-- North steps of a word with a first letter. -/
private lemma card_filter_cons_eq_true {N : ℕ} (b : Bool) (w : Fin N → Bool) :
    #{i | (Fin.cons b w : Fin (N + 1) → Bool) i} = (if b then 1 else 0) + #{i | w i} := by
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  simp

/-- Earlier north steps of a word with a first letter. -/
private lemma card_filter_lt_succ_cons_eq_true {N : ℕ} (b : Bool) (w : Fin N → Bool) (i : Fin N) :
    #{i' : Fin (N + 1) | i' < i.succ ∧ (Fin.cons b w : Fin (N + 1) → Bool) i'} =
      (if b then 1 else 0) + #{i' : Fin N | i' < i ∧ w i'} := by
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  simp [Fin.succ_pos, Fin.succ_lt_succ_iff]

/-- Area after a first north step. -/
private lemma wordArea_cons_true {N : ℕ} (k : ℕ) (w : Fin N → Bool) :
    wordArea (k + 1) (Fin.cons true w : Fin (N + 1) → Bool) = wordArea k w := by
  unfold wordArea
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, ite_true, zero_add]
  refine sum_congr rfl fun i _ => ?_
  rw [card_filter_lt_succ_cons_eq_true]
  simp only [ite_true]
  split_ifs <;> omega

/-- Area after a first east step. -/
private lemma wordArea_cons_false {N : ℕ} (k : ℕ) (w : Fin N → Bool) :
    wordArea k (Fin.cons false w : Fin (N + 1) → Bool) = k + wordArea k w := by
  unfold wordArea
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ite_false]
  congr 1
  · have : #{i' : Fin (N + 1) | i' < 0 ∧ (Fin.cons false w : Fin (N + 1) → Bool) i'} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; intro x _ h; exact Fin.not_lt_zero _ h.1
    rw [this]; rfl
  · refine sum_congr rfl fun i _ => ?_
    rw [card_filter_lt_succ_cons_eq_true]
    simp

/-- The lattice-path counts satisfy the recurrence of `p_k(≤ m, n)`. -/
private lemma areaPathCount_succ_succ (N k n : ℕ) :
    areaPathCount (N + 1) (k + 1) n =
      areaPathCount N k n + (if k + 1 ≤ n then areaPathCount N (k + 1) (n - (k + 1)) else 0) := by
  unfold areaPathCount
  rw [card_filter]
  set G : (Fin (N + 1) → Bool) → ℕ := fun w =>
    if #{i | w i} = k + 1 ∧ wordArea (k + 1) w = n then 1 else 0 with hG
  have hsum : ∑ w : Fin (N + 1) → Bool, G w =
      ∑ p : Bool × (Fin N → Bool), G (Fin.cons p.1 p.2) :=
    Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) => Bool)).symm _ _
      (fun w => by simp [Fin.consEquiv])
  rw [hsum, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [hG, card_filter_cons_eq_true, wordArea_cons_true, wordArea_cons_false, ite_true,
    Bool.false_eq_true, ite_false, zero_add]
  rw [card_filter]
  congr 1
  · exact sum_congr rfl fun w _ => by
      congr 1; exact propext ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
  split_ifs with hkn
  · rw [card_filter]
    exact sum_congr rfl fun w _ => by
      congr 1; exact propext ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩
  · exact sum_eq_zero fun w _ => ite_eq_right fun h => by omega

/-- Lattice paths without north steps. -/
private lemma areaPathCount_zero (N n : ℕ) : areaPathCount N 0 n = if n = 0 then 1 else 0 := by
  unfold areaPathCount
  have harea : ∀ w : Fin N → Bool, wordArea 0 w = 0 := fun w => by simp [wordArea]
  have hc : ∀ w : Fin N → Bool, #{i | w i} = 0 ↔ w = fun _ => false := by
    intro w
    rw [card_eq_zero, filter_eq_empty_iff]
    constructor
    · intro h; funext i; simpa using h (mem_univ i)
    · rintro rfl; simp
  simp only [harea, hc]
  split_ifs with hn
  · subst hn; rw [card_eq_one]; exact ⟨fun _ => false, by ext w; simp⟩
  · rw [card_eq_zero, filter_eq_empty_iff]; intro w _ h; exact hn h.2.symm

/-- Lattice paths without east steps. -/
private lemma areaPathCount_self (N n : ℕ) : areaPathCount N N n = if n = 0 then 1 else 0 := by
  unfold areaPathCount
  have hc : ∀ w : Fin N → Bool, #{i | w i} = N ↔ w = fun _ => true := by
    intro w
    have := card_filter_eq_iff (s := (univ : Finset (Fin N))) (p := fun i => w i = true)
    rw [card_univ, Fintype.card_fin] at this
    rw [this]
    constructor
    · intro h; funext i; exact h i (mem_univ i)
    · rintro rfl; simp
  have harea : wordArea N (fun _ : Fin N => true) = 0 := by simp [wordArea]
  simp only [hc]
  split_ifs with hn
  · subst hn
    rw [card_eq_one]
    refine ⟨fun _ => true, ?_⟩
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, harea⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro w _ ⟨rfl, h⟩
    exact hn (h.symm.trans harea)

/-- Boxed partitions and lattice paths satisfy the same recurrence. -/
private lemma partitionCountBoxed_eq_areaPathCount (k m n : ℕ) :
    partitionCountBoxed k m n = areaPathCount (m + k) k n := by
  induction k generalizing m n with
  | zero => rw [partitionCountBoxed_zero_left, areaPathCount_zero]
  | succ k ihk =>
    induction m generalizing n with
    | zero => rw [partitionCountBoxed_zero_right, zero_add, areaPathCount_self]
    | succ m ihm =>
      rw [partitionCountBoxed_succ_succ, show m + 1 + (k + 1) = (m + 1 + k) + 1 by omega,
        areaPathCount_succ_succ, ihk, ihm, show m + (k + 1) = m + 1 + k by omega]

/-- §26.9(i): `p_k(≤ m, n)` equals the number of lattice paths from `(0, 0)` to `(m, k)` (unit
east and north steps) with exactly `n` lattice points `(h, j)`, `1 ≤ h ≤ m`, `1 ≤ j ≤ k`, above
and to the left of the path. -/
@[dlmf 26.9.i]
theorem partitionCountBoxed_eq_card_latticePaths (k m n : ℕ) :
    partitionCountBoxed k m n =
      #{w : Fin (m + k) → Bool | #{i | w i} = k ∧ latticePathArea w = n} :=
  partitionCountBoxed_eq_areaPathCount k m n

/-- The polynomial identity `[m n]_q (q;q)_n = ∏_{i<n} (1 - q^{m-i})` for `n ≤ m`. -/
private lemma qBinom_mul_qPochhammer_eq_prod (q : ℂ) :
    ∀ m n : ℕ, n ≤ m → qBinom q m n * qPochhammer q q n = ∏ i ∈ range n, (1 - q ^ (m - i)) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp
  | succ m ih =>
    intro n hn
    rcases n with _ | n
    · simp
    rw [qBinom_succ_succ, qPochhammer_succ, Finset.prod_range_succ']
    simp only [Nat.sub_zero, Nat.add_sub_add_right]
    have h1 := ih n (by omega)
    rcases Nat.lt_or_ge n m with hnm | hnm
    · have h2 := ih (n + 1) (by omega)
      rw [qPochhammer_succ, Finset.prod_range_succ] at h2
      have hpow : q ^ (n + 1) * q ^ (m - n) = q ^ (m + 1) := by
        rw [← pow_add]; congr 1; omega
      linear_combination (1 - q * q ^ n) * h1 + q ^ (n + 1) * h2 -
        (∏ i ∈ range n, (1 - q ^ (m - i))) * hpow
    · obtain rfl : n = m := by omega
      rw [qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
      linear_combination (1 - q * q ^ n) * h1

/-- (26.9.4): the Gaussian polynomial `[m n]_q = ∏_{j=1}^n (1 - q^{m-n+j})/(1 - q^j)` for
`m ≥ n ≥ 0`, when no denominator vanishes (`q^j ≠ 1` for `1 ≤ j ≤ n`; in particular for
`|q| < 1`). `qBinom` is the project's Gaussian coefficient, defined by the `q`-Pascal rule. -/
@[dlmf 26.9.E4]
theorem qBinom_eq_prod {q : ℂ} {m n : ℕ} (hnm : n ≤ m) (hq : ∀ j ∈ Icc 1 n, q ^ j ≠ 1) :
    qBinom q m n = ∏ j ∈ Icc 1 n, (1 - q ^ (m - n + j)) / (1 - q ^ j) := by
  have hI : ∀ f : ℕ → ℂ, ∏ j ∈ Icc 1 n, f j = ∏ i ∈ range n, f (i + 1) := by
    intro f
    have : Icc 1 n = (range n).image (· + 1) := by
      ext t; simp only [mem_Icc, mem_image, mem_range]
      constructor
      · intro h; exact ⟨t - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega
    rw [this, Finset.prod_image (fun a _ b _ h => by simpa using h)]
  have hP : qPochhammer q q n = ∏ j ∈ Icc 1 n, (1 - q ^ j) := by
    rw [qPochhammer_eq_prod, hI]
    exact prod_congr rfl fun i _ => by ring
  have hne : qPochhammer q q n ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    exact fun j hj => sub_ne_zero.mpr (hq j hj).symm
  have hnum : ∏ j ∈ Icc 1 n, (1 - q ^ (m - n + j)) = ∏ i ∈ range n, (1 - q ^ (m - i)) := by
    rw [hI, ← Finset.prod_range_reflect]
    refine prod_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    congr 2; omega
  rw [Finset.prod_div_distrib, hnum, ← hP, ← qBinom_mul_qPochhammer_eq_prod q m n hnm,
    mul_div_cancel_right₀ _ hne]

/-- Polynomial growth: `p_k(n) ≤ (n+1)^k`. -/
private lemma partitionCountAtMostParts_le_pow (k n : ℕ) :
    partitionCountAtMostParts k n ≤ (n + 1) ^ k := by
  induction k generalizing n with
  | zero => rw [partitionCountAtMostParts_zero_left]; split_ifs <;> simp
  | succ k ihk =>
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      rw [partitionCountAtMostParts_succ_eq]
      have h1 := ihk n
      split_ifs with h
      · have h2 := ihn (n - (k + 1)) (by omega)
        have h3 : (n - (k + 1) + 1) ^ (k + 1) ≤ n ^ (k + 1) :=
          Nat.pow_le_pow_left (by omega) _
        have h4 : n ^ (k + 1) + (n + 1) ^ k ≤ (n + 1) ^ (k + 1) := by
          rw [pow_succ (n + 1), pow_succ n]
          have : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (by omega) _
          nlinarith
        omega
      · simp only [zero_add]
        exact h1.trans (Nat.pow_le_pow_right (by omega) (by omega))

/-- The generating series of `p_k(n)` converges for `|q| < 1`. -/
private lemma summable_partitionCountAtMostParts_mul_pow {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (fun n => (partitionCountAtMostParts k n : ℂ) * q ^ n) := by
  have hr : ‖(‖q‖ : ℝ)‖ < 1 := by rwa [norm_norm]
  have hs : Summable (fun n : ℕ => (2 : ℝ) ^ k * ((n : ℝ) ^ k * ‖q‖ ^ n + ‖q‖ ^ n)) :=
    ((summable_pow_mul_geometric_of_norm_lt_one k hr).add
      (summable_geometric_of_lt_one (norm_nonneg q) hq)).mul_left _
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hb : (partitionCountAtMostParts k n : ℝ) ≤ ((n : ℝ) + 1) ^ k := by
    exact_mod_cast partitionCountAtMostParts_le_pow k n
  have hb2 : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * ((n : ℝ) ^ k + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have h2 : (0 : ℝ) ≤ (0 : ℝ) ^ k := pow_nonneg le_rfl k
      simp only [Nat.cast_zero, zero_add, one_pow]
      nlinarith
    · have : (n : ℝ) + 1 ≤ 2 * n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      calc ((n : ℝ) + 1) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by positivity) this k
        _ = 2 ^ k * n ^ k := by rw [mul_pow]
        _ ≤ 2 ^ k * ((n : ℝ) ^ k + 1) := by nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) k]
  have hq0 : 0 ≤ ‖q‖ ^ n := pow_nonneg (norm_nonneg q) n
  calc (partitionCountAtMostParts k n : ℝ) * ‖q‖ ^ n ≤ 2 ^ k * ((n : ℝ) ^ k + 1) * ‖q‖ ^ n :=
        mul_le_mul_of_nonneg_right (hb.trans hb2) hq0
    _ = 2 ^ k * ((n : ℝ) ^ k * ‖q‖ ^ n + ‖q‖ ^ n) := by ring

/-- (26.9.5), first equality: `∑ p_k(n) qⁿ = ∏_{j=1}^k (1 - q^j)⁻¹` for `|q| < 1`. -/
@[dlmf 26.9.E5]
theorem hasSum_partitionCountAtMostParts {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun n => (partitionCountAtMostParts k n : ℂ) * q ^ n)
      (∏ j ∈ Icc 1 k, (1 - q ^ j)⁻¹) := by
  induction k with
  | zero =>
    simp only [show Icc 1 0 = (∅ : Finset ℕ) from rfl, prod_empty]
    convert hasSum_single (f := fun n => (partitionCountAtMostParts 0 n : ℂ) * q ^ n) 0 ?_ using 1
    · simp [partitionCountAtMostParts_zero_left]
    · intro n hn; simp [partitionCountAtMostParts_zero_left, hn]
  | succ k ih =>
    set S := ∑' n, (partitionCountAtMostParts (k + 1) n : ℂ) * q ^ n
    have hS := (summable_partitionCountAtMostParts_mul_pow hq (k + 1)).hasSum
    have hb : HasSum (fun n => if k + 1 ≤ n then
        (partitionCountAtMostParts (k + 1) (n - (k + 1)) : ℂ) * q ^ n else 0)
        (q ^ (k + 1) * S) := by
      rw [← hasSum_nat_add_iff' (k + 1)]
      have hz : ∑ i ∈ range (k + 1), (if k + 1 ≤ i then
          (partitionCountAtMostParts (k + 1) (i - (k + 1)) : ℂ) * q ^ i else 0) = 0 :=
        sum_eq_zero fun i hi => by simp only [mem_range] at hi; simp [show ¬ k + 1 ≤ i by omega]
      rw [hz, sub_zero]
      convert hS.mul_left (q ^ (k + 1)) using 1
      funext n
      simp only [show k + 1 ≤ n + (k + 1) by omega, ↓reduceIte, Nat.add_sub_cancel]
      ring
    have hsum := hb.add ih
    have heq : S = q ^ (k + 1) * S + ∏ j ∈ Icc 1 k, (1 - q ^ j)⁻¹ := by
      refine hS.unique ?_
      convert hsum using 1
      funext n
      rw [partitionCountAtMostParts_succ_eq]
      split_ifs <;> push_cast <;> ring
    have hne : (1 : ℂ) - q ^ (k + 1) ≠ 0 := by
      have h1 : ‖q ^ (k + 1)‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
      intro h
      rw [sub_eq_zero] at h
      rw [← h] at h1
      simp at h1
    rw [Finset.prod_Icc_succ_top (by omega)]
    convert hS using 1
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hne]
    linear_combination heq

/-- `[m+1+k, k]_q = ∑_{i ≤ k} q^i [m+i, i]_q` (iterated `q`-Pascal rule). -/
private lemma qBinom_add_succ_eq_sum (q : ℂ) (m k : ℕ) :
    qBinom q (m + 1 + k) k = ∑ i ∈ range (k + 1), q ^ i * qBinom q (m + i) i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + 1 + (k + 1) = (m + 1 + k) + 1 by omega, qBinom_succ_succ, ih,
      sum_range_succ (n := k + 1), show m + 1 + k = m + (k + 1) by omega]

/-- The `q`-binomial series `∑_k [m+k, k]_q x^k = ∏_{j=0}^m (1 - x q^j)⁻¹`, with absolute
convergence. -/
private lemma summable_and_hasSum_qBinom_add_mul_pow (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) :
    ∀ x : ℂ, ‖x‖ < 1 → (Summable fun k => ‖qBinom q (m + k) k * x ^ k‖) ∧
      HasSum (fun k => qBinom q (m + k) k * x ^ k) (∏ j ∈ range (m + 1), (1 - x * q ^ j)⁻¹) := by
  induction m with
  | zero =>
    intro x hx
    simp only [zero_add, qBinom_self, one_mul, range_one, prod_singleton, pow_zero, mul_one]
    refine ⟨?_, hasSum_geometric_of_norm_lt_one hx⟩
    simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg x) hx
  | succ m ih =>
    intro x hx
    have hy : ‖q * x‖ < 1 := by
      rw [norm_mul]
      calc ‖q‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hx
    obtain ⟨hn, hs⟩ := ih (q * x) hy
    have hg : Summable fun k => ‖x ^ k‖ := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg x) hx
    have hc : ∀ k, ∑ i ∈ range (k + 1), qBinom q (m + i) i * (q * x) ^ i * x ^ (k - i) =
        qBinom q (m + 1 + k) k * x ^ k := by
      intro k
      rw [qBinom_add_succ_eq_sum, sum_mul]
      refine sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := by simp only [mem_range] at hi; omega
      rw [mul_pow, show x ^ k = x ^ i * x ^ (k - i) by rw [← pow_add]; congr 1; omega]
      ring
    have hS := hasSum_sum_range_mul_of_summable_norm hn hg
    rw [hs.tsum_eq, tsum_geometric_of_norm_lt_one hx] at hS
    have hN := summable_norm_sum_mul_range_of_summable_norm hn hg
    simp_rw [hc] at hS hN
    refine ⟨hN, ?_⟩
    convert hS using 1
    rw [Finset.prod_range_succ' (fun j => (1 - x * q ^ j)⁻¹), pow_zero, mul_one]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    rw [pow_succ]; ring_nf

/-- (26.9.5), second equality: `∏_{j=1}^k (1 - q^j)⁻¹ = 1 + ∑_{m ≥ 1} [k+m-1, m]_q q^m`
for `|q| < 1` (the `m = 0` term of the series is `1`). -/
@[dlmf 26.9.E5]
theorem hasSum_qBinom_mul_pow {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun m => qBinom q (k + m - 1) m * q ^ m) (∏ j ∈ Icc 1 k, (1 - q ^ j)⁻¹) := by
  rcases k with _ | k
  · simp only [show Icc 1 0 = (∅ : Finset ℕ) from rfl, prod_empty]
    convert hasSum_single (f := fun m => qBinom q (0 + m - 1) m * q ^ m) 0 ?_ using 1
    · simp
    · intro m hm
      rw [qBinom_eq_zero_of_lt q (by omega), zero_mul]
  · have h := (summable_and_hasSum_qBinom_add_mul_pow q hq k q hq).2
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simp only [show k + 1 + 1 - 1 = k + 1 by omega]
    convert h using 1
    · funext m; congr 2; omega
    · refine prod_congr rfl fun j _ => ?_
      rw [pow_add, pow_one, mul_comm]

/-- (26.9.6): `∑ₙ p_k(≤ m, n) qⁿ = [m+k, k]_q`; a finite sum, valid for every `q ∈ ℂ` (stronger
than DLMF's `|q| < 1`). -/
@[dlmf 26.9.E6]
theorem hasSum_partitionCountBoxed (q : ℂ) (k m : ℕ) :
    HasSum (fun n => (partitionCountBoxed k m n : ℂ) * q ^ n) (qBinom q (m + k) k) := by
  have hδ : HasSum (fun n : ℕ => ((if n = 0 then 1 else 0 : ℕ) : ℂ) * q ^ n) 1 := by
    convert hasSum_single (f := fun n : ℕ => ((if n = 0 then 1 else 0 : ℕ) : ℂ) * q ^ n) 0
      (fun n hn => by simp [hn]) using 1
    simp
  induction k generalizing m with
  | zero =>
    simp only [qBinom_zero_right, add_zero]
    simpa [partitionCountBoxed_zero_left] using hδ
  | succ k ihk =>
    induction m with
    | zero =>
      simp only [zero_add, qBinom_self]
      simpa [partitionCountBoxed_zero_right] using hδ
    | succ m ihm =>
      have hb : HasSum (fun n => ((if k + 1 ≤ n then partitionCountBoxed (k + 1) m (n - (k + 1))
          else 0 : ℕ) : ℂ) * q ^ n) (q ^ (k + 1) * qBinom q (m + (k + 1)) (k + 1)) := by
        rw [← hasSum_nat_add_iff' (k + 1)]
        have hz : ∑ i ∈ range (k + 1), ((if k + 1 ≤ i then
            partitionCountBoxed (k + 1) m (i - (k + 1)) else 0 : ℕ) : ℂ) * q ^ i = 0 :=
          sum_eq_zero fun i hi => by simp only [mem_range] at hi; simp [show ¬ k + 1 ≤ i by omega]
        rw [hz, sub_zero]
        convert ihm.mul_left (q ^ (k + 1)) using 1
        funext n
        simp only [show k + 1 ≤ n + (k + 1) by omega, ↓reduceIte, Nat.add_sub_cancel]
        ring
      have h := (ihk (m + 1)).add hb
      convert h using 1
      · funext n
        rw [partitionCountBoxed_succ_succ]
        push_cast; ring
      · rw [show m + 1 + (k + 1) = (m + 1 + k) + 1 by omega, qBinom_succ_succ,
          show m + 1 + k = m + (k + 1) by omega]

/-- Boxed partitions vanish beyond `n = k m`. -/
private lemma partitionCountBoxed_eq_zero_of_lt {k m n : ℕ} (h : k * m < n) :
    partitionCountBoxed k m n = 0 := by
  unfold partitionCountBoxed
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨hk, hm⟩
  have h1 := Multiset.sum_le_card_nsmul p.parts m hm
  rw [p.parts_sum, smul_eq_mul] at h1
  have h2 : Multiset.card p.parts * m ≤ k * m := Nat.mul_le_mul_right m hk
  omega

/-- The total number of boxed partitions is `C(m+k, k)`. -/
private lemma sum_partitionCountBoxed (k m : ℕ) :
    ∑ n ∈ range (k * m + 1), partitionCountBoxed k m n = (m + k).choose k := by
  have h := hasSum_partitionCountBoxed 1 k m
  rw [qBinom_one] at h
  have h2 : HasSum (fun n => (partitionCountBoxed k m n : ℂ) * 1 ^ n)
      (∑ n ∈ range (k * m + 1), (partitionCountBoxed k m n : ℂ) * 1 ^ n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [mem_range, not_lt] at hn
      rw [partitionCountBoxed_eq_zero_of_lt (by omega)]; simp)
  have := h.unique h2
  simp only [one_pow, mul_one] at this
  exact_mod_cast this.symm

/-- (26.9.7), corrected: `∑_{k,n} p_k(≤ m, n) x^k qⁿ = ∏_{j=0}^m (1 - x q^j)⁻¹` for `|q| < 1`,
`|x| < 1`. DLMF prints the summation indices as `m, n` and the condition as `|xq| < 1`; the
sum is over `k, n` and needs `|x| < 1` (see the module docstring). -/
@[dlmf 26.9.E7 "corrected: summation over k,n (printed m,n); condition |x|<1 (printed |xq|<1)"]
theorem hasSum_partitionCountBoxed_two {q x : ℂ} (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) (m : ℕ) :
    HasSum (fun kn : ℕ × ℕ => (partitionCountBoxed kn.1 m kn.2 : ℂ) * x ^ kn.1 * q ^ kn.2)
      (∏ j ∈ range (m + 1), (1 - x * q ^ j)⁻¹) := by
  set f : ℕ × ℕ → ℂ := fun kn => (partitionCountBoxed kn.1 m kn.2 : ℂ) * x ^ kn.1 * q ^ kn.2
  set g : ℕ × ℕ → ℝ := fun kn => (partitionCountBoxed kn.1 m kn.2 : ℝ) * ‖x‖ ^ kn.1
  have hg0 : 0 ≤ g := fun kn => by positivity
  have hfib : ∀ k, HasSum (fun n => g (k, n)) (((m + k).choose k : ℝ) * ‖x‖ ^ k) := by
    intro k
    have h2 : HasSum (fun n => g (k, n)) (∑ n ∈ range (k * m + 1), g (k, n)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by
        simp only [mem_range, not_lt] at hn
        simp only [g, partitionCountBoxed_eq_zero_of_lt (show k * m < n by omega)]; simp)
    convert h2 using 1
    simp only [g, ← sum_mul]
    congr 1
    exact_mod_cast (sum_partitionCountBoxed k m).symm
  have hgs : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨fun k => (hfib k).summable, ?_⟩
    simp_rw [fun k => (hfib k).tsum_eq]
    have hr : ‖(‖x‖ : ℝ)‖ < 1 := by rwa [norm_norm]
    have := (hasSum_choose_mul_geometric_of_norm_lt_one m hr).summable
    convert this using 2 with k
    rw [add_comm m k, Nat.choose_symm_add]
  have hfs : Summable f := by
    refine Summable.of_norm_bounded hgs fun kn => ?_
    simp only [f, g, norm_mul, norm_pow, Complex.norm_natCast]
    have : ‖q‖ ^ kn.2 ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
    have h0 : 0 ≤ (partitionCountBoxed kn.1 m kn.2 : ℝ) * ‖x‖ ^ kn.1 := by positivity
    nlinarith
  have hrow : ∀ k, HasSum (fun n => f (k, n)) (qBinom q (m + k) k * x ^ k) := by
    intro k
    convert (hasSum_partitionCountBoxed q k m).mul_right (x ^ k) using 1
    funext n; simp only [f]; ring
  have h1 := hfs.hasSum.prod_fiberwise hrow
  have h2 := (summable_and_hasSum_qBinom_add_mul_pow q hq m x hx).2
  rw [h2.unique h1]
  exact hfs.hasSum

/-- (26.9.7), middle member: `1 + ∑_{k ≥ 1} [m+k, k]_q x^k = ∏_{j=0}^m (1 - x q^j)⁻¹` for
`|q| < 1`, `|x| < 1` (the `k = 0` term is `1`). -/
@[dlmf 26.9.E7 "corrected condition |x|<1"]
theorem hasSum_qBinom_mul_pow_x {q x : ℂ} (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) (m : ℕ) :
    HasSum (fun k => qBinom q (m + k) k * x ^ k) (∏ j ∈ range (m + 1), (1 - x * q ^ j)⁻¹) := by
  exact (summable_and_hasSum_qBinom_add_mul_pow q hq m x hx).2

/-- (26.9.8): `p_k(n) = p_k(n - k) + p_{k-1}(n)` for `k ≥ 1`, with DLMF's convention
`p_k(n - k) = 0` for `n < k` made explicit. -/
@[dlmf 26.9.E8]
theorem partitionCountAtMostParts_succ (k n : ℕ) :
    partitionCountAtMostParts (k + 1) n =
      (if k + 1 ≤ n then partitionCountAtMostParts (k + 1) (n - (k + 1)) else 0) +
        partitionCountAtMostParts k n := by
  exact partitionCountAtMostParts_succ_eq k n

section LogDerivative
open PowerSeries


/-- The generating function of `p_k(n)` as a formal power series. -/
noncomputable def atMostPartsSeries (k : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (partitionCountAtMostParts k n : ℚ)

/-- `∑ₙ [j ∣ n] Xⁿ = 1/(1 - X^j)`. -/
noncomputable def multiplesSeries (j : ℕ) : ℚ⟦X⟧ := PowerSeries.mk fun n => if j ∣ n then 1 else 0

/-- `∑_t (∑_{d ∣ t, d ≤ k} d) X^t`. -/
noncomputable def boundedDivisorSumSeries (k : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun t => ((∑ j ∈ t.divisors with j ≤ k, j : ℕ) : ℚ)

/-- `P₀ = 1`. -/
private lemma atMostPartsSeries_zero : atMostPartsSeries 0 = 1 := by
  ext n
  rw [atMostPartsSeries, coeff_mk, partitionCountAtMostParts_zero_left, coeff_one]
  split_ifs <;> simp

/-- (26.9.8) as a power series identity. -/
private lemma atMostPartsSeries_succ_eq_X_pow_mul_add (k : ℕ) : atMostPartsSeries (k + 1) = X ^ (k + 1) * atMostPartsSeries (k + 1) + atMostPartsSeries k := by
  ext n
  rw [map_add, coeff_X_pow_mul']
  simp only [atMostPartsSeries, coeff_mk]
  rw [partitionCountAtMostParts_succ_eq]
  split_ifs <;> simp

/-- `(1 - X^j) G_j = 1`. -/
private lemma one_sub_X_pow_mul_multiplesSeries {j : ℕ} (hj : 1 ≤ j) : (1 - X ^ j) * multiplesSeries j = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', multiplesSeries, coeff_mk, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; omega
  · rw [ite_eq_right (by omega : n ≠ 0)]
    by_cases hjn : j ≤ n
    · rw [ite_eq_left hjn]
      have : j ∣ n ↔ j ∣ n - j := (Nat.dvd_sub_iff_left hjn (dvd_refl j)).symm
      by_cases h : j ∣ n
      · rw [ite_eq_left h, ite_eq_left (this.1 h)]; ring
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.2 h'))]; ring
    · rw [ite_eq_right hjn, ite_eq_right (fun h => hjn (Nat.le_of_dvd hn h))]; ring

/-- `P_{k+1} = P_k G_{k+1}`. -/
private lemma atMostPartsSeries_succ (k : ℕ) : atMostPartsSeries (k + 1) = atMostPartsSeries k * multiplesSeries (k + 1) := by
  have h1 : atMostPartsSeries (k + 1) * (1 - X ^ (k + 1)) = atMostPartsSeries k := by
    rw [mul_sub, mul_one]
    nth_rewrite 1 [atMostPartsSeries_succ_eq_X_pow_mul_add k]
    ring
  calc atMostPartsSeries (k + 1) = atMostPartsSeries (k + 1) * ((1 - X ^ (k + 1)) * multiplesSeries (k + 1)) := by
        rw [one_sub_X_pow_mul_multiplesSeries (by omega), mul_one]
    _ = atMostPartsSeries k * multiplesSeries (k + 1) := by rw [← mul_assoc, h1]

/-- `X G_j' = G_j · j X^j G_j`. -/
private lemma X_mul_derivative_multiplesSeries {j : ℕ} (hj : 1 ≤ j) :
    X * d⁄dX (multiplesSeries j) = multiplesSeries j * ((j : ℚ⟦X⟧) * X ^ j * multiplesSeries j) := by
  have h := congrArg (fun f : ℚ⟦X⟧ => d⁄dX f) (one_sub_X_pow_mul_multiplesSeries hj)
  rw [Derivation.leibniz, derivative_one, map_sub, derivative_one, derivative_pow, derivative_X,
    zero_sub, mul_one, smul_eq_mul, smul_eq_mul] at h
  have hX : X * X ^ (j - 1) = (X : ℚ⟦X⟧) ^ j := by
    rw [← pow_succ']; congr 1; omega
  have hG := one_sub_X_pow_mul_multiplesSeries hj
  calc X * d⁄dX (multiplesSeries j)
      = X * d⁄dX (multiplesSeries j) * ((1 - X ^ j) * multiplesSeries j) := by rw [hG, mul_one]
    _ = X * multiplesSeries j * ((1 - X ^ j) * d⁄dX (multiplesSeries j)) := by ring
    _ = X * multiplesSeries j * (multiplesSeries j * ((j : ℚ⟦X⟧) * X ^ (j - 1))) := by
        congr 1; linear_combination h
    _ = _ := by rw [← hX]; ring

/-- `D₀ = 0`. -/
private lemma boundedDivisorSumSeries_zero : boundedDivisorSumSeries 0 = 0 := by
  ext t
  rw [boundedDivisorSumSeries, coeff_mk, map_zero]
  have : (t.divisors.filter fun j => j ≤ 0) = ∅ := by
    ext j; simp only [mem_filter, Nat.mem_divisors, notMem_empty, iff_false, not_and]
    intro hj h0
    obtain rfl : j = 0 := by omega
    exact hj.2 (Nat.eq_zero_of_zero_dvd hj.1)
  rw [this]; simp

/-- `D_{k+1} = D_k + (k+1) X^{k+1} G_{k+1}`. -/
private lemma boundedDivisorSumSeries_succ (k : ℕ) :
    boundedDivisorSumSeries (k + 1) = boundedDivisorSumSeries k + ((k + 1 : ℕ) : ℚ⟦X⟧) * X ^ (k + 1) * multiplesSeries (k + 1) := by
  ext t
  rw [map_add, show ((k + 1 : ℕ) : ℚ⟦X⟧) = C ((k + 1 : ℕ) : ℚ) by simp, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul']
  simp only [boundedDivisorSumSeries, multiplesSeries, coeff_mk]
  have hsplit : ∑ j ∈ t.divisors with j ≤ k + 1, j =
      ∑ j ∈ t.divisors with j ≤ k, j + ∑ j ∈ t.divisors with j = k + 1, j := by
    rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> omega
  rw [hsplit, Nat.cast_add, add_right_inj]
  rw [Finset.sum_filter, Finset.sum_ite_eq']
  by_cases h : k + 1 ∈ t.divisors
  · rw [ite_eq_left h]
    rw [Nat.mem_divisors] at h
    have h1 : k + 1 ≤ t := Nat.le_of_dvd (Nat.pos_of_ne_zero h.2) h.1
    rw [ite_eq_left h1, ite_eq_left ((Nat.dvd_sub_iff_left h1 (dvd_refl _)).mpr h.1)]
    push_cast; ring
  · rw [ite_eq_right h]
    rw [Nat.mem_divisors, not_and_or, not_not] at h
    split_ifs with h1 h2 <;> simp
    exfalso
    rcases h with h | rfl
    · exact h ((Nat.dvd_sub_iff_left h1 (dvd_refl _)).mp h2)
    · omega

/-- The logarithmic derivative `X P_k' = P_k D_k`. -/
private lemma X_mul_derivative_atMostPartsSeries (k : ℕ) : X * d⁄dX (atMostPartsSeries k) = atMostPartsSeries k * boundedDivisorSumSeries k := by
  induction k with
  | zero => rw [atMostPartsSeries_zero, boundedDivisorSumSeries_zero, derivative_one]; ring
  | succ k ih =>
    rw [atMostPartsSeries_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, boundedDivisorSumSeries_succ]
    have hG := X_mul_derivative_multiplesSeries (j := k + 1) (by omega)
    calc X * (atMostPartsSeries k * d⁄dX (multiplesSeries (k + 1)) + multiplesSeries (k + 1) * d⁄dX (atMostPartsSeries k))
        = atMostPartsSeries k * (X * d⁄dX (multiplesSeries (k + 1))) + multiplesSeries (k + 1) * (X * d⁄dX (atMostPartsSeries k)) := by
          ring
      _ = _ := by rw [hG, ih]; push_cast; ring

/-- Coefficients of `X f'`. -/
private lemma coeff_X_mul_derivative (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX f) = n * coeff n f := by
  rcases n with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/-- (26.9.9) via the logarithmic derivative of the generating function. -/
private lemma mul_partitionCountAtMostParts_eq_sum_divisors (k n : ℕ) :
    n * partitionCountAtMostParts k n =
      ∑ t ∈ Icc 1 n, partitionCountAtMostParts k (n - t) *
        ∑ j ∈ t.divisors with j ≤ k, j := by
  have h := congrArg (coeff n) (X_mul_derivative_atMostPartsSeries k)
  rw [coeff_X_mul_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => coeff a (atMostPartsSeries k) * coeff b (boundedDivisorSumSeries k)), ← sum_range_reflect] at h
  have hp : ∀ m, coeff m (atMostPartsSeries k) = (partitionCountAtMostParts k m : ℚ) := fun m => coeff_mk _ _
  have hd : ∀ m, coeff m (boundedDivisorSumSeries k) = ((∑ j ∈ m.divisors with j ≤ k, j : ℕ) : ℚ) :=
    fun m => coeff_mk _ _
  simp only [hp, hd, Nat.succ_eq_add_one] at h
  rw [sum_range_succ'] at h
  simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.sub_self, Nat.divisors_zero, filter_empty,
    sum_empty,
    Nat.cast_zero, mul_zero, add_zero] at h
  have h4 : ∀ i ∈ range n, n - (n - (i + 1)) = i + 1 := fun i hi => by
    have := mem_range.mp hi; omega
  rw [sum_congr rfl fun i hi => by rw [h4 i hi]] at h
  have h2 : ∑ t ∈ Icc 1 n, partitionCountAtMostParts k (n - t) *
      ∑ j ∈ t.divisors with j ≤ k, j = ∑ i ∈ range n, partitionCountAtMostParts k (n - (i + 1)) *
        ∑ j ∈ (i + 1).divisors with j ≤ k, j := by
    rw [show Icc 1 n = Ico 1 (n + 1) by ext; simp, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    exact sum_congr rfl fun i _ => by rw [add_comm 1 i]
  rw [h2]
  exact_mod_cast h

end LogDerivative
/-- (26.9.9): `n p_k(n) = ∑_{t=1}^n p_k(n - t) ∑_{j ∣ t, j ≤ k} j` (stated multiplied by `n`,
equivalent to DLMF's form for `n ≥ 1`). -/
@[dlmf 26.9.E9]
theorem partitionCountAtMostParts_recurrence (k n : ℕ) :
    n * partitionCountAtMostParts k n =
      ∑ t ∈ Icc 1 n, partitionCountAtMostParts k (n - t) *
        ∑ j ∈ t.divisors with j ≤ k, j :=
  mul_partitionCountAtMostParts_eq_sum_divisors k n

/-- (26.9.10): `p_k(n) ∼ n^{k-1}/(k! (k-1)!)` as `n → ∞` with `k ≥ 1` fixed. -/
@[dlmf 26.9.E10]
theorem partitionCountAtMostParts_isEquivalent {k : ℕ} (hk : 1 ≤ k) :
    (fun n : ℕ => (partitionCountAtMostParts k n : ℝ)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (k - 1) / ((k.factorial : ℝ) * ((k - 1).factorial : ℝ)) := by
  sorry

end DLMF.Combinatorics
