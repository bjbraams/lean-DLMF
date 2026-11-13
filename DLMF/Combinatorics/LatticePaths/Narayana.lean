/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams, The Tau Ceti contributors
-/
module

public import DLMF.Combinatorics.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import TauCeti.Combinatorics.NoncrossingPartition.Narayana
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Lattice paths counted by their peaks

Unit-step paths from `(0, 0)` to `(n, n)` above the diagonal correspond to Dyck words and
then to binary trees. The peak-generating polynomial satisfies the first-return recurrence.
The same recurrence describes noncrossing partitions by their number of parts, so the
Narayana formula of DLMF §26.6(i) follows from their proved enumeration.

The path-tree correspondence reuses Mathlib's `DyckWord.equivTreesOfNumNodesEq`.
The noncrossing-polynomial recurrence adapts the proof in
`TauCeti.Combinatorics.NoncrossingPartition.Narayana`, using its public first-part split and
cardinality-invariance theorems. The coefficient count reuses
`TauCeti.NoncrossingPartition.card_parts_eq_div`.

## Main results

* `NarayanaPaths.treePolynomial_eq_blockPolynomial`: equality of the two enumerators.
* `NarayanaPaths.card_latticePaths_peaks`: the Narayana lattice-path count.
-/

public noncomputable section

open Finset

namespace DLMF.Combinatorics

/-- The number of occurrences of a step `(0, 1)` immediately followed by a step `(1, 0)`. -/
@[expose] def numPeaks (l : List (ℕ × ℕ)) : ℕ := (l.zip l.tail).count ((0, 1), (1, 0))

/-- The peak count is the count of up-right pairs in consecutive steps. -/
lemma numPeaks_def (l : List (ℕ × ℕ)) :
    numPeaks l = (l.zip l.tail).count ((0, 1), (1, 0)) := rfl

namespace NarayanaPaths
open DyckStep BinaryTree

/-- The vertical or horizontal unit step corresponding to a Dyck letter. -/
@[expose] def step : DyckStep → ℕ × ℕ
  | U => (0, 1)
  | D => (1, 0)

/-- Read a vertical unit step as `U`, and a horizontal unit step as `D`. -/
@[expose] def readStep (s : ℕ × ℕ) : DyckStep := if s = (0, 1) then U else D

/-- Reading a converted Dyck step recovers that step. -/
lemma readStep_step (s : DyckStep) : readStep (step s) = s := by
  cases s <;> simp [readStep, step]

/-- Converting a valid lattice step to a Dyck letter and back recovers the step. -/
lemma step_readStep {s : ℕ × ℕ} (hs : s ∈ unitSteps) : step (readStep s) = s := by
  simp only [unitSteps, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl <;> simp [readStep, step]

/-- The endpoint of a converted word records its numbers of down and up letters. -/
lemma sum_map_step (l : List DyckStep) :
    (l.map step).sum = (l.count D, l.count U) := by
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp [step, ih, Nat.add_comm]

/-- Reading and converting all steps of a unit-step path recovers its step list. -/
lemma map_step_readStep (l : List (ℕ × ℕ)) (hl : ∀ s ∈ l, s ∈ unitSteps) :
    (l.map readStep).map step = l := by
  rw [List.map_map]
  exact (List.map_congr_left (fun s hs => step_readStep (hl s hs))).trans (List.map_id l)

/-- The unit-step lattice path associated with a Dyck word. -/
@[expose] def toLattice (p : DyckWord) : List (ℕ × ℕ) := p.toList.map step

/-- The empty Dyck word gives the empty lattice path. -/
lemma toLattice_zero : toLattice 0 = [] := rfl

/-- A Dyck word of semilength `n` gives a unit-step path to `(n, n)`. -/
lemma mem_latticePaths_toLattice (p : DyckWord) :
    toLattice p ∈ latticePaths unitSteps p.semilength p.semilength := by
  rw [mem_latticePaths (by decide)]
  constructor
  · intro s hs
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hs
    cases t <;> decide
  · rw [toLattice, sum_map_step, ← p.semilength_eq_count_D]
    rfl

/-- The prefix inequalities of a Dyck word give the diagonal condition. -/
lemma staysWeaklyAboveDiagonal_toLattice (p : DyckWord) :
    StaysWeaklyAboveDiagonal (toLattice p) := by
  intro i _
  simp only [toLattice, ← List.map_take, sum_map_step]
  exact p.count_D_le_count_U i

/-- Read a unit-step path above the diagonal as a Dyck word. -/
@[expose] def ofLattice {n : ℕ} (l : List (ℕ × ℕ)) (hl : l ∈ latticePaths unitSteps n n)
    (ha : StaysWeaklyAboveDiagonal l) : DyckWord where
  toList := l.map readStep
  count_U_eq_count_D := by
    obtain ⟨hs, he⟩ := (mem_latticePaths (by decide)).mp hl
    have h := sum_map_step (l.map readStep)
    rw [map_step_readStep l hs, he] at h
    exact (Prod.mk.inj h).2.symm.trans (Prod.mk.inj h).1
  count_D_le_count_U i := by
    have hs := ((mem_latticePaths (by decide)).mp hl).1
    have h := sum_map_step ((l.take i).map readStep)
    rw [map_step_readStep (l.take i) (fun s hs' => hs s (List.mem_of_mem_take hs'))] at h
    have hi : i ≤ l.length ∨ l.length ≤ i := le_total _ _
    have hh : (l.take i).sum.1 ≤ (l.take i).sum.2 := by
      rcases hi with hi | hi
      · exact ha i (mem_range.mpr (by omega))
      · rw [List.take_of_length_le hi]
        have he := ((mem_latticePaths (by decide)).mp hl).2
        rw [he]
    simpa only [h, ← List.map_take] using hh

/-- The semilength of the Dyck word is the common coordinate of the endpoint. -/
lemma semilength_ofLattice {n : ℕ} (l : List (ℕ × ℕ))
    (hl : l ∈ latticePaths unitSteps n n) (ha : StaysWeaklyAboveDiagonal l) :
    (ofLattice l hl ha).semilength = n := by
  obtain ⟨hs, he⟩ := (mem_latticePaths (by decide)).mp hl
  have h := sum_map_step (l.map readStep)
  rw [map_step_readStep l hs, he] at h
  exact (Prod.mk.inj h).2.symm

/-- Converting a valid lattice path to a Dyck word and back recovers the path. -/
lemma toLattice_ofLattice {n : ℕ} (l : List (ℕ × ℕ))
    (hl : l ∈ latticePaths unitSteps n n) (ha : StaysWeaklyAboveDiagonal l) :
    toLattice (ofLattice l hl ha) = l :=
  map_step_readStep l (((mem_latticePaths (by decide)).mp hl).1)

/-- Converting a Dyck word to a lattice path and back recovers the word. -/
lemma ofLattice_toLattice (p : DyckWord) :
    ofLattice (toLattice p) (mem_latticePaths_toLattice p)
      (staysWeaklyAboveDiagonal_toLattice p) = p := by
  apply DyckWord.ext
  simp only [ofLattice, toLattice, List.map_map]
  exact List.map_id'' readStep_step p.toList

/-- The empty path has no peaks. -/
lemma numPeaks_nil : numPeaks [] = 0 := rfl

/-- The initial pair contributes one peak precisely when it is up then right. -/
lemma numPeaks_cons_cons (s t : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    numPeaks (s :: t :: l) =
      (if s = (0, 1) ∧ t = (1, 0) then 1 else 0) + numPeaks (t :: l) := by
  by_cases hs : s = (0, 1) <;> by_cases ht : t = (1, 0) <;>
    simp [numPeaks, Prod.mk.injEq, hs, ht, Nat.add_comm]

/-- A horizontal step at the beginning cannot create a peak. -/
lemma numPeaks_down_cons (l : List (ℕ × ℕ)) : numPeaks ((1, 0) :: l) = numPeaks l := by
  cases l with
  | nil => rfl
  | cons s l => rw [numPeaks_cons_cons]; simp

/-- A separating horizontal step allows the peak counts to be added. -/
lemma numPeaks_append_down (a b : List (ℕ × ℕ)) :
    numPeaks (a ++ (1, 0) :: b) = numPeaks (a ++ [(1, 0)]) + numPeaks b := by
  induction a with
  | nil => simp only [List.nil_append, numPeaks_down_cons, numPeaks_nil, zero_add]
  | cons s a ih =>
    cases a with
    | nil =>
      simp only [List.nil_append, List.cons_append, numPeaks_cons_cons,
        numPeaks_down_cons, numPeaks_nil]
      omega
    | cons t a =>
      simp only [List.cons_append, numPeaks_cons_cons] at ih ⊢
      omega

/-- The lattice path obtained from the Dyck word of a binary tree. -/
@[expose] def treePath (t : BinaryTree Unit) : List (ℕ × ℕ) := toLattice (DyckWord.ofTree t)

/-- The empty binary tree gives the empty path. -/
lemma treePath_nil : treePath BinaryTree.nil = [] := rfl

/-- A tree node nests the left path and appends the right path. -/
lemma treePath_node (l r : BinaryTree Unit) :
    treePath (l △ r) = (0, 1) :: (treePath l ++ (1, 0) :: treePath r) := by
  dsimp only [treePath, toLattice, DyckWord.ofTree, DyckWord.nest, HAdd.hAdd, Add.add]
  simp only [List.map_cons, List.map_append, step, List.cons_append,
    List.nil_append, List.append_assoc]

/-- Concatenating Dyck words concatenates their lattice paths. -/
lemma toLattice_add (p q : DyckWord) : toLattice (p + q) = toLattice p ++ toLattice q := by
  dsimp only [toLattice, HAdd.hAdd, Add.add]
  exact List.map_append

/-- Nesting a Dyck word adds an initial vertical and a final horizontal step. -/
lemma toLattice_nest (p : DyckWord) :
    toLattice p.nest = (0, 1) :: (toLattice p ++ [(1, 0)]) := by
  simp only [toLattice, DyckWord.nest, List.map_cons, List.map_append, List.map_nil, step,
    List.cons_append, List.nil_append]

/-- Every nonempty Dyck path begins vertically and ends horizontally. -/
lemma exists_toLattice_eq_up_append_down {p : DyckWord} (hp : p ≠ 0) :
    ∃ b, toLattice p = (0, 1) :: (b ++ [(1, 0)]) := by
  refine ⟨p.toList.dropLast.tail.map step, ?_⟩
  have h := congrArg (List.map step) (p.cons_tail_dropLast_concat hp)
  simp only [List.map_append, List.map_cons, List.map_nil, step] at h
  exact h.symm

/-- Concatenating Dyck paths adds their peak counts. -/
lemma numPeaks_toLattice_add (p q : DyckWord) :
    numPeaks (toLattice (p + q)) = numPeaks (toLattice p) + numPeaks (toLattice q) := by
  rw [toLattice_add]
  by_cases hp : p = 0
  · subst p
    rw [toLattice_zero, List.nil_append, numPeaks_nil, zero_add]
  · obtain ⟨b, hb⟩ := exists_toLattice_eq_up_append_down hp
    rw [hb]
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      numPeaks_append_down ((0, 1) :: b) (toLattice q)

/-- Nesting creates one peak only when the nested path is empty. -/
lemma numPeaks_toLattice_nest (p : DyckWord) :
    numPeaks (toLattice p.nest) = if p = 0 then 1 else numPeaks (toLattice p) := by
  rw [toLattice_nest]
  by_cases hp : p = 0
  · subst p
    rfl
  · rw [ite_eq_right hp]
    obtain ⟨b, hb⟩ := exists_toLattice_eq_up_append_down hp
    rw [hb, List.cons_append, numPeaks_cons_cons]
    norm_num only [Prod.mk.injEq, true_and, false_and, ite_false, zero_add]
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append,
      numPeaks_down_cons,
      numPeaks_nil, add_zero] using numPeaks_append_down ((0, 1) :: b) [(1, 0)]

open Polynomial
open TauCeti

/-- The generating polynomial of the number of parts of noncrossing partitions. -/
@[expose] def blockPolynomial {α : Type*} [LinearOrder α] (s : Finset α) : ℚ[X] :=
  ∑ P : NoncrossingPartition s, X ^ #P.1.parts

/-- The part-generating polynomial depends only on the number of positions. -/
lemma blockPolynomial_of_card_eq {α β : Type*} [LinearOrder α] [LinearOrder β]
    {s : Finset α} {t : Finset β} (h : #s = #t) : blockPolynomial s = blockPolynomial t :=
  NoncrossingPartition.sum_comp_card_parts_eq_of_card_eq h (fun k => (X : ℚ[X]) ^ k)

/-- The empty set has a single noncrossing partition with no parts. -/
lemma blockPolynomial_empty {α : Type*} [LinearOrder α] :
    blockPolynomial (∅ : Finset α) = 1 := by
  unfold blockPolynomial
  rw [NoncrossingPartition.sum_comp_card_parts_of_card_eq_zero (by simp)]
  simp

/-- Separate the weight of the part through the least position. -/
lemma blockPolynomial_first_part {α : Type*} [LinearOrder α] (s : Finset α) (m : α)
    (hm : s.Nonempty → m ∈ s) :
    (∑ P : NoncrossingPartition s, (X : ℚ[X]) * ∏ B ∈ P.1.parts with m ∉ B, X) =
      if #s = 0 then X else blockPolynomial s := by
  by_cases hs : #s = 0
  · obtain rfl := card_eq_zero.mp hs
    rw [ite_eq_left hs, Fintype.sum_unique, Finpartition.parts_eq_empty_iff.mpr rfl]
    simp
  · rw [ite_eq_right hs, blockPolynomial]
    apply sum_congr rfl
    intro P _
    have he := P.1.prod_parts_eq_mul_prod_filter_notMem
      (hm (nonempty_of_ne_empty fun h => hs (by simp [h]))) (fun _ => (X : ℚ[X]))
    rw [prod_const] at he
    exact he.symm

/-- Split a noncrossing partition at the last position of its first part. -/
lemma blockPolynomial_eq_sum {α : Type*} [LinearOrder α] {s : Finset α}
    (hs : s.Nonempty) :
    blockPolynomial s = ∑ x ∈ s,
      (if #{y ∈ s | y < x} = 0 then X else blockPolynomial {y ∈ s | y < x}) *
        blockPolynomial {y ∈ s | x < y} := by
  have h := NoncrossingPartition.sum_mul_prod_eq_sum_mul_sum (M := ℚ[X]) hs
    (fun _ => X) (fun _ => X)
  have hL := blockPolynomial_first_part s (s.min' hs) (fun _ => s.min'_mem hs)
  rw [ite_eq_right hs.card_pos.ne'] at hL
  beta_reduce at h
  rw [hL] at h
  rw [h]
  apply sum_congr rfl
  intro x _
  congr 1
  · refine blockPolynomial_first_part _ _ (fun hne => ?_)
    obtain ⟨y, hy⟩ := hne
    obtain ⟨hys, hyx⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨s.min'_mem hs, (s.min'_le y hys).trans_lt hyx⟩
  · simp only [blockPolynomial, prod_const]

/-- A node with empty left subtree creates a peak; other nodes preserve left peaks. -/
lemma numPeaks_treePath_node (l r : BinaryTree Unit) :
    numPeaks (treePath (l △ r)) =
      (if l = BinaryTree.nil then 1 else numPeaks (treePath l)) + numPeaks (treePath r) := by
  dsimp only [treePath]
  rw [DyckWord.ofTree, numPeaks_toLattice_add, numPeaks_toLattice_nest]
  by_cases hl : l = BinaryTree.nil
  · subst l
    rfl
  · have hp : DyckWord.ofTree l ≠ 0 := by
      intro h
      have he := congrArg DyckWord.toTree h
      rw [DyckWord.toTree_ofTree] at he
      exact hl (by simpa only [DyckWord.toTree, ↓reduceIte] using he)
    rw [ite_eq_right hl, ite_eq_right hp]

/-- The peak-generating polynomial of the paths of binary trees with `n` nodes. -/
@[expose] def treePolynomial (n : ℕ) : ℚ[X] :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n, X ^ numPeaks (treePath t)

/-- The empty tree contributes the constant polynomial one. -/
lemma treePolynomial_zero : treePolynomial 0 = 1 := by
  rw [treePolynomial, BinaryTree.treesOfNumNodesEq_zero, sum_singleton, treePath_nil,
    numPeaks_nil, pow_zero]

/-- The weight of a node factors through its two subtrees. -/
lemma treeWeight_node {i : ℕ} {l : BinaryTree Unit}
    (hl : l ∈ BinaryTree.treesOfNumNodesEq i) (r : BinaryTree Unit) :
    (X : ℚ[X]) ^ numPeaks (treePath (l △ r)) =
      (if i = 0 then X else X ^ numPeaks (treePath l)) * X ^ numPeaks (treePath r) := by
  rw [numPeaks_treePath_node, pow_add]
  by_cases hi : i = 0
  · subst i
    have he : l = BinaryTree.nil := by simpa using hl
    simp only [he, ite_true, pow_one]
  · have hln : l ≠ BinaryTree.nil := by
      intro h
      have he := BinaryTree.mem_treesOfNumNodesEq.mp hl
      exact hi (by simpa only [h, BinaryTree.numNodes] using he.symm)
    rw [ite_eq_right hi, ite_eq_right hln]

/-- The peak-generating polynomials satisfy the first-return recurrence. -/
lemma treePolynomial_succ (n : ℕ) :
    treePolynomial (n + 1) = ∑ i ∈ range (n + 1),
      (if i = 0 then X else treePolynomial i) * treePolynomial (n - i) := by
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (if i = 0 then (X : ℚ[X]) else treePolynomial i) * treePolynomial j)]
  unfold treePolynomial
  rw [BinaryTree.treesOfNumNodesEq_succ, sum_biUnion]
  · apply sum_congr rfl
    intro ij _
    have hsum :
        ∑ l ∈ BinaryTree.treesOfNumNodesEq ij.1,
          (if ij.1 = 0 then (X : ℚ[X]) else X ^ numPeaks (treePath l)) =
        if ij.1 = 0 then X else
          ∑ l ∈ BinaryTree.treesOfNumNodesEq ij.1, X ^ numPeaks (treePath l) := by
      split_ifs with hi
      · rw [hi]
        simp
      · rfl
    rw [← hsum, sum_mul_sum, BinaryTree.pairwiseNode, sum_map, sum_product]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro r _
    exact treeWeight_node hl r
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
    aesop

/-- Tree peaks and parts of noncrossing partitions have the same generating polynomial. -/
lemma treePolynomial_eq_blockPolynomial (n : ℕ) :
    treePolynomial n = blockPolynomial (range n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · simp only [treePolynomial_zero, range_zero, blockPolynomial_empty]
    · have hs : (range (n + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
      have hlt {x : ℕ} (hx : x ∈ range (n + 1)) {p : ℕ → Prop} [DecidablePred p]
          (hp : ¬p x) : #{y ∈ range (n + 1) | p y} < n + 1 := by
        simpa only [card_range] using card_lt_card (filter_ssubset.mpr ⟨x, hx, hp⟩)
      have hbridge (t : Finset ℕ) (ht : #t < n + 1) :
          blockPolynomial t = treePolynomial #t := by
        rw [ih #t ht]
        exact blockPolynomial_of_card_eq (by simp)
      symm
      calc
        _ = ∑ x ∈ range (n + 1),
            (if #{y ∈ range (n + 1) | y < x} = 0 then X else
              blockPolynomial {y ∈ range (n + 1) | y < x}) *
                blockPolynomial {y ∈ range (n + 1) | x < y} := blockPolynomial_eq_sum hs
        _ = ∑ x ∈ range (n + 1),
            (if #{y ∈ range (n + 1) | y < x} = 0 then X else
              treePolynomial #{y ∈ range (n + 1) | y < x}) *
                treePolynomial #{y ∈ range (n + 1) | x < y} := by
          apply sum_congr rfl
          intro x hx
          rw [hbridge {y ∈ range (n + 1) | y < x} (hlt hx (lt_irrefl x)),
            hbridge {y ∈ range (n + 1) | x < y} (hlt hx (lt_irrefl x))]
        _ = ∑ i ∈ range (n + 1),
            (if i = 0 then X else treePolynomial i) * treePolynomial (n - i) := by
          simpa only [card_range, Nat.add_sub_cancel] using
            sum_card_filter_lt_card_filter_gt (range (n + 1))
              (fun i j => (if i = 0 then (X : ℚ[X]) else treePolynomial i) * treePolynomial j)
        _ = _ := (treePolynomial_succ n).symm

/-- A coefficient of the tree polynomial counts paths with the given number of peaks. -/
lemma coeff_treePolynomial (n k : ℕ) :
    (treePolynomial n).coeff k =
      (#{t ∈ BinaryTree.treesOfNumNodesEq n | numPeaks (treePath t) = k} : ℚ) := by
  simp only [treePolynomial, finsetSum_coeff, coeff_X_pow, card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro t _
  split_ifs <;> simp_all

/-- A coefficient of the part polynomial counts partitions with that number of parts. -/
lemma coeff_blockPolynomial {α : Type*} [LinearOrder α] (s : Finset α) (k : ℕ) :
    (blockPolynomial s).coeff k = (#{P : NoncrossingPartition s | #P.1.parts = k} : ℚ) := by
  simp only [blockPolynomial, finsetSum_coeff, coeff_X_pow, card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro P _
  split_ifs <;> simp_all

/-- The paths of `n`-node trees with `k` peaks are counted by the Narayana number. -/
lemma card_treePath_peaks {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    #{t ∈ BinaryTree.treesOfNumNodesEq n | numPeaks (treePath t) = k} = narayana n k := by
  have h := congrArg (fun p : ℚ[X] => p.coeff k) (treePolynomial_eq_blockPolynomial n)
  rw [coeff_treePolynomial, coeff_blockPolynomial] at h
  have hc : #{t ∈ BinaryTree.treesOfNumNodesEq n | numPeaks (treePath t) = k} =
      #{P : NoncrossingPartition (range n) | #P.1.parts = k} := by exact_mod_cast h
  rw [hc]
  rcases k with _ | k
  · rw [NoncrossingPartition.card_filter_card_parts_eq_zero]
    simp [narayana, show n ≠ 0 by omega]
  · rw [NoncrossingPartition.card_parts_eq_div]
    simp [narayana]

/-- Unit-step paths to `(n, n)` above the diagonal are Dyck words of semilength `n`. -/
@[expose] def dyckEquiv (n : ℕ) :
    ↥({l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l}) ≃
      {p : DyckWord // p.semilength = n} where
  toFun l := ⟨ofLattice l.val (mem_filter.mp l.property).1 (mem_filter.mp l.property).2,
    semilength_ofLattice l.val _ _⟩
  invFun p := ⟨toLattice p.val, mem_filter.mpr
    ⟨by simpa only [p.property] using mem_latticePaths_toLattice p.val,
      staysWeaklyAboveDiagonal_toLattice p.val⟩⟩
  left_inv l := Subtype.ext (toLattice_ofLattice l.val
    (mem_filter.mp l.property).1 (mem_filter.mp l.property).2)
  right_inv p := by
    apply Subtype.ext
    apply DyckWord.ext
    simp only [ofLattice, toLattice, List.map_map]
    exact List.map_id'' readStep_step p.val.toList

/-- Unit-step paths to `(n, n)` above the diagonal correspond to `n`-node binary trees. -/
@[expose] def treeEquiv (n : ℕ) :
    ↥({l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l}) ≃
      ↥(BinaryTree.treesOfNumNodesEq n) :=
  (dyckEquiv n).trans (DyckWord.equivTreesOfNumNodesEq n)

/-- The tree corresponding to a lattice path recovers that path. -/
lemma treePath_treeEquiv (n : ℕ)
    (l : ↥({l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l})) :
    treePath (treeEquiv n l).val = l.val := by
  have he : (treeEquiv n l).val =
      (ofLattice l.val (mem_filter.mp l.property).1 (mem_filter.mp l.property).2).toTree := by
    simp only [treeEquiv, Equiv.trans_apply, DyckWord.equivTreesOfNumNodesEq,
      Equiv.subtypeEquiv_apply, DyckWord.equivTree_apply, dyckEquiv]
    rfl
  rw [he, treePath, DyckWord.ofTree_toTree]
  exact toLattice_ofLattice l.val _ _

/-- The path-tree correspondence preserves the number of peaks. -/
lemma card_latticePaths_peaks_eq_card_treePath_peaks (n k : ℕ) :
    #{l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l ∧ numPeaks l = k} =
      #{t ∈ BinaryTree.treesOfNumNodesEq n | numPeaks (treePath t) = k} := by
  rw [← filter_filter]
  apply card_bij (fun l hl =>
    (treeEquiv n ⟨l, (mem_filter.mp hl).1⟩).val)
  · intro l hl
    refine mem_filter.mpr ⟨(treeEquiv n ⟨l, (mem_filter.mp hl).1⟩).property, ?_⟩
    rw [treePath_treeEquiv]
    exact (mem_filter.mp hl).2
  · intro a ha b hb hab
    have he : treeEquiv n ⟨a, (mem_filter.mp ha).1⟩ =
        treeEquiv n ⟨b, (mem_filter.mp hb).1⟩ := Subtype.ext hab
    exact congrArg Subtype.val ((treeEquiv n).injective he)
  · intro t ht
    let l := (treeEquiv n).symm ⟨t, (mem_filter.mp ht).1⟩
    have he : treeEquiv n l = ⟨t, (mem_filter.mp ht).1⟩ := (treeEquiv n).apply_symm_apply _
    refine ⟨l.val, mem_filter.mpr ⟨l.property, ?_⟩, congrArg Subtype.val he⟩
    have hpath := treePath_treeEquiv n l
    rw [he] at hpath
    rw [← hpath]
    exact (mem_filter.mp ht).2

/-- The number of diagonal paths with `k` peaks is the Narayana number. -/
lemma card_latticePaths_peaks {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    #{l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l ∧ numPeaks l = k} =
      narayana n k := by
  rw [card_latticePaths_peaks_eq_card_treePath_peaks, card_treePath_peaks hn]

/-- The conversion from Dyck letters to lattice steps. -/
lemma step_def (s : DyckStep) : step s = if s = U then (0, 1) else (1, 0) := by
  cases s <;> rfl

/-- The conversion from lattice steps to Dyck letters. -/
lemma readStep_def (s : ℕ × ℕ) : readStep s = if s = (0, 1) then U else D := rfl

/-- The underlying step list of a converted Dyck word. -/
lemma toLattice_def (p : DyckWord) : toLattice p = p.toList.map step := rfl

/-- The word underlying a Dyck word constructed from a lattice path. -/
lemma ofLattice_toList {n : ℕ} (l : List (ℕ × ℕ)) (hl : l ∈ latticePaths unitSteps n n)
    (ha : StaysWeaklyAboveDiagonal l) : (ofLattice l hl ha).toList = l.map readStep := rfl

/-- The path of a tree is obtained through Mathlib's tree-to-Dyck correspondence. -/
lemma treePath_def (t : BinaryTree Unit) : treePath t = toLattice (DyckWord.ofTree t) := rfl

/-- The finite sum defining the noncrossing-partition polynomial. -/
lemma blockPolynomial_def {α : Type*} [LinearOrder α] (s : Finset α) :
    blockPolynomial s = ∑ P : NoncrossingPartition s, X ^ #P.1.parts := rfl

/-- The finite sum defining the tree polynomial. -/
lemma treePolynomial_def (n : ℕ) :
    treePolynomial n = ∑ t ∈ BinaryTree.treesOfNumNodesEq n, X ^ numPeaks (treePath t) := rfl

/-- The word obtained by the lattice-path-to-Dyck correspondence. -/
lemma dyckEquiv_apply (n : ℕ)
    (l : ↥({l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l})) :
    (dyckEquiv n l).val =
      ofLattice l.val (mem_filter.mp l.property).1 (mem_filter.mp l.property).2 := rfl

/-- The tree correspondence is the composition through Dyck words. -/
lemma treeEquiv_def (n : ℕ) :
    treeEquiv n = (dyckEquiv n).trans (DyckWord.equivTreesOfNumNodesEq n) := rfl

end NarayanaPaths
end DLMF.Combinatorics
