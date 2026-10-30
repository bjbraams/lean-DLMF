/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Notation and basic definitions (DLMF §§26.1–26.2)

DLMF 26.1.1 introduces the rising and falling factorials `x^{(n)} = x(x+1)⋯(x+n-1)` and
`x_{(n)} = x(x-1)⋯(x-n+1)`; these are Mathlib's `ascPochhammer` and `descPochhammer`
(evaluated at `x`). The other §26.2 notions are Mathlib's: a permutation of a finite set is an
`Equiv.Perm`, its cycles are `Equiv.Perm.cycleFactorsFinset` (with the cycle type, fixed points
included, in `Equiv.Perm.partition`), a partition of a finite set `S` is a `Finpartition S`,
and a partition of an integer `n` is a `Nat.Partition n` (the partition function `p(n)` is
`DLMF.Partitions.partitionFunction`).

Lattice paths (§26.2) have no Mathlib counterpart and are defined here. A lattice path from
`(0, 0)` to `(m, n)` with steps in a finite set `steps ⊆ ℕ × ℕ` is the list of its steps, a list
of elements of `steps` whose sum is `(m, n)`. Every step used in DLMF (`(1,0)`, `(0,1)`,
`(1,1)`, `(2,0)`, `(0,2)`) is nonzero, so such a path has at most `m + n` steps and
`latticePaths steps m n` is a finite set (`mem_latticePaths`). A path "stays on or above the
line `y = x`" when every vertex (every partial sum) does (`StaysWeaklyAboveDiagonal`); since the
segments are straight, this is the same as the whole path staying there. A `k`-dimensional
lattice path from the origin to `(n₁, …, n_k)` with unit steps is the word of its step
directions, a list over `Fin k` containing `i` exactly `nᵢ` times (`latticePathsFin`).
-/

@[expose] public section

open Finset

noncomputable section

namespace DLMF.Combinatorics

/-! ### Rising and falling factorials (§26.1) -/

/-- DLMF 26.1.1 (rising factorial): `x(x+1)⋯(x+n-1)` is `ascPochhammer` at `x`. -/
@[dlmf 26.1.E1]
theorem ascPochhammer_eval_eq_prod_range {R : Type*} [CommSemiring R] (n : ℕ) (x : R) :
    (ascPochhammer R n).eval x = ∏ j ∈ range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_right, ih, Finset.prod_range_succ]

/-- DLMF 26.1.1 (falling factorial): `x(x-1)⋯(x-n+1)` is `descPochhammer` at `x` (Mathlib
`descPochhammer_eval_eq_prod_range`). -/
@[dlmf 26.1.E1]
theorem descPochhammer_eval_eq_prod_range' {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    (descPochhammer R n).eval x = ∏ j ∈ range n, (x - j) :=
  descPochhammer_eval_eq_prod_range n x

/-! ### Lattice paths (§26.2) -/

/-- The lists of length `L` with entries in `steps`. -/
def stepLists (steps : Finset (ℕ × ℕ)) : ℕ → Finset (List (ℕ × ℕ))
  | 0 => {[]}
  | L + 1 => (steps ×ˢ stepLists steps L).image fun p => p.1 :: p.2

/-- Formula under the stated hypotheses: `l ∈ stepLists steps L ↔ l.length = L ∧ ∀ s ∈ l, s ∈
steps`. -/
theorem mem_stepLists {steps : Finset (ℕ × ℕ)} {L : ℕ} {l : List (ℕ × ℕ)} :
    l ∈ stepLists steps L ↔ l.length = L ∧ ∀ s ∈ l, s ∈ steps := by
  induction L generalizing l with
  | zero =>
    simp [stepLists, List.length_eq_zero_iff]
    rintro rfl; simp
  | succ L ih =>
    rcases l with _ | ⟨a, l⟩
    · simp [stepLists]
    · simp [stepLists, ih]; tauto

/-- DLMF §26.2: the lattice paths from `(0, 0)` to `(m, n)` whose steps lie in `steps`, each
path recorded as the list of its steps. Meaningful when every step is nonzero (as in all of
DLMF's uses); see `mem_latticePaths`. -/
@[dlmf 26.2]
def latticePaths (steps : Finset (ℕ × ℕ)) (m n : ℕ) : Finset (List (ℕ × ℕ)) :=
  ((range (m + n + 1)).biUnion (stepLists steps)).filter fun l => l.sum = (m, n)

/-- A list of nonzero steps has at most as many entries as the sum of the coordinates of its
endpoint. -/
lemma c26a_length_le_sum {l : List (ℕ × ℕ)} (h : ∀ s ∈ l, s ≠ (0, 0)) :
    l.length ≤ l.sum.1 + l.sum.2 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have ha : 1 ≤ a.1 + a.2 := by
      rcases a with ⟨a1, a2⟩
      by_contra hc
      exact h.1 (by simp only [Prod.mk.injEq]; omega)
    have := ih h.2
    simp only [List.length_cons, List.sum_cons, Prod.fst_add, Prod.snd_add]
    omega

/-- Membership in `latticePaths`: a list of steps from `steps` with endpoint `(m, n)`, when
`(0, 0)` is not a step. -/
theorem mem_latticePaths {steps : Finset (ℕ × ℕ)} (h0 : (0, 0) ∉ steps) {m n : ℕ}
    {l : List (ℕ × ℕ)} :
    l ∈ latticePaths steps m n ↔ (∀ s ∈ l, s ∈ steps) ∧ l.sum = (m, n) := by
  simp only [latticePaths, mem_filter, mem_biUnion, mem_range, mem_stepLists]
  constructor
  · rintro ⟨⟨L, _, _, hs⟩, hsum⟩; exact ⟨hs, hsum⟩
  · rintro ⟨hs, hsum⟩
    refine ⟨⟨l.length, ?_, rfl, hs⟩, hsum⟩
    have := c26a_length_le_sum fun s hs' => fun he => h0 (he ▸ hs s hs')
    rw [hsum] at this
    omega

/-- DLMF §26.2: the path (list of steps) stays on or above the line `y = x`: every vertex
`(x, y)` (partial sum of the steps) has `x ≤ y`. -/
@[dlmf 26.2]
def StaysWeaklyAboveDiagonal (l : List (ℕ × ℕ)) : Prop :=
  ∀ i ∈ range (l.length + 1), ((l.take i).sum).1 ≤ ((l.take i).sum).2

/-- The weak diagonal condition on a finite lattice path is decidable. -/
instance (l : List (ℕ × ℕ)) : Decidable (StaysWeaklyAboveDiagonal l) := by
  unfold StaysWeaklyAboveDiagonal; infer_instance

/-- The horizontal and vertical unit steps `(1, 0)`, `(0, 1)` of an ordinary lattice path
(DLMF §26.2). -/
def unitSteps : Finset (ℕ × ℕ) := {(1, 0), (0, 1)}

/-- DLMF §26.2: the `k`-dimensional lattice paths with unit steps from the origin to
`(n₀, …, n_{k-1})`, each recorded as the word of its step directions (a list over `Fin k`
containing `i` exactly `nᵢ` times). -/
@[dlmf 26.2]
def latticePathsFin {k : ℕ} (n : Fin k → ℕ) : Finset (List (Fin k)) :=
  ((univ : Finset (Fin (∑ i, n i) → Fin k)).image List.ofFn).filter fun l =>
    ∀ i, l.count i = n i

/-! ### Lattice path counting by the first step -/

/-- Decomposition of the lattice paths to `(m, n) ≠ (0, 0)` by their first step. -/
lemma q26a_latticePaths_eq_biUnion {steps : Finset (ℕ × ℕ)} (h0 : (0, 0) ∉ steps) {m n : ℕ}
    (hmn : (m, n) ≠ (0, 0)) :
    latticePaths steps m n = (steps.filter fun s => s.1 ≤ m ∧ s.2 ≤ n).biUnion fun s =>
      (latticePaths steps (m - s.1) (n - s.2)).map ⟨List.cons s, List.cons_injective⟩ := by
  ext l
  simp only [mem_latticePaths h0, mem_biUnion, mem_filter, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  rcases l with _ | ⟨s, l⟩
  · simp only [List.not_mem_nil, false_imp_iff, implies_true, List.sum_nil, true_and,
      reduceCtorEq, and_false, exists_false, iff_false]
    exact fun h => hmn h.symm
  · simp only [List.mem_cons, forall_eq_or_imp, List.sum_cons, List.cons.injEq]
    constructor
    · rintro ⟨⟨hs, hl⟩, hsum⟩
      refine ⟨s, ⟨hs, ?_, ?_⟩, l, ⟨hl, ?_⟩, rfl, rfl⟩
      · have := congrArg Prod.fst hsum; simp at this; omega
      · have := congrArg Prod.snd hsum; simp at this; omega
      · have h1 := congrArg Prod.fst hsum; have h2 := congrArg Prod.snd hsum
        simp at h1 h2; ext <;> simp <;> omega
    · rintro ⟨t, ⟨ht, h1, h2⟩, l', ⟨hl', hsum⟩, rfl, rfl⟩
      refine ⟨⟨ht, hl'⟩, ?_⟩
      ext <;> simp [hsum] <;> omega

/-- Counting lattice paths with a property by their first step. -/
theorem q26a_card_filter_latticePaths {steps : Finset (ℕ × ℕ)} (h0 : (0, 0) ∉ steps) {m n : ℕ}
    (hmn : (m, n) ≠ (0, 0)) (Q : List (ℕ × ℕ) → Prop) [DecidablePred Q] :
    #{l ∈ latticePaths steps m n | Q l} = ∑ s ∈ steps.filter (fun s => s.1 ≤ m ∧ s.2 ≤ n),
      #{l ∈ latticePaths steps (m - s.1) (n - s.2) | Q (s :: l)} := by
  rw [q26a_latticePaths_eq_biUnion h0 hmn, filter_biUnion, card_biUnion]
  · refine sum_congr rfl fun s _ => ?_
    rw [filter_map, card_map]
    rfl
  · intro s _ t _ hst
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨⟨a, _, rfl⟩, _⟩ := h1
    obtain ⟨⟨b, _, hb⟩, _⟩ := h2
    exact hst (List.cons.inj hb).1.symm

/-- The only lattice path to the origin is the empty path. -/
theorem q26a_latticePaths_zero {steps : Finset (ℕ × ℕ)} (h0 : (0, 0) ∉ steps) :
    latticePaths steps 0 0 = {[]} := by
  ext l
  rw [mem_latticePaths h0, mem_singleton]
  constructor
  · rintro ⟨hs, hsum⟩
    have := c26a_length_le_sum fun s hs' => fun he => h0 (he ▸ hs s hs')
    rw [hsum] at this
    exact List.eq_nil_of_length_eq_zero (by simpa using this)
  · rintro rfl; simp; rfl

/-- Every vertex `(x, y)` of the path satisfies `x ≤ y + d`. -/
def Q26aStaysAbove (d : ℤ) (l : List (ℕ × ℕ)) : Prop :=
  ∀ i ∈ range (l.length + 1), (((l.take i).sum).1 : ℤ) ≤ ((l.take i).sum).2 + d

/-- Decidability of `Q26aStaysAbove`. -/
instance (d : ℤ) (l : List (ℕ × ℕ)) : Decidable (Q26aStaysAbove d l) := by
  unfold Q26aStaysAbove; infer_instance

/-- With offset `0`, `Q26aStaysAbove` is `StaysWeaklyAboveDiagonal`. -/
theorem q26a_staysAbove_zero_iff (l : List (ℕ × ℕ)) :
    Q26aStaysAbove 0 l ↔ StaysWeaklyAboveDiagonal l := by
  simp only [Q26aStaysAbove, StaysWeaklyAboveDiagonal, add_zero, Nat.cast_le]

/-- The empty path stays in `x ≤ y + d` iff `0 ≤ d`. -/
lemma q26a_staysAbove_nil (d : ℤ) : Q26aStaysAbove d [] ↔ 0 ≤ d := by
  simp [Q26aStaysAbove]

/-- A path stays in `x ≤ y + d` iff the origin does and the rest stays in the shifted
half-plane. -/
lemma q26a_staysAbove_cons (d : ℤ) (s : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    Q26aStaysAbove d (s :: l) ↔ 0 ≤ d ∧ Q26aStaysAbove (d + s.2 - s.1) l := by
  simp only [Q26aStaysAbove, mem_range, List.length_cons]
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
    have := h (i + 1) (by omega)
    simp only [List.take_succ_cons, List.sum_cons, Prod.fst_add, Prod.snd_add] at this
    push_cast at this
    linarith
  · rintro ⟨hd, h⟩ i hi
    rcases i with _ | i
    · simpa using hd
    · have := h i (by omega)
      simp only [List.take_succ_cons, List.sum_cons, Prod.fst_add, Prod.snd_add]
      push_cast
      linarith

/-- The count of unit-step paths to `(m, n)` staying in `x ≤ y + d`. -/
def q26a_ballot (d : ℤ) (m n : ℕ) : ℕ := #{l ∈ latticePaths unitSteps m n | Q26aStaysAbove d l}

/-- No path stays in `x ≤ y + d` for `d < 0` (the origin fails). -/
lemma q26a_ballot_neg {d : ℤ} (hd : d < 0) (m n : ℕ) : q26a_ballot d m n = 0 := by
  rw [q26a_ballot, card_eq_zero, filter_eq_empty_iff]
  intro l _ h
  have := h 0 (by simp)
  simp at this; omega

/-- `(0, 0)` is not a unit step. -/
lemma q26a_unitSteps_h0 : (0, 0) ∉ unitSteps := by decide

/-- The empty path is counted when `0 ≤ d`. -/
lemma q26a_ballot_zero_zero {d : ℤ} (hd : 0 ≤ d) : q26a_ballot d 0 0 = 1 := by
  rw [q26a_ballot, q26a_latticePaths_zero q26a_unitSteps_h0]
  rw [filter_singleton]
  simp [(q26a_staysAbove_nil d).2 hd]

/-- First-step recurrence for `q26a_ballot`. -/
lemma q26a_ballot_step {d : ℤ} (hd : 0 ≤ d) {m n : ℕ} (hmn : (m, n) ≠ (0, 0)) :
    q26a_ballot d m n = ∑ s ∈ unitSteps.filter (fun s => s.1 ≤ m ∧ s.2 ≤ n),
      q26a_ballot (d + s.2 - s.1) (m - s.1) (n - s.2) := by
  rw [q26a_ballot, q26a_card_filter_latticePaths q26a_unitSteps_h0 hmn]
  refine sum_congr rfl fun s _ => ?_
  rw [q26a_ballot]
  congr 1
  refine filter_congr fun l _ => ?_
  rw [q26a_staysAbove_cons]
  simp [hd]

/-- `q26a_ballot` recurrence at `(m+1, n+1)`. -/
lemma q26a_ballot_succ_succ {d : ℤ} (hd : 0 ≤ d) (m n : ℕ) :
    q26a_ballot d (m + 1) (n + 1) =
      q26a_ballot (d - 1) m (n + 1) + q26a_ballot (d + 1) (m + 1) n := by
  rw [q26a_ballot_step hd (by simp), show unitSteps.filter (fun s => s.1 ≤ m + 1 ∧ s.2 ≤ n + 1)
      = unitSteps by
    ext ⟨a, b⟩; simp only [unitSteps, mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
    omega]
  have hp : ∀ f : ℕ × ℕ → ℕ, ∑ s ∈ unitSteps, f s = f (1, 0) + f (0, 1) :=
    fun f => sum_pair (by decide)
  rw [hp]
  simp only [Nat.cast_zero, Nat.cast_one, add_zero, Nat.add_sub_cancel, Nat.sub_zero,
    sub_zero]

/-- `q26a_ballot` recurrence at `(0, n+1)`. -/
lemma q26a_ballot_zero_succ {d : ℤ} (hd : 0 ≤ d) (n : ℕ) :
    q26a_ballot d 0 (n + 1) = q26a_ballot (d + 1) 0 n := by
  rw [q26a_ballot_step hd (by simp), show unitSteps.filter (fun s => s.1 ≤ 0 ∧ s.2 ≤ n + 1)
      = {(0, 1)} by
    ext ⟨a, b⟩; simp only [unitSteps, mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
    omega]
  simp

/-- `q26a_ballot` recurrence at `(m+1, 0)`. -/
lemma q26a_ballot_succ_zero {d : ℤ} (hd : 0 ≤ d) (m : ℕ) :
    q26a_ballot d (m + 1) 0 = q26a_ballot (d - 1) m 0 := by
  rw [q26a_ballot_step hd (by simp), show unitSteps.filter (fun s => s.1 ≤ m + 1 ∧ s.2 ≤ 0)
      = {(1, 0)} by
    ext ⟨a, b⟩; simp only [unitSteps, mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
    omega]
  simp

/-- The ballot (reflection) count: paths to `(m, n)` staying in `x ≤ y + d`, `m ≤ n + d`. -/
theorem q26a_ballot_eq (N : ℕ) : ∀ (d m n : ℕ), m + n = N → m ≤ n + d →
    (q26a_ballot d m n : ℤ) =
      (m + n).choose n - if d < m then ((m + n).choose (m - d - 1) : ℤ) else 0 := by
  induction N with
  | zero =>
    intro d m n h _
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
    simp [q26a_ballot_zero_zero (Int.natCast_nonneg d)]
  | succ N ih =>
    intro d m n h hle
    rcases m with _ | m
    · rcases n with _ | n
      · omega
      rw [q26a_ballot_zero_succ (Int.natCast_nonneg d),
        show (d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) by push_cast; ring,
        ih (d + 1) 0 n (by omega) (by omega)]
      simp
    rcases n with _ | n
    · obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [q26a_ballot_succ_zero (Int.natCast_nonneg _),
        show ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) by push_cast; ring,
        ih d m 0 (by omega) (by omega)]
      simp [show ¬ d + 1 < m + 1 by omega, show ¬ d < m by omega]
    rw [q26a_ballot_succ_succ (Int.natCast_nonneg _)]
    push_cast
    rcases d with _ | d
    · rw [q26a_ballot_neg (by norm_num), show ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num,
        ih 1 (m + 1) n (by omega) (by omega)]
      rw [show m + 1 + (n + 1) = (m + 1 + n) + 1 by ring]
      rcases m with _ | m
      · simp only [Nat.cast_zero, zero_add, lt_self_iff_false, ite_false, sub_zero,
          show 0 < 0 + 1 by omega, ite_true, Nat.sub_self, Nat.choose_zero_right]
        rw [show 0 + 1 + n = n + 1 by ring, Nat.choose_succ_self_right,
          Nat.choose_succ_self_right]
        push_cast; ring
      · simp only [Nat.cast_zero, zero_add, show 1 < m + 1 + 1 by omega,
          show 0 < m + 1 + 1 by omega, ite_true, Nat.add_sub_cancel, Nat.sub_zero]
        have s1 : (m + 1 + 1 + n).choose (n + 1) = (m + 1 + 1 + n).choose (m + 1) := by
          rw [← Nat.choose_symm (by omega)]; congr 1; omega
        rw [Nat.choose_succ_succ' (m + 1 + 1 + n) n, Nat.choose_succ_succ' (m + 1 + 1 + n) m, s1]
        push_cast; ring
    · rw [show ((d + 1 : ℕ) : ℤ) - 1 = ((d : ℕ) : ℤ) by push_cast; ring,
        show ((d + 1 : ℕ) : ℤ) + 1 = ((d + 2 : ℕ) : ℤ) by push_cast; ring,
        ih d m (n + 1) (by omega) (by omega), ih (d + 2) (m + 1) n (by omega) (by omega)]
      rw [show m + 1 + (n + 1) = (m + n + 1) + 1 by ring, show m + (n + 1) = m + n + 1 by ring,
        show m + 1 + n = m + n + 1 by ring, Nat.choose_succ_succ' (m + n + 1) n]
      by_cases hdm : d < m
      · obtain ⟨e, rfl⟩ : ∃ e, m = d + 1 + e := ⟨m - d - 1, by omega⟩
        simp only [hdm, show d + 1 < d + 1 + e + 1 by omega, ite_true]
        rw [show d + 1 + e - d - 1 = e by omega, show d + 1 + e + 1 - (d + 1) - 1 = e by omega]
        rcases e with _ | e
        · simp only [show ¬ d + 2 < d + 1 + 0 + 1 by omega, ite_false, Nat.choose_zero_right]
          push_cast; ring
        · simp only [show d + 2 < d + 1 + (e + 1) + 1 by omega, ite_true,
            show d + 1 + (e + 1) + 1 - (d + 2) - 1 = e by omega, Nat.choose_succ_succ']
          push_cast; ring
      · simp only [hdm, show ¬ d + 1 < m + 1 by omega, show ¬ d + 2 < m + 1 by omega, ite_false]
        push_cast; ring

end DLMF.Combinatorics
