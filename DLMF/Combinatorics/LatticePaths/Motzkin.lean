/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic
public import TauCeti.Combinatorics.PlanarMatching.HalfDiagram

/-!
# Motzkin paths and ballot counts

The paths with steps `(2, 0)`, `(0, 2)`, `(1, 1)` that stay above the diagonal are Motzkin
walks after a linear change of coordinates. Their count is the binomial transform of the
ballot counts `TauCeti.halfCount`. The recurrence of that transform agrees with the
first-step recurrence of lattice paths, including boundary and empty cases.

The proof reuses TauCeti's proved half-diagram ballot recurrence and its Catalan count,
without copying their proofs. At height zero, only even ballot lengths contribute.

## Main results

* `MotzkinPaths.latticeCount_eq_count`: the finite lattice-path enumeration.
* `MotzkinPaths.count_zero_eq_sum`: its Catalan-binomial specialization.
-/

public noncomputable section

open Finset

namespace DLMF.Combinatorics.MotzkinPaths

/-- The binomial transform of the ballot counts, allowing horizontal Motzkin steps. -/
@[expose] def count (n d : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), n.choose k * TauCeti.halfCount k d

/-- The defining sum of the ballot transform. -/
lemma count_def (n d : ℕ) :
    count n d = ∑ k ∈ range (n + 1), n.choose k * TauCeti.halfCount k d := rfl

/-- There is no Motzkin walk with more initial height than steps. -/
lemma count_of_lt {n d : ℕ} (h : n < d) : count n d = 0 := by
  apply sum_eq_zero
  intro k hk
  rw [TauCeti.halfCount_eq_zero_of_lt (by simp only [mem_range] at hk; omega), mul_zero]

/-- The empty walk can start and end at zero only. -/
lemma count_zero (d : ℕ) : count 0 d = if d = 0 then 1 else 0 := by
  cases d <;> simp [count]

/-- Pascal's identity separates an initial horizontal step from an initial nonhorizontal step. -/
lemma count_succ (n d : ℕ) :
    count (n + 1) d = count n d +
      ∑ k ∈ range (n + 1), n.choose k * TauCeti.halfCount (k + 1) d := by
  unfold count
  rw [sum_range_succ']
  simp only [Nat.choose_zero_right, one_mul]
  have h : ∀ k : ℕ, (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) :=
    fun k => Nat.choose_succ_succ n k
  simp_rw [h, add_mul]
  rw [sum_add_distrib]
  have hs : ∑ k ∈ range (n + 1), n.choose (k + 1) * TauCeti.halfCount (k + 1) d =
      ∑ k ∈ range n, n.choose (k + 1) * TauCeti.halfCount (k + 1) d := by
    rw [sum_range_succ]
    simp
  rw [hs, sum_range_succ' (fun k => n.choose k * TauCeti.halfCount k d) n]
  simp only [Nat.choose_zero_right, one_mul]
  omega

/-- A walk starting at height zero begins with a horizontal or an upward step. -/
lemma count_succ_zero (n : ℕ) : count (n + 1) 0 = count n 0 + count n 1 := by
  rw [count_succ]
  simp_rw [TauCeti.halfCount_succ_zero]
  rfl

/-- A walk starting at positive height has three possible initial steps. -/
lemma count_succ_succ (n d : ℕ) :
    count (n + 1) (d + 1) = count n (d + 1) + count n d + count n (d + 2) := by
  rw [count_succ]
  simp_rw [TauCeti.halfCount_succ_succ, mul_add]
  rw [sum_add_distrib]
  exact (add_assoc _ _ _).symm

/-- A walk with initial height equal to its length consists only of downward steps. -/
lemma count_self (n : ℕ) : count n n = 1 := by
  unfold count
  rw [sum_eq_single n]
  · simp
  · intro k hk hkn
    rw [TauCeti.halfCount_eq_zero_of_lt (by simp only [mem_range] at hk; omega), mul_zero]
  · simp

/-- The number of paths with steps `(2, 0)`, `(0, 2)`, `(1, 1)` staying in `x ≤ y + 2d`. -/
@[expose] def latticeCount (d : ℤ) (m n : ℕ) : ℕ :=
  #{l ∈ latticePaths {(2, 0), (0, 2), (1, 1)} m n | StaysAbove (2 * d) l}

/-- The defining filtered lattice-path count. -/
lemma latticeCount_def (d : ℤ) (m n : ℕ) :
    latticeCount d m n =
      #{l ∈ latticePaths {(2, 0), (0, 2), (1, 1)} m n | StaysAbove (2 * d) l} := rfl

/-- No path can start below the permitted half-plane. -/
lemma latticeCount_of_neg {d : ℤ} (hd : d < 0) (m n : ℕ) :
    latticeCount d m n = 0 := by
  rw [latticeCount, card_eq_zero, filter_eq_empty_iff]
  intro l _ h
  have := h 0 (by simp)
  simp at this
  omega

/-- The empty path is the unique path to the origin in the permitted half-plane. -/
lemma latticeCount_zero_zero {d : ℤ} (hd : 0 ≤ d) : latticeCount d 0 0 = 1 := by
  rw [latticeCount, latticePaths_zero_zero (by decide), filter_singleton]
  have h : StaysAbove (2 * d) [] := by simp only [StaysAbove]; simp; omega
  simp [h]

/-- Counting Motzkin paths by their first step gives the three allowed predecessor counts. -/
lemma latticeCount_eq_sum {d : ℤ} (hd : 0 ≤ d) {m n : ℕ} (hmn : (m, n) ≠ (0, 0)) :
    latticeCount d m n =
      (if 2 ≤ m then latticeCount (d - 1) (m - 2) n else 0) +
      (if 2 ≤ n then latticeCount (d + 1) m (n - 2) else 0) +
      (if 1 ≤ m ∧ 1 ≤ n then latticeCount d (m - 1) (n - 1) else 0) := by
  unfold latticeCount
  rw [card_filter_latticePaths (by decide) hmn, sum_filter]
  have heq (s : ℕ × ℕ) :
      #{l ∈ latticePaths {(2, 0), (0, 2), (1, 1)} (m - s.1) (n - s.2) |
        StaysAbove (2 * d) (s :: l)} =
      #{l ∈ latticePaths {(2, 0), (0, 2), (1, 1)} (m - s.1) (n - s.2) |
        StaysAbove (2 * d + s.2 - s.1) l} := by
    congr 1
    apply filter_congr
    intro l _
    rw [staysAbove_cons]
    simp only [show 0 ≤ 2 * d by omega, true_and]
  simp_rw [heq]
  rw [sum_insert (by decide), sum_pair (by decide)]
  simp only [Nat.zero_le, and_true, true_and, Nat.sub_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  have e1 : 2 * d + 0 - 2 = 2 * (d - 1) := by ring
  have e2 : 2 * d + 2 - 0 = 2 * (d + 1) := by ring
  have e3 : 2 * d + 1 - 1 = 2 * d := by ring
  simp only [e1, e2, e3]
  omega

/-- A Motzkin path with given length and initial height is counted by the ballot transform. -/
lemma latticeCount_eq_count (n : ℕ) : ∀ d : ℕ, d ≤ n →
    latticeCount d (n + d) (n - d) = count n d := by
  induction n with
  | zero =>
    intro d hd
    obtain rfl : d = 0 := by omega
    simp [latticeCount_zero_zero, count_zero]
  | succ n ih =>
    intro d hd
    rcases d with _ | d
    · rw [Nat.cast_zero, add_zero, Nat.sub_zero,
        latticeCount_eq_sum (by norm_num) (by simp), count_succ_zero]
      simp only [zero_sub, zero_add, latticeCount_of_neg (by norm_num : (-1 : ℤ) < 0),
        ite_self, zero_add]
      by_cases hn : 1 ≤ n
      · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
        have h1 := ih 1 hn
        have h0 := ih 0 (by omega)
        simp only [Nat.cast_one, Nat.cast_zero, add_zero, Nat.sub_zero] at h1 h0
        rw [show n + 1 - 2 = n - 1 by omega, Nat.add_sub_cancel, h1, h0]
        omega
      · obtain rfl : n = 0 := by omega
        norm_num [latticeCount_zero_zero, count_zero]
    · have hd' : d ≤ n := by omega
      rw [latticeCount_eq_sum (Int.natCast_nonneg _) (by simp)]
      have e1 : ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) := by push_cast; ring
      have e2 : ((d + 1 : ℕ) : ℤ) + 1 = ((d + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, ite_eq_left (by omega)]
      by_cases he : d = n
      · subst d
        rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero]
        rw [show n + 1 + (n + 1) - 2 = n + n by omega,
          show n + 1 - (n + 1) = n - n by omega, ih n le_rfl, count_self, count_self]
      · have hd'' : d + 1 ≤ n := by omega
        rw [ite_eq_left (show 1 ≤ n + 1 + (d + 1) ∧ 1 ≤ n + 1 - (d + 1) by omega)]
        rw [show n + 1 + (d + 1) - 2 = n + d by omega,
          show n + 1 - (d + 1) = n - d by omega, ih d hd']
        rw [show n + 1 + (d + 1) - 1 = n + (d + 1) by omega,
          show n - d - 1 = n - (d + 1) by omega, ih (d + 1) hd'']
        rw [count_succ_succ]
        by_cases h2 : d + 2 ≤ n
        · rw [ite_eq_left (show 2 ≤ n - d by omega), show n + 1 + (d + 1) = n + (d + 2) by omega,
            show n - d - 2 = n - (d + 2) by omega, ih (d + 2) h2]
          omega
        · rw [ite_eq_right (show ¬2 ≤ n - d by omega), count_of_lt (by omega : n < d + 2)]
          omega

/-- The zero-height ballot transform is the Catalan-binomial formula. -/
lemma count_zero_eq_sum (n : ℕ) :
    count n 0 = ∑ k ∈ range (n + 1), catalan k * n.choose (2 * k) := by
  unfold count
  refine sum_bij_ne_zero (fun k _ _ => k / 2) ?_ ?_ ?_ ?_
  · intro k hk hne
    simp only [mem_range] at hk ⊢
    omega
  · intro a _ hna b _ hnb heq
    have hpa : ¬Odd a := by
      intro h
      rw [TauCeti.halfCount_eq_zero_of_odd (by simpa using h), mul_zero] at hna
      exact hna rfl
    have hpb : ¬Odd b := by
      intro h
      rw [TauCeti.halfCount_eq_zero_of_odd (by simpa using h), mul_zero] at hnb
      exact hnb rfl
    simp only [Nat.odd_iff] at hpa hpb
    omega
  · intro k _ hne
    have hkn : 2 * k ≤ n := by
      by_contra h
      rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero] at hne
      exact hne rfl
    refine ⟨2 * k, mem_range.mpr (by omega), ?_, by omega⟩
    rw [TauCeti.halfCount_two_mul_zero]
    exact (mul_comm _ _).trans_ne hne
  · intro k _ hne
    have hp : ¬Odd k := by
      intro h
      rw [TauCeti.halfCount_eq_zero_of_odd (by simpa using h), mul_zero] at hne
      exact hne rfl
    have he : 2 * (k / 2) = k := by simp only [Nat.odd_iff] at hp; omega
    rw [← he, TauCeti.halfCount_two_mul_zero]
    simp only [Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    ring

end DLMF.Combinatorics.MotzkinPaths
