/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Permutations.RookPolynomials

/-!
# Menage numbers and Ferrers-board rook numbers

Inclusion-exclusion for menage numbers and the column recurrence for rook numbers of Ferrers
boards.

Source references and common attribution are retained in
`DLMF.Combinatorics.Permutations`.
-/

@[expose] public section

noncomputable section

open Finset Equiv

open Polynomial hiding bernoulli

namespace DLMF.Combinatorics

/-! ### Helpers for the ménage numbers (26.15.9)

The `2n` squares of the ménage board are arranged in a cycle `(0,0), (0,1), (1,1), (1,2), …`
in which two squares attack each other exactly when they are cyclically adjacent, so
`r_k` counts `k`-subsets of a `2n`-cycle without two adjacent elements. -/

section MenageHelpers

open Fin.NatCast

/-- `k`-subsets of `range M` without two consecutive elements. -/
def s26b_P (M k : ℕ) : ℕ := #{S ∈ (range M).powersetCard k | ∀ i ∈ S, i + 1 ∉ S}

/-- Identity under the stated parameter and domain assumptions: `s26b_P M 0 = 1`. -/
lemma s26b_P_zero_right (M : ℕ) : s26b_P M 0 = 1 := by
  rw [s26b_P, powersetCard_zero, filter_true_of_mem (by simp), card_singleton]

/-- Identity under the stated parameter and domain assumptions: `s26b_P (M + 2) (k + 1) = s26b_P
(M + 1) (k + 1) + s26b_P M k`. -/
lemma s26b_P_succ_succ (M k : ℕ) :
    s26b_P (M + 2) (k + 1) = s26b_P (M + 1) (k + 1) + s26b_P M k := by
  rw [s26b_P, ← card_filter_add_card_filter_not (p := fun S => M + 1 ∉ S)]
  congr 1
  · rw [filter_filter, s26b_P]
    congr 1
    ext S
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hS, hc⟩, hn, h⟩
      refine ⟨⟨fun x hx => ?_, hc⟩, hn⟩
      have := mem_range.mp (hS hx)
      have : x ≠ M + 1 := fun h' => h (h' ▸ hx)
      exact mem_range.mpr (by omega)
    · rintro ⟨⟨hS, hc⟩, hn⟩
      exact ⟨⟨hS.trans (range_subset_range.mpr (by omega)), hc⟩, hn, fun h =>
        by have := mem_range.mp (hS h); omega⟩
  · rw [filter_filter, s26b_P]
    refine card_nbij' (fun S => S.erase (M + 1)) (fun S => insert (M + 1) S) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_coe, mem_filter, mem_powersetCard, not_not] at hS ⊢
      obtain ⟨⟨hS, hc⟩, hn, hM⟩ := hS
      refine ⟨⟨fun x hx => ?_, by rw [card_erase_of_mem hM, hc]; rfl⟩, fun i hi h => ?_⟩
      · obtain ⟨hne, hx⟩ := mem_erase.mp hx
        have := mem_range.mp (hS hx)
        have : x ≠ M := fun h' => hn x hx (h' ▸ hM)
        exact mem_range.mpr (by omega)
      · exact hn i (mem_erase.mp hi).2 (mem_erase.mp h).2
    · intro S hS
      simp only [mem_coe, mem_filter, mem_powersetCard, not_not] at hS ⊢
      obtain ⟨⟨hS, hc⟩, hn⟩ := hS
      have hM : M + 1 ∉ S := fun h => by have := mem_range.mp (hS h); omega
      refine ⟨⟨fun x hx => ?_, by rw [card_insert_of_notMem hM, hc]⟩, fun i hi h => ?_,
        mem_insert_self _ _⟩
      · rcases mem_insert.mp hx with rfl | hx
        · exact mem_range.mpr (by omega)
        · have := mem_range.mp (hS hx); exact mem_range.mpr (by omega)
      · rcases mem_insert.mp hi with rfl | hi
        · rcases mem_insert.mp h with h | h
          · omega
          · have := mem_range.mp (hS h); omega
        · rcases mem_insert.mp h with h | h
          · have := mem_range.mp (hS hi); omega
          · exact hn i hi h
    · intro S hS
      simp only [mem_coe, mem_filter, not_not] at hS
      exact insert_erase hS.2.2
    · intro S hS
      simp only [mem_coe, mem_filter, mem_powersetCard] at hS
      have hM : M + 1 ∉ S := fun h => by have := mem_range.mp (hS.1.1 h); omega
      exact erase_insert hM

/-- Identity under the stated parameter and domain assumptions: `s26b_P 0 (k + 1) = 0`. -/
lemma s26b_P_zero_succ (k : ℕ) : s26b_P 0 (k + 1) = 0 := by
  simp [s26b_P]

/-- Identity under the stated parameter and domain assumptions: `s26b_P 1 (k + 2) = 0`. -/
lemma s26b_P_one_succ_succ (k : ℕ) : s26b_P 1 (k + 2) = 0 := by
  rw [s26b_P, powersetCard_eq_empty.mpr (by simp)]
  rfl

/-- Identity under the stated parameter and domain assumptions: `s26b_P 1 1 = 1`. -/
lemma s26b_P_one_one : s26b_P 1 1 = 1 := by decide

/-- Identity under the stated parameter and domain assumptions: `s26b_P M k = (M + 1 - k).choose
k`. -/
lemma s26b_P_eq (M k : ℕ) : s26b_P M k = (M + 1 - k).choose k := by
  induction M using Nat.strong_induction_on generalizing k with
  | _ M ih =>
    rcases k with _ | k
    · simp [s26b_P_zero_right]
    rcases M with _ | _ | M
    · rw [s26b_P_zero_succ]; simp
    · rcases k with _ | k
      · rw [s26b_P_one_one]; rfl
      · rw [s26b_P_one_succ_succ]; simp
    · rw [s26b_P_succ_succ, ih (M + 1) (by omega), ih M (by omega)]
      rcases Nat.lt_or_ge (M + 1) k with hk | hk
      · rw [show M + 1 + 1 - (k + 1) = 0 by omega, show M + 1 - k = 0 by omega,
          show M + 2 + 1 - (k + 1) = 0 by omega]
        simp [Nat.choose_eq_zero_of_lt (show 0 < k by omega)]
      · rw [show M + 1 + 1 - (k + 1) = M + 1 - k by omega,
          show M + 2 + 1 - (k + 1) = (M + 1 - k) + 1 by omega, Nat.choose_succ_succ', add_comm]

/-- Formula under the stated hypotheses: `#{S ∈ (Ico a (a + M)).powersetCard k | ∀ i ∈ S, i + 1 ∉
S} = s26b_P M k`. -/
lemma s26b_P_shift (a M k : ℕ) :
    #{S ∈ (Ico a (a + M)).powersetCard k | ∀ i ∈ S, i + 1 ∉ S} = s26b_P M k := by
  rw [s26b_P]
  symm
  refine card_nbij' (fun T => T.image (· + a)) (fun S => S.image (· - a)) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [mem_coe, mem_filter, mem_powersetCard] at hT ⊢
    obtain ⟨⟨hT, hc⟩, hn⟩ := hT
    refine ⟨⟨fun x hx => ?_, ?_⟩, fun i hi h => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      have := mem_range.mp (hT hy); exact mem_Ico.mpr (by omega)
    · rw [card_image_of_injective _ (add_left_injective a), hc]
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hi
      obtain ⟨z, hz, hz'⟩ := mem_image.mp h
      exact hn y hy (by rwa [show y + 1 = z by omega])
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard] at hS ⊢
    obtain ⟨⟨hS, hc⟩, hn⟩ := hS
    have hinj : Set.InjOn (· - a) (S : Set ℕ) := by
      intro x hx y hy h
      have := mem_Ico.mp (hS hx); have := mem_Ico.mp (hS hy); simp only at h; omega
    refine ⟨⟨fun x hx => ?_, ?_⟩, fun i hi h => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      have := mem_Ico.mp (hS hy); exact mem_range.mpr (by omega)
    · rw [card_image_of_injOn hinj, hc]
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hi
      obtain ⟨z, hz, hz'⟩ := mem_image.mp h
      have := mem_Ico.mp (hS hy); have := mem_Ico.mp (hS hz)
      exact hn y hy (by rwa [show y + 1 = z by omega])
  · intro T _
    simp [image_image, Function.comp_def]
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard] at hS
    dsimp only
    rw [image_image]
    conv_rhs => rw [← image_id (s := S)]
    refine image_congr fun x hx => ?_
    have := mem_Ico.mp (hS.1.1 hx); simp only [Function.comp_apply, id]; omega

/-- `k`-subsets of `range N` without two cyclically consecutive elements. -/
def s26b_Q (N k : ℕ) : ℕ := #{S ∈ (range N).powersetCard k | ∀ i ∈ S, (i + 1) % N ∉ S}

/-- Identity under the stated parameter and domain assumptions: `s26b_Q N 0 = 1`. -/
lemma s26b_Q_zero (N : ℕ) : s26b_Q N 0 = 1 := by
  rw [s26b_Q, powersetCard_zero, filter_true_of_mem (by simp), card_singleton]

/-- Identity under the stated parameter and domain assumptions: `s26b_Q N (k + 1) = s26b_P (N - 1)
(k + 1) + s26b_P (N - 3) k`. -/
lemma s26b_Q_succ {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    s26b_Q N (k + 1) = s26b_P (N - 1) (k + 1) + s26b_P (N - 3) k := by
  rw [s26b_Q, ← card_filter_add_card_filter_not (p := fun S => 0 ∉ S), filter_filter,
    filter_filter, ← s26b_P_shift 1, ← s26b_P_shift 2]
  congr 1
  · congr 1
    ext S
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hS, hc⟩, hn, h0⟩
      have hS' : S ⊆ Ico 1 (1 + (N - 1)) := fun x hx => by
        have := mem_range.mp (hS hx)
        have : x ≠ 0 := fun h => h0 (h ▸ hx)
        exact mem_Ico.mpr (by omega)
      refine ⟨⟨hS', hc⟩, fun i hi h => ?_⟩
      have := mem_Ico.mp (hS' hi); have := mem_Ico.mp (hS' h)
      exact hn i hi (by rwa [Nat.mod_eq_of_lt (by omega)])
    · rintro ⟨⟨hS, hc⟩, hn⟩
      refine ⟨⟨fun x hx => by have := mem_Ico.mp (hS hx); exact mem_range.mpr (by omega), hc⟩,
        fun i hi h => ?_, fun h => by have := mem_Ico.mp (hS h); omega⟩
      have := mem_Ico.mp (hS hi)
      rcases Nat.lt_or_ge (i + 1) N with hl | hl
      · rw [Nat.mod_eq_of_lt hl] at h; exact hn i hi h
      · rw [show i + 1 = N by omega, Nat.mod_self] at h
        have := mem_Ico.mp (hS h); omega
  · refine card_nbij' (fun S => S.erase 0) (fun S => insert 0 S) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_coe, mem_filter, mem_powersetCard, not_not] at hS ⊢
      obtain ⟨⟨hS, hc⟩, hn, h0⟩ := hS
      have h1 : 1 ∉ S := fun h => hn 0 h0 (by rwa [Nat.mod_eq_of_lt (by omega)])
      have hl : N - 1 ∉ S := fun h => hn (N - 1) h (by rwa [show N - 1 + 1 = N by omega,
        Nat.mod_self])
      have hS' : S.erase 0 ⊆ Ico 2 (2 + (N - 3)) := fun x hx => by
        obtain ⟨hx0, hx⟩ := mem_erase.mp hx
        have := mem_range.mp (hS hx)
        have : x ≠ 1 := fun h => h1 (h ▸ hx)
        have : x ≠ N - 1 := fun h => hl (h ▸ hx)
        exact mem_Ico.mpr (by omega)
      refine ⟨⟨hS', by rw [card_erase_of_mem h0, hc]; rfl⟩, fun i hi h => ?_⟩
      have := mem_Ico.mp (hS' hi); have := mem_Ico.mp (hS' h)
      exact hn i (mem_erase.mp hi).2 (by rw [Nat.mod_eq_of_lt (by omega)]; exact (mem_erase.mp h).2)
    · intro S hS
      simp only [mem_coe, mem_filter, mem_powersetCard, not_not] at hS ⊢
      obtain ⟨⟨hS, hc⟩, hn⟩ := hS
      have h0 : 0 ∉ S := fun h => by have := mem_Ico.mp (hS h); omega
      refine ⟨⟨fun x hx => ?_, by rw [card_insert_of_notMem h0, hc]⟩, fun i hi h => ?_,
        mem_insert_self _ _⟩
      · rcases mem_insert.mp hx with rfl | hx
        · exact mem_range.mpr (by omega)
        · have := mem_Ico.mp (hS hx); exact mem_range.mpr (by omega)
      · rcases mem_insert.mp hi with rfl | hi
        · rw [Nat.mod_eq_of_lt (by omega)] at h
          rcases mem_insert.mp h with h | h
          · omega
          · have := mem_Ico.mp (hS h); omega
        · have := mem_Ico.mp (hS hi)
          rw [Nat.mod_eq_of_lt (by omega)] at h
          rcases mem_insert.mp h with h | h
          · omega
          · exact hn i hi h
    · intro S hS
      simp only [mem_coe, mem_filter, not_not] at hS
      exact insert_erase hS.2.2
    · intro S hS
      simp only [mem_coe, mem_filter, mem_powersetCard] at hS
      have h0 : 0 ∉ S := fun h => by have := mem_Ico.mp (hS.1.1 h); omega
      exact erase_insert h0

/-- Identity under the stated parameter and domain assumptions: `(s26b_Q (2 * n) k : ℚ) = 2 * n /
(2 * n - k) * (2 * n - k).choose k`. -/
lemma s26b_Q_formula {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : k ≤ n) :
    (s26b_Q (2 * n) k : ℚ) = 2 * n / (2 * n - k) * (2 * n - k).choose k := by
  rcases k with _ | k
  · rw [s26b_Q_zero]; have : (2 * n : ℚ) ≠ 0 := by positivity
    simp [this]
  rw [s26b_Q_succ (by omega), s26b_P_eq, s26b_P_eq]
  obtain ⟨M, hM⟩ : ∃ M, 2 * n = M + k + 2 := ⟨2 * n - k - 2, by omega⟩
  rw [show 2 * n - 1 + 1 - (k + 1) = M + 1 by omega, show 2 * n - 3 + 1 - k = M by omega,
    show 2 * n - (k + 1) = M + 1 by omega]
  have h := Nat.add_one_mul_choose_eq M k
  have hq : ((M + 1 : ℕ) : ℚ) * (M.choose k) = ((M + 1).choose (k + 1)) * (k + 1 : ℕ) := by
    exact_mod_cast h
  have h2 : (2 * n : ℚ) = M + k + 2 := by exact_mod_cast hM
  have h3 : (2 * n : ℚ) - ((k + 1 : ℕ) : ℚ) = M + 1 := by push_cast; linarith
  rw [h3, h2]
  have : (M + 1 : ℚ) ≠ 0 := by positivity
  push_cast at hq ⊢
  field_simp
  linear_combination hq

/-- The `m`-th square of the ménage board in cyclic order: `ψ (2i) = (i, i)`,
`ψ (2i + 1) = (i, i + 1)`. -/
def s26b_ψ (n : ℕ) [NeZero n] (m : ℕ) : Fin n × Fin n :=
  (((m / 2 : ℕ) : Fin n), (((m + 1) / 2 : ℕ) : Fin n))

/-- Identity under the stated parameter and domain assumptions: `((x : Fin n) = (y : Fin n)) ↔ x =
y ∨ (x = 0 ∧ y = n) ∨ (x = n ∧ y = 0)`. -/
lemma s26b_cast_eq_iff {n : ℕ} [NeZero n] {x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) :
    ((x : Fin n) = (y : Fin n)) ↔ x = y ∨ (x = 0 ∧ y = n) ∨ (x = n ∧ y = 0) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [Fin.ext_iff, Fin.val_natCast, Fin.val_natCast]
  rcases hx.lt_or_eq with hx | rfl <;> rcases hy.lt_or_eq with hy | rfl
  · rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]; omega
  · rw [Nat.mod_eq_of_lt hx, Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt hy, Nat.mod_self]; omega
  · simp

/-- Identity under the stated parameter and domain assumptions: `(range (2 * n)).image (s26b_ψ n)
= menageBoard n`. -/
lemma s26b_image_ψ {n : ℕ} [NeZero n] : (range (2 * n)).image (s26b_ψ n) = menageBoard n := by
  ext ⟨i, j⟩
  simp only [mem_image, mem_range, menageBoard, mem_union, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨m, hm, h⟩
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' m
    · left; refine ⟨(a : Fin n), ?_⟩
      simp only [s26b_ψ, Prod.mk.injEq] at h
      rw [show 2 * a / 2 = a by omega, show (2 * a + 1) / 2 = a by omega] at h
      exact ⟨h.1, h.2⟩
    · right; refine ⟨(a : Fin n), ?_⟩
      simp only [s26b_ψ, Prod.mk.injEq] at h
      rw [show (2 * a + 1) / 2 = a by omega, show (2 * a + 1 + 1) / 2 = a + 1 by omega,
        Nat.cast_succ] at h
      exact ⟨h.1, h.2⟩
  · rintro (⟨a, ha, hb⟩ | ⟨a, ha, hb⟩)
    · refine ⟨2 * a.val, by omega, ?_⟩
      simp only [s26b_ψ, Prod.mk.injEq]
      rw [show 2 * a.val / 2 = a.val by omega, show (2 * a.val + 1) / 2 = a.val by omega,
        Fin.cast_val_eq_self]
      exact ⟨ha, hb⟩
    · refine ⟨2 * a.val + 1, by omega, ?_⟩
      simp only [s26b_ψ, Prod.mk.injEq]
      rw [show (2 * a.val + 1) / 2 = a.val by omega,
        show (2 * a.val + 1 + 1) / 2 = a.val + 1 by omega, Nat.cast_succ, Fin.cast_val_eq_self]
      exact ⟨ha, hb⟩

/-- The stated relation follows from the given hypotheses: `Set.InjOn (s26b_ψ n) (range (2 * n) :
Set ℕ)`. -/
lemma s26b_injOn_ψ {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Set.InjOn (s26b_ψ n) (range (2 * n) : Set ℕ) := by
  intro a ha b hb h
  have ha := mem_range.mp ha; have hb := mem_range.mp hb
  simp only [s26b_ψ, Prod.mk.injEq] at h
  rw [s26b_cast_eq_iff (by omega) (by omega), s26b_cast_eq_iff (by omega) (by omega)] at h
  omega

/-- Identity under the stated parameter and domain assumptions: `((s26b_ψ n a).1 = (s26b_ψ n b).1
∨ (s26b_ψ n a).2 = (s26b_ψ n b).2) ↔ a = b ∨ (a + 1) % (2 * n) = b ∨ (b + 1) % (2 * n) = a`. -/
lemma s26b_adj {n : ℕ} [NeZero n] (hn : 2 ≤ n) {a b : ℕ} (ha : a < 2 * n) (hb : b < 2 * n) :
    ((s26b_ψ n a).1 = (s26b_ψ n b).1 ∨ (s26b_ψ n a).2 = (s26b_ψ n b).2) ↔
      a = b ∨ (a + 1) % (2 * n) = b ∨ (b + 1) % (2 * n) = a := by
  simp only [s26b_ψ]
  rw [s26b_cast_eq_iff (by omega) (by omega), s26b_cast_eq_iff (by omega) (by omega)]
  rcases Nat.lt_or_ge (a + 1) (2 * n) with h1 | h1 <;>
    rcases Nat.lt_or_ge (b + 1) (2 * n) with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]; omega
  · rw [Nat.mod_eq_of_lt h1, show b + 1 = 2 * n by omega, Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt h2, show a + 1 = 2 * n by omega, Nat.mod_self]; omega
  · omega

/-- Formula under the stated hypotheses: `IsNonattacking (S.image (s26b_ψ n)) ↔ ∀ i ∈ S, (i + 1) %
(2 * n) ∉ S`. -/
lemma s26b_nonattacking_iff {n : ℕ} [NeZero n] (hn : 2 ≤ n) {S : Finset ℕ}
    (hS : S ⊆ range (2 * n)) :
    IsNonattacking (S.image (s26b_ψ n)) ↔ ∀ i ∈ S, (i + 1) % (2 * n) ∉ S := by
  have hinj := (s26b_injOn_ψ hn).mono (coe_subset.mpr hS)
  constructor
  · intro h i hi hj
    have hi' := mem_range.mp (hS hi)
    have hj' := mem_range.mp (hS hj)
    have hne : (i + 1) % (2 * n) ≠ i := by
      rcases Nat.lt_or_ge (i + 1) (2 * n) with h1 | h1
      · rw [Nat.mod_eq_of_lt h1]; omega
      · rw [show i + 1 = 2 * n by omega, Nat.mod_self]; omega
    have hψ : s26b_ψ n i ≠ s26b_ψ n ((i + 1) % (2 * n)) := fun e => hne (hinj hj hi e.symm)
    have := h _ (mem_image_of_mem _ hi) _ (mem_image_of_mem _ hj) hψ
    have := (s26b_adj hn hi' hj').mpr (Or.inr (Or.inl rfl))
    tauto
  · intro h x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    have hab : a ≠ b := fun e => hxy (e ▸ rfl)
    by_contra hc
    have hc : (s26b_ψ n a).1 = (s26b_ψ n b).1 ∨ (s26b_ψ n a).2 = (s26b_ψ n b).2 := by tauto
    rcases (s26b_adj hn (mem_range.mp (hS ha)) (mem_range.mp (hS hb))).mp hc with e | e | e
    · exact hab e
    · exact h a ha (e ▸ hb)
    · exact h b hb (e ▸ ha)

/-- Formula under the stated hypotheses: `(range (2 * n)).filter (fun m => s26b_ψ n m ∈ S.image
(s26b_ψ n)) = S`. -/
lemma s26b_filter_image_ψ {n : ℕ} [NeZero n] (hn : 2 ≤ n) {S : Finset ℕ}
    (hS : S ⊆ range (2 * n)) :
    (range (2 * n)).filter (fun m => s26b_ψ n m ∈ S.image (s26b_ψ n)) = S := by
  ext m
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hm, a, ha, e⟩
    rwa [← s26b_injOn_ψ hn (coe_subset.mpr hS ha) hm e]
  · intro hm; exact ⟨hS hm, m, hm, rfl⟩

/-- Formula under the stated hypotheses: `((range (2 * n)).filter (fun m => s26b_ψ n m ∈ C)).image
(s26b_ψ n) = C`. -/
lemma s26b_image_filter_ψ {n : ℕ} [NeZero n] {C : Finset (Fin n × Fin n)}
    (hC : C ⊆ menageBoard n) :
    ((range (2 * n)).filter (fun m => s26b_ψ n m ∈ C)).image (s26b_ψ n) = C := by
  ext x
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨m, ⟨_, hm⟩, rfl⟩; exact hm
  · intro hx
    have hx' : x ∈ (range (2 * n)).image (s26b_ψ n) := by rw [s26b_image_ψ]; exact hC hx
    obtain ⟨m, hm, e⟩ := mem_image.mp hx'
    exact ⟨m, ⟨hm, e ▸ hx⟩, e⟩

/-- Identity under the stated parameter and domain assumptions: `rookNumber (menageBoard n) k =
s26b_Q (2 * n) k`. -/
lemma s26b_rook_menage {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) :
    rookNumber (menageBoard n) k = s26b_Q (2 * n) k := by
  rw [rookNumber, s26b_Q]
  symm
  refine card_nbij' (fun S => S.image (s26b_ψ n))
    (fun C => (range (2 * n)).filter (fun m => s26b_ψ n m ∈ C)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard, mem_powerset] at hS ⊢
    obtain ⟨⟨hS, hc⟩, h⟩ := hS
    refine ⟨by rw [← s26b_image_ψ]; exact image_subset_image hS, ?_,
      (s26b_nonattacking_iff hn hS).mpr h⟩
    rw [card_image_of_injOn ((s26b_injOn_ψ hn).mono (coe_subset.mpr hS)), hc]
  · intro C hC
    simp only [mem_coe, mem_filter, mem_powerset] at hC
    rw [mem_coe, mem_filter, mem_powersetCard]
    obtain ⟨hC, hc, h⟩ := hC
    have hsub : (range (2 * n)).filter (fun m => s26b_ψ n m ∈ C) ⊆ range (2 * n) :=
      filter_subset _ _
    have e := s26b_image_filter_ψ hC
    refine ⟨⟨hsub, ?_⟩, (s26b_nonattacking_iff hn hsub).mp (by rw [e]; exact h)⟩
    rw [← hc, ← card_image_of_injOn ((s26b_injOn_ψ hn).mono (coe_subset.mpr hsub)), e]
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard] at hS
    exact s26b_filter_image_ψ hn hS.1.1
  · intro C hC
    simp only [mem_coe, mem_filter, mem_powerset] at hC
    exact s26b_image_filter_ψ hC.1

end MenageHelpers

/-- (26.15.9), problème des ménages: for `n ≥ 2`, `r_k(B) = (2n/(2n-k)) C(2n-k, k)`,
`0 ≤ k ≤ n`. -/
@[dlmf 26.15.E9]
theorem rookNumber_menageBoard {n : ℕ} [NeZero n] (hn : 2 ≤ n) {k : ℕ} (hk : k ≤ n) :
    (rookNumber (menageBoard n) k : ℚ) = 2 * n / (2 * n - k) * (2 * n - k).choose k := by
  rw [s26b_rook_menage hn, s26b_Q_formula hn hk]

/-- (26.15.10): the number of permutations avoiding the ménage board (the placements of the
husbands; the solution of the problème des ménages is `2 (n!)` times this) is
`∑_{k=0}^n (-1)^k (2n/(2n-k)) C(2n-k, k) (n-k)!`, `n ≥ 2`. The seating interpretation is not
formalized. -/
@[dlmf 26.15.E10]
theorem hitNumber_menageBoard_zero {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (2 * n.factorial * hitNumber (menageBoard n) 0 : ℚ) =
      2 * n.factorial * ∑ k ∈ range (n + 1),
        (-1 : ℚ) ^ k * (2 * n / (2 * n - k)) * (2 * n - k).choose k * (n - k).factorial := by
  have h := (hitNumber_zero_eq (menageBoard n)).2
  have h' : (hitNumber (menageBoard n) 0 : ℚ) =
      ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * rookNumber (menageBoard n) k * (n - k).factorial := by
    exact_mod_cast h
  rw [h']
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [rookNumber_menageBoard hn (by simpa [Nat.lt_succ_iff] using hk)]
  ring

/-- The Ferrers board of shape `(b_1, …, b_n)`: `{(j, k) | 1 ≤ k ≤ b_j}` (`0`-based: column
`k < b_j`). -/
def ferrersBoard {n : ℕ} (b : Fin n → ℕ) : Finset (Fin n × Fin n) :=
  univ.filter fun x => (x.2 : ℕ) < b x.1

/-! ### Rook numbers of Ferrers boards, column by column

`s26b_NA b m k`: nonattacking placements of `k` rooks in the first `m` columns of the Ferrers
board; adding column `m` gives `r_{k+1} = r_{k+1}' + (b_m - k) r_k'`, from which (26.15.11)
follows by induction with `(X + c)(x)_k = (x)_{k+1} + (c + k)(x)_k`. -/

/-- The first `m` columns of the Ferrers board. -/
def s26b_fb {n : ℕ} (b : Fin n → ℕ) (m : ℕ) : Finset (Fin n × Fin n) :=
  (ferrersBoard b).filter fun x => (x.1 : ℕ) < m

/-- Nonattacking placements of `k` rooks on the first `m` columns. -/
def s26b_NA {n : ℕ} (b : Fin n → ℕ) (m k : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  (s26b_fb b m).powerset.filter fun C => C.card = k ∧ IsNonattacking C

/-- Membership in `s26b_NA`. -/
lemma s26b_mem_NA {n : ℕ} {b : Fin n → ℕ} {m k : ℕ} {C : Finset (Fin n × Fin n)} :
    C ∈ s26b_NA b m k ↔ (∀ x ∈ C, (x.2 : ℕ) < b x.1 ∧ (x.1 : ℕ) < m) ∧ C.card = k ∧
      IsNonattacking C := by
  simp only [s26b_NA, mem_filter, mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun x hx => by simpa [s26b_fb, ferrersBoard] using h1 hx, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun x hx => by simpa [s26b_fb, ferrersBoard] using h1 x hx, h2⟩

/-- Distinct columns: a placement on `m` columns has at most `m` rooks. -/
lemma s26b_card_le {n : ℕ} {b : Fin n → ℕ} {m k : ℕ} {C : Finset (Fin n × Fin n)}
    (hC : C ∈ s26b_NA b m k) : k ≤ m := by
  obtain ⟨h1, rfl, h3⟩ := s26b_mem_NA.mp hC
  have hinj : Set.InjOn (fun x : Fin n × Fin n => (x.1 : ℕ)) C := fun x hx y hy h => by
    by_contra hne; exact (h3 x hx y hy hne).1 (Fin.ext h)
  rw [← card_image_of_injOn hinj]
  have : C.image (fun x : Fin n × Fin n => (x.1 : ℕ)) ⊆ range m := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact mem_range.mpr (h1 x hx).2
  simpa using card_le_card this

/-- The recurrence for the column-by-column rook numbers of a Ferrers board. -/
lemma s26b_NA_succ {n : ℕ} {b : Fin n → ℕ} (hb : Monotone b) (hbn : ∀ j, b j ≤ n) {m : ℕ}
    (hm : m < n) (k : ℕ) :
    ((s26b_NA b (m + 1) (k + 1)).card : ℤ) =
      (s26b_NA b m (k + 1)).card + ((b ⟨m, hm⟩ : ℤ) - k) * (s26b_NA b m k).card := by
  set bm := b ⟨m, hm⟩ with hbm
  have hbmn : bm ≤ n := hbn ⟨m, hm⟩
  set A := s26b_NA b (m + 1) (k + 1)
  have hsplit := card_filter_add_card_filter_not
    (s := A) (fun C => ∀ x ∈ C, (x.1 : ℕ) < m)
  have h0 : A.filter (fun C => ∀ x ∈ C, (x.1 : ℕ) < m) = s26b_NA b m (k + 1) := by
    ext C
    simp only [A, mem_filter, s26b_mem_NA]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨fun x hx => ⟨(h1 x hx).1, h4 x hx⟩, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun x hx => ⟨(h1 x hx).1, by have := (h1 x hx).2; omega⟩, h2, h3⟩,
        fun x hx => (h1 x hx).2⟩
  -- the placements using column `m`
  set A1 := A.filter (fun C => ¬∀ x ∈ C, (x.1 : ℕ) < m)
  have hmaps : ∀ C ∈ A1, C.filter (fun x => (x.1 : ℕ) < m) ∈ s26b_NA b m k := by
    intro C hC
    simp only [A1, A, mem_filter, s26b_mem_NA, not_forall] at hC
    obtain ⟨⟨h1, h2, h3⟩, x0, hx0, hx0m⟩ := hC
    have hx0' : (x0.1 : ℕ) = m := by have := (h1 x0 hx0).2; omega
    refine s26b_mem_NA.mpr ⟨fun x hx => ⟨(h1 x (mem_filter.mp hx).1).1, (mem_filter.mp hx).2⟩,
      ?_, fun x hx y hy => h3 x (mem_filter.mp hx).1 y (mem_filter.mp hy).1⟩
    have : C.filter (fun x => (x.1 : ℕ) < m) = C.erase x0 := by
      ext x
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨hx, hxm⟩; exact ⟨fun h => by rw [h] at hxm; omega, hx⟩
      · rintro ⟨hne, hx⟩
        refine ⟨hx, ?_⟩
        have := (h1 x hx).2
        by_contra hxm
        have hxeq : (x.1 : ℕ) = m := by omega
        exact (h3 x hx x0 hx0 hne).1 (Fin.ext (hxeq.trans hx0'.symm))
    rw [this, card_erase_of_mem hx0, h2, Nat.add_sub_cancel]
  have hfib : ∀ C' ∈ s26b_NA b m k,
      #{C ∈ A1 | C.filter (fun x => (x.1 : ℕ) < m) = C'} = bm - k ∧ k ≤ bm := by
    intro C' hC'
    obtain ⟨h1, h2, h3⟩ := s26b_mem_NA.mp hC'
    set mc : Fin n := ⟨m, hm⟩
    set Rows := (univ : Finset (Fin n)).filter fun ρ : Fin n => (ρ : ℕ) < bm
    have hRows : #Rows = bm := by
      have : Rows.map Fin.valEmbedding = range bm := by
        ext i
        simp only [Rows, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
          mem_range]
        constructor
        · rintro ⟨ρ, hρ, rfl⟩; exact hρ
        · intro hi; exact ⟨⟨i, by omega⟩, hi, rfl⟩
      rw [← card_map, this, card_range]
    have hsub : C'.image Prod.snd ⊆ Rows := by
      intro ρ hρ
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hρ
      simp only [Rows, mem_filter, mem_univ, true_and]
      have hle : x.1 ≤ mc := by rw [Fin.le_def]; exact (h1 x hx).2.le
      have := hb hle
      rw [hbm]
      exact lt_of_lt_of_le (h1 x hx).1 this
    have hcimg : #(C'.image Prod.snd) = k := by
      rw [card_image_of_injOn fun x hx y hy h => by
        by_contra hne; exact (h3 x hx y hy hne).2 h, h2]
    have hkb : k ≤ bm := by rw [← hcimg, ← hRows]; exact card_le_card hsub
    refine ⟨?_, hkb⟩
    rw [← hRows, ← hcimg, ← card_sdiff_of_subset hsub]
    symm
    refine card_bij (fun ρ _ => insert (mc, ρ) C') ?_ ?_ ?_
    · intro ρ hρ
      simp only [mem_sdiff, Rows, mem_filter, mem_univ, true_and, mem_image] at hρ
      have hnot : (mc, ρ) ∉ C' := fun h => by have := (h1 _ h).2; simp [mc] at this
      simp only [A1, A, mem_filter, s26b_mem_NA, not_forall]
      refine ⟨⟨⟨fun x hx => ?_, by rw [card_insert_of_notMem hnot, h2], ?_⟩, ⟨(mc, ρ),
        mem_insert_self _ _, by simp [mc]⟩⟩, ?_⟩
      · rcases mem_insert.mp hx with rfl | hx
        · exact ⟨hρ.1, by simp [mc]⟩
        · exact ⟨(h1 x hx).1, by have := (h1 x hx).2; omega⟩
      · intro x hx y hy hxy
        rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hy with rfl | hy
        · exact absurd rfl hxy
        · refine ⟨fun h => ?_, fun h => hρ.2 ⟨y, hy, h.symm⟩⟩
          have := (h1 y hy).2; rw [← h] at this; simp [mc] at this
        · refine ⟨fun h => ?_, fun h => hρ.2 ⟨x, hx, h⟩⟩
          have := (h1 x hx).2; rw [h] at this; simp [mc] at this
        · exact h3 x hx y hy hxy
      · ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hx, hxm⟩
          · simp [mc] at hxm
          · exact hx
        · intro hx; exact ⟨Or.inr hx, (h1 x hx).2⟩
    · intro ρ _ ρ' _ h
      have : (mc, ρ) ∈ insert (mc, ρ') C' := h ▸ mem_insert_self _ _
      rcases mem_insert.mp this with h' | h'
      · exact (Prod.mk.inj h').2
      · have := (h1 _ h').2; simp [mc] at this
    · intro C hC
      simp only [A1, A, mem_filter, s26b_mem_NA, not_forall] at hC
      obtain ⟨⟨⟨g1, g2, g3⟩, x0, hx0, hx0m⟩, hfil⟩ := hC
      have hx0' : x0.1 = mc := Fin.ext (by have := (g1 x0 hx0).2; simp [mc]; omega)
      have hCe : C.filter (fun x => (x.1 : ℕ) < m) = C.erase x0 := by
        ext x
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨hx, hxm⟩
          exact ⟨fun h => by rw [h, hx0'] at hxm; simp [mc] at hxm, hx⟩
        · rintro ⟨hne, hx⟩
          refine ⟨hx, ?_⟩
          have := (g1 x hx).2
          by_contra hxm
          exact (g3 x hx x0 hx0 hne).1 (Fin.ext (by rw [hx0']; simp [mc]; omega))
      refine ⟨x0.2, ?_, ?_⟩
      · simp only [mem_sdiff, Rows, mem_filter, mem_univ, true_and, mem_image, not_exists,
          not_and]
        refine ⟨by have := (g1 x0 hx0).1; rwa [hx0'] at this, fun y hy hyx => ?_⟩
        rw [← hfil, hCe] at hy
        obtain ⟨hne, hy⟩ := mem_erase.mp hy
        exact (g3 y hy x0 hx0 hne).2 hyx
      · rw [← hfil, hCe, show (mc, x0.2) = x0 from Prod.ext hx0'.symm rfl, insert_erase hx0]
  have hA1 : (#A1 : ℤ) = (bm - k : ℤ) * #(s26b_NA b m k) := by
    rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum, sum_congr rfl fun C' hC' => by
      rw [(hfib C' hC').1, Nat.cast_sub (hfib C' hC').2], sum_const, nsmul_eq_mul, mul_comm]
  rw [← hsplit, h0, Nat.cast_add, hA1]

/-- One empty placement. -/
lemma s26b_NA_zero {n : ℕ} (b : Fin n → ℕ) (m : ℕ) : #(s26b_NA b m 0) = 1 := by
  rw [card_eq_one]
  refine ⟨∅, ?_⟩
  ext C
  simp only [mem_singleton, s26b_mem_NA, card_eq_zero]
  constructor
  · exact fun h => h.2.1
  · rintro rfl; exact ⟨by simp, rfl, by simp [IsNonattacking]⟩

/-- No placement of more rooks than columns. -/
lemma s26b_NA_gt {n : ℕ} (b : Fin n → ℕ) {m k : ℕ} (h : m < k) : #(s26b_NA b m k) = 0 := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro C hC
  have := s26b_card_le hC
  omega

/-- All `n` columns give the rook numbers of the board. -/
lemma s26b_NA_full {n : ℕ} (b : Fin n → ℕ) (k : ℕ) :
    #(s26b_NA b n k) = rookNumber (ferrersBoard b) k := by
  have : s26b_fb b n = ferrersBoard b :=
    filter_true_of_mem fun (x : Fin n × Fin n) _ => x.1.isLt
  rw [s26b_NA, this, rookNumber]

/-- `(X + c) (x)_k = (x)_{k+1} + (c + k) (x)_k`. -/
lemma s26b_X_add_mul_desc (c : ℤ) (k : ℕ) :
    (X + C c) * descPochhammer ℤ k = descPochhammer ℤ (k + 1) + C (c + k) * descPochhammer ℤ k := by
  rw [descPochhammer_succ_right, map_add, map_natCast]; ring

/-- `b` extended by `0` to all of `ℕ`. -/
def s26b_bb {n : ℕ} (b : Fin n → ℕ) (j : ℕ) : ℕ := if h : j < n then b ⟨j, h⟩ else 0

/-- The column-by-column form of the Ferrers board identity. -/
lemma s26b_ferrers_poly {n : ℕ} {b : Fin n → ℕ} (hb : Monotone b) (hbn : ∀ j, b j ≤ n) :
    ∀ m, m ≤ n → ∑ k ∈ range (m + 1), C (#(s26b_NA b m (m - k)) : ℤ) * descPochhammer ℤ k =
      ∏ j ∈ range m, (X + C ((s26b_bb b j : ℤ) - j)) := by
  intro m
  induction m with
  | zero => intro _; simp [s26b_NA_zero]
  | succ m ih =>
    intro hm
    have hmn : m < n := by omega
    rw [prod_range_succ, ← ih hmn.le, sum_mul, sum_range_succ, Nat.sub_self, s26b_NA_zero,
      Nat.cast_one, map_one, one_mul]
    have hbb : s26b_bb b m = b ⟨m, hmn⟩ := by simp only [s26b_bb, hmn, ↓reduceDIte]
    have hL : ∀ k ∈ range (m + 1), C (#(s26b_NA b (m + 1) (m + 1 - k)) : ℤ) *
        descPochhammer ℤ k = C (#(s26b_NA b m (m - k + 1)) : ℤ) * descPochhammer ℤ k +
        C (#(s26b_NA b m (m - k)) : ℤ) * C ((b ⟨m, hmn⟩ : ℤ) - m + k) * descPochhammer ℤ k := by
      intro k hk
      rw [mem_range] at hk
      rw [show m + 1 - k = (m - k) + 1 by omega, s26b_NA_succ hb hbn hmn, Nat.cast_sub (by omega)]
      simp only [map_add, map_mul, map_sub, map_natCast]
      ring
    have hR : ∀ k ∈ range (m + 1), C (#(s26b_NA b m (m - k)) : ℤ) * descPochhammer ℤ k *
        (X + C ((s26b_bb b m : ℤ) - m)) = C (#(s26b_NA b m (m - k)) : ℤ) *
          descPochhammer ℤ (k + 1) +
        C (#(s26b_NA b m (m - k)) : ℤ) * C ((b ⟨m, hmn⟩ : ℤ) - m + k) * descPochhammer ℤ k := by
      intro k _
      rw [hbb, mul_assoc, mul_comm (descPochhammer ℤ k), s26b_X_add_mul_desc]
      ring
    rw [sum_congr rfl hL, sum_congr rfl hR, sum_add_distrib, sum_add_distrib]
    rw [sum_range_succ' (fun k => C (#(s26b_NA b m (m - k + 1)) : ℤ) * descPochhammer ℤ k),
      sum_range_succ (fun k => C (#(s26b_NA b m (m - k)) : ℤ) * descPochhammer ℤ (k + 1)),
      Nat.sub_zero, s26b_NA_gt b (Nat.lt_succ_self m), Nat.sub_self, s26b_NA_zero]
    have hre : ∀ k ∈ range m, C (#(s26b_NA b m (m - (k + 1) + 1)) : ℤ) *
        descPochhammer ℤ (k + 1) = C (#(s26b_NA b m (m - k)) : ℤ) * descPochhammer ℤ (k + 1) := by
      intro k hk
      rw [mem_range] at hk
      rw [show m - (k + 1) + 1 = m - k by omega]
    rw [sum_congr rfl hre]
    simp only [Nat.cast_zero, map_zero, zero_mul, add_zero, Nat.cast_one, map_one, one_mul]
    ring

/-- Coefficients in the falling-factorial basis are unique. -/
lemma s26b_descPochhammer_coeff_unique (N : ℕ) (d : ℕ → ℤ)
    (h : ∑ k ∈ range (N + 1), C (d k) * descPochhammer ℤ k = 0) : ∀ k ≤ N, d k = 0 := by
  induction N with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using h
  | succ N ih =>
    have hN : d (N + 1) = 0 := by
      have hc : (descPochhammer ℤ (N + 1)).coeff (N + 1) = 1 := by
        have := (monic_descPochhammer ℤ (N + 1)).coeff_natDegree
        rwa [descPochhammer_natDegree] at this
      have hlow : ∀ k ∈ range (N + 1), d k * (descPochhammer ℤ k).coeff (N + 1) = 0 := by
        intro k hk
        rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
        rw [descPochhammer_natDegree]
        exact mem_range.mp hk
      have := congrArg (fun p => p.coeff (N + 1)) h
      simp only [finsetSum_coeff, coeff_C_mul, coeff_zero] at this
      rw [sum_range_succ, hc, mul_one, sum_eq_zero hlow, zero_add] at this
      exact this
    intro k hk
    rcases Nat.lt_or_ge k (N + 1) with hk' | hk'
    · refine ih ?_ k (by omega)
      rw [sum_range_succ, hN, map_zero, zero_mul, add_zero] at h
      exact h
    · rw [show k = N + 1 by omega]; exact hN

/-- (26.15.11): for a Ferrers board with `0 ≤ b_1 ≤ ⋯ ≤ b_n ≤ n`,
`∑_{k=0}^n r_{n-k}(B) (x-k+1)_k = ∏_{j=1}^n (x + b_j - j + 1)`; `(x-k+1)_k` is the falling
factorial `x(x-1)⋯(x-k+1)` (`descPochhammer`); `0`-based `j` gives the factor `x + b_j - j`. -/
@[dlmf 26.15.E11]
theorem sum_rookNumber_ferrersBoard {n : ℕ} {b : Fin n → ℕ} (hb : Monotone b) (hbn : ∀ j, b j ≤ n) :
    ∑ k ∈ range (n + 1), C (rookNumber (ferrersBoard b) (n - k) : ℤ) * descPochhammer ℤ k =
      ∏ j : Fin n, (X + C ((b j : ℤ) - j)) := by
  have := s26b_ferrers_poly hb hbn n le_rfl
  simp only [s26b_NA_full] at this
  rw [this, ← Fin.prod_univ_eq_prod_range (fun j => X + C ((s26b_bb b j : ℤ) - j))]
  refine prod_congr rfl fun j _ => ?_
  simp only [s26b_bb, j.isLt, ↓reduceDIte]

/-- (26.15.12): for the Ferrers board of shape `(0, 1, …, n-1)`,
`∑_{k=0}^n r_{n-k}(B) (x-k+1)_k = xⁿ`. -/
@[dlmf 26.15.E12]
theorem sum_rookNumber_staircase (n : ℕ) :
    ∑ k ∈ range (n + 1), C (rookNumber (ferrersBoard fun j : Fin n => (j : ℕ)) (n - k) : ℤ) *
      descPochhammer ℤ k = X ^ n := by
  rw [sum_rookNumber_ferrersBoard (fun i j h => h) (fun j => j.isLt.le)]
  simp

/-- (26.15.13): for the Ferrers board of shape `(0, 1, …, n-1)`, `r_{n-k}(B) = S(n, k)`. -/
@[dlmf 26.15.E13]
theorem rookNumber_staircase {n k : ℕ} (hk : k ≤ n) :
    rookNumber (ferrersBoard fun j : Fin n => (j : ℕ)) (n - k) = Nat.stirlingSecond n k := by
  have h1 := sum_rookNumber_staircase n
  have h2 := X_pow_eq_sum_stirlingSecond_mul_descPochhammer ℤ n
  have := s26b_descPochhammer_coeff_unique n
    (fun k => (rookNumber (ferrersBoard fun j : Fin n => (j : ℕ)) (n - k) : ℤ) -
      Nat.stirlingSecond n k) (by
        simp only [map_sub, sub_mul, sum_sub_distrib]
        rw [h1, ← h2, sub_self]) k hk
  exact_mod_cast sub_eq_zero.mp this

end DLMF.Combinatorics

end
end
