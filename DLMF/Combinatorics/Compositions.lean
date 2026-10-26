/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer partitions: compositions (DLMF §26.11)

Compositions are Mathlib's `Composition n` (ordered lists of positive integers summing to `n`;
the empty composition of `0` included). `c(n)` is `compositionCount n`, `c_m(n)` is
`compositionCountLength m n` and `c(∈ T, n)` (no part `1`) is `compositionCountNoOne n`.
Mathlib already has `composition_card : Fintype.card (Composition n) = 2 ^ (n - 1)`.
The Fibonacci numbers are Mathlib's `Nat.fib`; (26.11.5) and Binet's formula (26.11.7,
`Real.coe_fib_eq`) are recorded as upstream pointers in `MathlibCoverageB`.

## References

* NIST DLMF §26.11.
-/

@[expose] public section

noncomputable section

open Finset

namespace DLMF.Combinatorics

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
lemma q26b_card_compositionAsSetEquiv {n : ℕ} (hn : 1 ≤ n) (d : CompositionAsSet n) :
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
      rw [q26b_card_compositionAsSetEquiv hn]
      simp [compositionEquiv])
  rw [h]
  split_ifs with hm
  · subst hm
    simp
  · rw [show (univ.filter fun s : Finset (Fin (n - 1)) => s.card + 1 = m) =
        powersetCard (m - 1) univ by
      ext s; simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]; omega]
    simp

/-- (26.11.4): `∑ₙ c_m(n) qⁿ = q^m/(1 - q)^m` for `|q| < 1`. -/
@[dlmf 26.11.E4]
theorem hasSum_compositionCountLength {q : ℂ} (hq : ‖q‖ < 1) (m : ℕ) :
    HasSum (fun n => (compositionCountLength m n : ℂ) * q ^ n) (q ^ m / (1 - q) ^ m) := by
  have hc : ∀ n, compositionCountLength m n =
      if n = 0 then (if m = 0 then 1 else 0)
        else (if m = 0 then 0 else (n - 1).choose (m - 1)) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp only [↓reduceIte]; exact compositionCountLength_zero m
    · simp only [hn, ↓reduceIte]; exact compositionCountLength_eq_choose (by omega) m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, div_one]
    convert hasSum_single (f := fun n : ℕ => (compositionCountLength 0 n : ℂ) * q ^ n) 0 ?_ using 1
    · simp [hc]
    · intro n hn; simp [hc, hn]
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [← hasSum_nat_add_iff' (j + 1)]
    have hz : ∑ i ∈ range (j + 1), (compositionCountLength (j + 1) i : ℂ) * q ^ i = 0 := by
      refine sum_eq_zero fun i hi => ?_
      simp only [mem_range] at hi
      by_cases h0 : i = 0
      · simp [hc, h0]
      · rw [hc]; simp only [h0, show j + 1 ≠ 0 by omega, ↓reduceIte]
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [hz, sub_zero]
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one j hq).mul_right (q ^ (j + 1))
    convert h using 1
    · funext i
      rw [hc]
      simp only [show i + (j + 1) ≠ 0 by omega, show j + 1 ≠ 0 by omega, ↓reduceIte]
      rw [show i + (j + 1) - 1 = i + j by omega, pow_add]
      push_cast; ring
    · field_simp

/-- Prepend a block `2`. -/
def q26b_compCons2 {n : ℕ} (c : Composition n) : Composition (n + 2) where
  blocks := 2 :: c.blocks
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | h
    · norm_num
    · exact c.blocks_pos h
  blocks_sum := by rw [List.sum_cons, c.blocks_sum]; omega

/-- Add `1` to the first block. -/
def q26b_compSuccHead {n : ℕ} (c : Composition (n + 1)) : Composition (n + 2) where
  blocks := c.blocks.modifyHead (· + 1)
  blocks_pos := by
    intro i hi
    rcases h : c.blocks with _ | ⟨a, l⟩
    · rw [h] at hi; simp at hi
    · rw [h] at hi
      simp only [List.modifyHead_cons, List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact c.blocks_pos (by rw [h]; exact List.mem_cons_of_mem a hi)
  blocks_sum := by
    have hs := c.blocks_sum
    rcases h : c.blocks with _ | ⟨a, l⟩
    · rw [h] at hs; simp at hs
    · rw [h] at hs
      simp only [List.modifyHead_cons, List.sum_cons] at hs ⊢
      omega

/-- The recurrence `c(∈ T, n+2) = c(∈ T, n) + c(∈ T, n+1)`. -/
lemma q26b_compositionCountNoOne_add_two (n : ℕ) :
    compositionCountNoOne (n + 2) = compositionCountNoOne n + compositionCountNoOne (n + 1) := by
  classical
  unfold compositionCountNoOne
  set P : ∀ {m : ℕ}, Composition m → Prop := fun c => ∀ i ∈ c.blocks, 2 ≤ i
  have hA : Function.Injective (q26b_compCons2 (n := n)) := by
    intro c d h
    have := congrArg Composition.blocks h
    simp only [q26b_compCons2, List.cons.injEq, true_and] at this
    exact Composition.ext this
  have hB : Function.Injective (q26b_compSuccHead (n := n)) := by
    intro c d h
    have h1 := congrArg Composition.blocks h
    simp only [q26b_compSuccHead] at h1
    apply Composition.ext
    rcases hc : c.blocks with _ | ⟨a, l⟩ <;> rcases hd : d.blocks with _ | ⟨b, l'⟩
    · rfl
    · have := d.blocks_sum; rw [hd] at h1; rw [hc] at h1; simp at h1
    · have := c.blocks_sum; rw [hd] at h1; rw [hc] at h1; simp at h1
    · rw [hc, hd] at h1
      simp only [List.modifyHead_cons, List.cons.injEq, Nat.add_right_cancel_iff] at h1
      rw [h1.1, h1.2]
  have hU : (univ.filter fun c : Composition (n + 2) => ∀ i ∈ c.blocks, 2 ≤ i) =
      (univ.filter fun c : Composition n => ∀ i ∈ c.blocks, 2 ≤ i).image q26b_compCons2 ∪
      (univ.filter fun c : Composition (n + 1) => ∀ i ∈ c.blocks, 2 ≤ i).image
        q26b_compSuccHead := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
    constructor
    · intro hc
      have hs := c.blocks_sum
      rcases h : c.blocks with _ | ⟨a, l⟩
      · rw [h] at hs; simp at hs
      rw [h] at hs hc
      have ha : 2 ≤ a := hc a List.mem_cons_self
      have hl : ∀ i ∈ l, 2 ≤ i := fun i hi => hc i (List.mem_cons_of_mem a hi)
      have hlpos : ∀ i ∈ l, 0 < i := fun i hi => by have := hl i hi; omega
      rw [List.sum_cons] at hs
      rcases Nat.eq_or_lt_of_le ha with rfl | ha3
      · left
        refine ⟨⟨l, hlpos _, by omega⟩, hl, Composition.ext ?_⟩
        simp [q26b_compCons2, h]
      · right
        refine ⟨⟨(a - 1) :: l, ?_, ?_⟩, ?_, Composition.ext ?_⟩
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · exact hlpos i hi
        · rw [List.sum_cons]; omega
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · exact hl i hi
        · simp only [q26b_compSuccHead, List.modifyHead_cons, h]
          congr 1; omega
    · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
      · intro i hi
        simp only [q26b_compCons2, List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact le_rfl
        · exact hd i hi
      · intro i hi
        simp only [q26b_compSuccHead] at hi
        rcases h : d.blocks with _ | ⟨a, l⟩
        · rw [h] at hi; simp at hi
        · rw [h] at hi hd
          simp only [List.modifyHead_cons, List.mem_cons] at hi
          rcases hi with rfl | hi
          · have := hd a List.mem_cons_self; omega
          · exact hd i (List.mem_cons_of_mem a hi)
  have hD : Disjoint
      ((univ.filter fun c : Composition n => ∀ i ∈ c.blocks, 2 ≤ i).image q26b_compCons2)
      ((univ.filter fun c : Composition (n + 1) => ∀ i ∈ c.blocks, 2 ≤ i).image
        q26b_compSuccHead) := by
    rw [Finset.disjoint_left]
    rintro c hc hc'
    obtain ⟨d, -, rfl⟩ := mem_image.mp hc
    obtain ⟨d', hd', h⟩ := mem_image.mp hc'
    simp only [mem_filter, mem_univ, true_and] at hd'
    have h1 := congrArg Composition.blocks h
    simp only [q26b_compSuccHead, q26b_compCons2] at h1
    rcases hb : d'.blocks with _ | ⟨a, l⟩
    · rw [hb] at h1; simp at h1
    · rw [hb] at h1 hd'
      simp only [List.modifyHead_cons, List.cons.injEq] at h1
      have := hd' a List.mem_cons_self
      omega
  rw [hU, card_union_of_disjoint hD, card_image_of_injective _ hA, card_image_of_injective _ hB]

/-- (26.11.6): `c(∈ T, n) = F_{n-1}` for `n ≥ 1`. -/
@[dlmf 26.11.E6]
theorem compositionCountNoOne_eq_fib {n : ℕ} (hn : 1 ≤ n) :
    compositionCountNoOne n = Nat.fib (n - 1) := by
  have h1 : compositionCountNoOne 1 = 0 := by
    unfold compositionCountNoOne
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    have hs := c.blocks_sum
    rcases h : c.blocks with _ | ⟨a, l⟩
    · rw [h] at hs; simp at hs
    · rw [h] at hs hc
      have := hc a List.mem_cons_self
      rw [List.sum_cons] at hs
      omega
  have h0 : compositionCountNoOne 0 = 1 := compositionCount_zero.2
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · omega
    · simpa using h1
    · rw [q26b_compositionCountNoOne_add_two, h0, h1]; rfl
    · rw [q26b_compositionCountNoOne_add_two, ih (n + 1) (by omega) (by omega),
        ih (n + 2) (by omega) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [show n + 2 - 1 = n + 1 by omega, Nat.fib_add_two]

end DLMF.Combinatorics
