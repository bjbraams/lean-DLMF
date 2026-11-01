/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic.Partitions
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Integer partitions: compositions

The compositions of DLMF §26.11. Compositions are Mathlib's `Composition n` (ordered lists of
positive integers summing to `n`; the empty composition of `0` included).

The counts `compositionCount` (`c(n)`), `compositionCountLength` (`c_m(n)`) and
`compositionCountNoOne` (`c(∈ T, n)`), with the initial values 26.11.1–26.11.2 and the closed
form 26.11.3, are in `DLMF.Combinatorics.Basic.Partitions`.

## Main definitions

* `compositionConsTwo`, `compositionSuccHead`: prepend a block `2`, and increase the first
  block by one.

## Main results

* `hasSum_compositionCountLength`: the generating function `q^m/(1 - q)^m` (DLMF 26.11.4).
* `compositionCountNoOne_eq_fib`: `c(∈ T, n) = F_{n-1}` for `n ≥ 1` (DLMF 26.11.6).

## Implementation notes

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
def compositionConsTwo {n : ℕ} (c : Composition n) : Composition (n + 2) where
  blocks := 2 :: c.blocks
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | h
    · norm_num
    · exact c.blocks_pos h
  blocks_sum := by rw [List.sum_cons, c.blocks_sum]; omega

/-- Add `1` to the first block. -/
def compositionSuccHead {n : ℕ} (c : Composition (n + 1)) : Composition (n + 2) where
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
private lemma compositionCountNoOne_add_two (n : ℕ) :
    compositionCountNoOne (n + 2) = compositionCountNoOne n + compositionCountNoOne (n + 1) := by
  classical
  unfold compositionCountNoOne
  set P : ∀ {m : ℕ}, Composition m → Prop := fun c => ∀ i ∈ c.blocks, 2 ≤ i
  have hA : Function.Injective (compositionConsTwo (n := n)) := by
    intro c d h
    have := congrArg Composition.blocks h
    simp only [compositionConsTwo, List.cons.injEq, true_and] at this
    exact Composition.ext this
  have hB : Function.Injective (compositionSuccHead (n := n)) := by
    intro c d h
    have h1 := congrArg Composition.blocks h
    simp only [compositionSuccHead] at h1
    apply Composition.ext
    rcases hc : c.blocks with _ | ⟨a, l⟩ <;> rcases hd : d.blocks with _ | ⟨b, l'⟩
    · rfl
    · have := d.blocks_sum; rw [hd] at h1; rw [hc] at h1; simp at h1
    · have := c.blocks_sum; rw [hd] at h1; rw [hc] at h1; simp at h1
    · rw [hc, hd] at h1
      simp only [List.modifyHead_cons, List.cons.injEq, Nat.add_right_cancel_iff] at h1
      rw [h1.1, h1.2]
  have hU : (univ.filter fun c : Composition (n + 2) => ∀ i ∈ c.blocks, 2 ≤ i) =
      (univ.filter fun c : Composition n => ∀ i ∈ c.blocks, 2 ≤ i).image compositionConsTwo ∪
      (univ.filter fun c : Composition (n + 1) => ∀ i ∈ c.blocks, 2 ≤ i).image
        compositionSuccHead := by
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
        simp [compositionConsTwo, h]
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
        · simp only [compositionSuccHead, List.modifyHead_cons, h]
          congr 1; omega
    · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
      · intro i hi
        simp only [compositionConsTwo, List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact le_rfl
        · exact hd i hi
      · intro i hi
        simp only [compositionSuccHead] at hi
        rcases h : d.blocks with _ | ⟨a, l⟩
        · rw [h] at hi; simp at hi
        · rw [h] at hi hd
          simp only [List.modifyHead_cons, List.mem_cons] at hi
          rcases hi with rfl | hi
          · have := hd a List.mem_cons_self; omega
          · exact hd i (List.mem_cons_of_mem a hi)
  have hD : Disjoint
      ((univ.filter fun c : Composition n => ∀ i ∈ c.blocks, 2 ≤ i).image compositionConsTwo)
      ((univ.filter fun c : Composition (n + 1) => ∀ i ∈ c.blocks, 2 ≤ i).image
        compositionSuccHead) := by
    rw [Finset.disjoint_left]
    rintro c hc hc'
    obtain ⟨d, -, rfl⟩ := mem_image.mp hc
    obtain ⟨d', hd', h⟩ := mem_image.mp hc'
    simp only [mem_filter, mem_univ, true_and] at hd'
    have h1 := congrArg Composition.blocks h
    simp only [compositionSuccHead, compositionConsTwo] at h1
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
    · rw [compositionCountNoOne_add_two, h0, h1]; rfl
    · rw [compositionCountNoOne_add_two, ih (n + 1) (by omega) (by omega),
        ih (n + 2) (by omega) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [show n + 2 - 1 = n + 1 by omega, Nat.fib_add_two]

end DLMF.Combinatorics
