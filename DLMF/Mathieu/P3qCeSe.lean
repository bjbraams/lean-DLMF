/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.P3qVector

/-!
# The expansions DLMF 28.6.21–28.6.26 of `ce_n`, `se_n` for small `n`

Explicit trial vectors (Rayleigh–Schrödinger perturbation series of the Fourier coefficients)
for `p3q_expand_AE0`, `p3q_expand_AE`, `p3q_expand_AO`, `p3q_expand_BO`, `p3q_expand_BE`:
`√2 ce₀`, `ce₁`, `se₁` to `O(q⁴)`, `ce₂`, `se₂` to `O(q³)` (DLMF 28.6.21–28.6.25), and the
general formula 28.6.26 (and its `se` analogue) at `m = 3, 4, 5`, where the boundary rows of the
recurrences enter.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- DLMF 28.6.21: `√2 ce₀(z, q) = 1 - (q/2) cos 2z + (q²/32)(cos 4z - 2)
- (q³/128)((1/9) cos 6z - 11 cos 2z) + O(q⁴)`. -/
theorem p3q_ce0 (z : ℂ) :
    (fun q : ℝ => (Real.sqrt 2 : ℂ) * mathieuCe 0 z q - (1 - q / 2 * Complex.cos (2 * z) +
      q ^ 2 / 32 * (Complex.cos (4 * z) - 2) -
      q ^ 3 / 128 * (1 / 9 * Complex.cos (6 * z) - 11 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 4) := by
  have h := p3q_expand_AE0 (N := 4) (K := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => -((1 : ℂ) / 2) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 2) * (q : ℂ) + ((7 : ℂ) / 128) * (q : ℂ) ^ 3
      | 2 => ((1 : ℂ) / 32) * (q : ℂ) ^ 2
      | 3 => -((1 : ℂ) / 1152) * (q : ℂ) ^ 3
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => ((7 : ℂ) / 128))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((7 : ℂ) / 256))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => ((5 : ℂ) / 72))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 2304))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 1152))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 16) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((1 : ℂ) / 16) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => -((79 : ℂ) / 2048) + ((443 : ℂ) / 82944) * (q : ℂ) ^ 2
        - ((12395 : ℂ) / 42467328) * (q : ℂ) ^ 4 + ((1985 : ℂ) / 339738624) * (q : ℂ) ^ 6)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 16) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 4, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => (1 : ℂ)
        | 1 => -((1 : ℂ) / 2) * (q : ℂ) + ((7 : ℂ) / 128) * (q : ℂ) ^ 3
        | 2 => ((1 : ℂ) / 32) * (q : ℂ) ^ 2
        | 3 => -((1 : ℂ) / 1152) * (q : ℂ) ^ 3
        | _ => 0) q i * Complex.cos (2 * (i : ℂ) * z) -
      (1 - q / 2 * Complex.cos (2 * z) +
      q ^ 2 / 32 * (Complex.cos (4 * z) - 2) -
      q ^ 3 / 128 * (1 / 9 * Complex.cos (6 * z) - 11 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q : ℝ => q ^ 4) :=
    p3q_isBigO_of_eq (e := 4) le_rfl
      (s := fun q : ℝ => -((1 : ℂ) / 512) * Complex.cos (4 * z)
        - ((7 : ℂ) / 2048) * Complex.cos (2 * z) * (q : ℂ)
        + ((1 : ℂ) / 18432) * Complex.cos (6 * z) * (q : ℂ))
      (fun q => by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf
        simp only [Complex.cos_zero]
        ring_nf)
      (by fun_prop)
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.22: the expansion of `ce₁(z, q)` to `O(q⁴)`. -/
theorem p3q_ce1 (z : ℂ) :
    (fun q : ℝ => mathieuCe 1 z q - (Complex.cos z - q / 8 * Complex.cos (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.cos (5 * z) - 2 * Complex.cos (3 * z) - Complex.cos z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.cos (7 * z) - 8 / 9 * Complex.cos (5 * z) -
        1 / 3 * Complex.cos (3 * z) + 2 * Complex.cos z))) =O[𝓝 0] (fun q => q ^ 4) := by
  have h := p3q_expand_AO 0 (N := 4) (K := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (1 : ℂ) + (1 : ℂ) * (q : ℂ) - ((1 : ℂ) / 8) * (q : ℂ) ^ 2
      - ((1 : ℂ) / 64) * (q : ℂ) ^ 3)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 8) * (q : ℂ) - ((1 : ℂ) / 64) * (q : ℂ) ^ 2
          - ((1 : ℂ) / 1536) * (q : ℂ) ^ 3
      | 2 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1152) * (q : ℂ) ^ 3
      | 3 => -((1 : ℂ) / 9216) * (q : ℂ) ^ 3
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 1536))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((11 : ℂ) / 4608) - ((1 : ℂ) / 3072) * (q : ℂ)
            - ((1 : ℂ) / 98304) * (q : ℂ) ^ 2)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 1024) + ((7 : ℂ) / 36864) * (q : ℂ)
            + ((1 : ℂ) / 73728) * (q : ℂ) ^ 2)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 1024) - ((1 : ℂ) / 73728) * (q : ℂ)
            - ((1 : ℂ) / 589824) * (q : ℂ) ^ 2)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 9216))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 128) * (q : ℂ) ^ 2 - ((1 : ℂ) / 512) * (q : ℂ) ^ 3)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((1 : ℂ) / 128) * (q : ℂ) ^ 2 - ((1 : ℂ) / 512) * (q : ℂ) ^ 3).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => ((37 : ℂ) / 147456) - ((55 : ℂ) / 884736) * (q : ℂ)
        - ((683 : ℂ) / 42467328) * (q : ℂ) ^ 2 - ((163 : ℂ) / 113246208) * (q : ℂ) ^ 3
        + ((391 : ℂ) / 5435817984) * (q : ℂ) ^ 4 + ((275 : ℂ) / 10871635968) * (q : ℂ) ^ 5
        + ((3653 : ℂ) / 1391569403904) * (q : ℂ) ^ 6 + ((413 : ℂ) / 2783138807808) * (q : ℂ) ^ 7
        + ((101 : ℂ) / 22265110462464) * (q : ℂ) ^ 8)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 128) * (q : ℂ) ^ 2 - ((1 : ℂ) / 512) * (q : ℂ) ^ 3) q *
      ∑ i ∈ Finset.range 4, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => (1 : ℂ)
        | 1 => -((1 : ℂ) / 8) * (q : ℂ) - ((1 : ℂ) / 64) * (q : ℂ) ^ 2
            - ((1 : ℂ) / 1536) * (q : ℂ) ^ 3
        | 2 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1152) * (q : ℂ) ^ 3
        | 3 => -((1 : ℂ) / 9216) * (q : ℂ) ^ 3
        | _ => 0) q i * Complex.cos ((2 * (i : ℂ) + 1) * z) -
      (Complex.cos z - q / 8 * Complex.cos (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.cos (5 * z) - 2 * Complex.cos (3 * z) - Complex.cos z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.cos (7 * z) - 8 / 9 * Complex.cos (5 * z) -
        1 / 3 * Complex.cos (3 * z) + 2 * Complex.cos z))) =O[𝓝 0]
      (fun q : ℝ => q ^ 4) :=
    p3q_isBigO_of_eq (e := 4) le_rfl
      (s := fun q : ℝ => ((3 : ℂ) / 8192) * Complex.cos (3 * z)
        - ((1 : ℂ) / 24576) * Complex.cos (5 * z)
        + ((7 : ℂ) / 196608) * Complex.cos (3 * z) * (q : ℂ)
        - ((5 : ℂ) / 294912) * Complex.cos (5 * z) * (q : ℂ)
        + ((1 : ℂ) / 1179648) * Complex.cos (7 * z) * (q : ℂ)
        + ((1 : ℂ) / 786432) * Complex.cos (3 * z) * (q : ℂ) ^ 2
        - ((1 : ℂ) / 589824) * Complex.cos (5 * z) * (q : ℂ) ^ 2
        + ((1 : ℂ) / 4718592) * Complex.cos (7 * z) * (q : ℂ) ^ 2)
      (fun q => by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf)
      (by fun_prop)
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.23: the expansion of `se₁(z, q)` to `O(q⁴)`. -/
theorem p3q_se1 (z : ℂ) :
    (fun q : ℝ => mathieuSe 1 z q - (Complex.sin z - q / 8 * Complex.sin (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.sin (5 * z) + 2 * Complex.sin (3 * z) - Complex.sin z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.sin (7 * z) + 8 / 9 * Complex.sin (5 * z) -
        1 / 3 * Complex.sin (3 * z) - 2 * Complex.sin z))) =O[𝓝 0] (fun q => q ^ 4) := by
  have h := p3q_expand_BO 0 (N := 4) (K := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (1 : ℂ) - (1 : ℂ) * (q : ℂ) - ((1 : ℂ) / 8) * (q : ℂ) ^ 2
      + ((1 : ℂ) / 64) * (q : ℂ) ^ 3)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 8) * (q : ℂ) + ((1 : ℂ) / 64) * (q : ℂ) ^ 2
          - ((1 : ℂ) / 1536) * (q : ℂ) ^ 3
      | 2 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2 - ((1 : ℂ) / 1152) * (q : ℂ) ^ 3
      | 3 => -((1 : ℂ) / 9216) * (q : ℂ) ^ 3
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 1536))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => ((11 : ℂ) / 4608) - ((1 : ℂ) / 3072) * (q : ℂ)
            + ((1 : ℂ) / 98304) * (q : ℂ) ^ 2)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 1024) - ((7 : ℂ) / 36864) * (q : ℂ)
            + ((1 : ℂ) / 73728) * (q : ℂ) ^ 2)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 1024) - ((1 : ℂ) / 73728) * (q : ℂ)
            + ((1 : ℂ) / 589824) * (q : ℂ) ^ 2)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 9216))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 128) * (q : ℂ) ^ 2 + ((1 : ℂ) / 512) * (q : ℂ) ^ 3)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((1 : ℂ) / 128) * (q : ℂ) ^ 2 + ((1 : ℂ) / 512) * (q : ℂ) ^ 3).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => ((37 : ℂ) / 147456) + ((55 : ℂ) / 884736) * (q : ℂ)
        - ((683 : ℂ) / 42467328) * (q : ℂ) ^ 2 + ((163 : ℂ) / 113246208) * (q : ℂ) ^ 3
        + ((391 : ℂ) / 5435817984) * (q : ℂ) ^ 4 - ((275 : ℂ) / 10871635968) * (q : ℂ) ^ 5
        + ((3653 : ℂ) / 1391569403904) * (q : ℂ) ^ 6 - ((413 : ℂ) / 2783138807808) * (q : ℂ) ^ 7
        + ((101 : ℂ) / 22265110462464) * (q : ℂ) ^ 8)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 128) * (q : ℂ) ^ 2 + ((1 : ℂ) / 512) * (q : ℂ) ^ 3) q *
      ∑ i ∈ Finset.range 4, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => (1 : ℂ)
        | 1 => -((1 : ℂ) / 8) * (q : ℂ) + ((1 : ℂ) / 64) * (q : ℂ) ^ 2
            - ((1 : ℂ) / 1536) * (q : ℂ) ^ 3
        | 2 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2 - ((1 : ℂ) / 1152) * (q : ℂ) ^ 3
        | 3 => -((1 : ℂ) / 9216) * (q : ℂ) ^ 3
        | _ => 0) q i * Complex.sin ((2 * (i : ℂ) + 1) * z) -
      (Complex.sin z - q / 8 * Complex.sin (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.sin (5 * z) + 2 * Complex.sin (3 * z) - Complex.sin z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.sin (7 * z) + 8 / 9 * Complex.sin (5 * z) -
        1 / 3 * Complex.sin (3 * z) - 2 * Complex.sin z))) =O[𝓝 0]
      (fun q : ℝ => q ^ 4) :=
    p3q_isBigO_of_eq (e := 4) le_rfl
      (s := fun q : ℝ => -((3 : ℂ) / 8192) * Complex.sin (3 * z)
        - ((1 : ℂ) / 24576) * Complex.sin (5 * z)
        + ((7 : ℂ) / 196608) * Complex.sin (3 * z) * (q : ℂ)
        + ((5 : ℂ) / 294912) * Complex.sin (5 * z) * (q : ℂ)
        + ((1 : ℂ) / 1179648) * Complex.sin (7 * z) * (q : ℂ)
        - ((1 : ℂ) / 786432) * Complex.sin (3 * z) * (q : ℂ) ^ 2
        - ((1 : ℂ) / 589824) * Complex.sin (5 * z) * (q : ℂ) ^ 2
        - ((1 : ℂ) / 4718592) * Complex.sin (7 * z) * (q : ℂ) ^ 2)
      (fun q => by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf)
      (by fun_prop)
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.24: the expansion of `ce₂(z, q)` to `O(q³)`. -/
theorem p3q_ce2 (z : ℂ) :
    (fun q : ℝ => mathieuCe 2 z q - (Complex.cos (2 * z) -
      q / 4 * (1 / 3 * Complex.cos (4 * z) - 1) +
      q ^ 2 / 128 * (1 / 3 * Complex.cos (6 * z) - 76 / 9 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_AE 1 (by norm_num) (N := 4) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (4 : ℂ) + ((5 : ℂ) / 12) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 4) * (q : ℂ)
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 12) * (q : ℂ)
      | 3 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => -((5 : ℂ) / 48))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((43 : ℂ) / 1152))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((5 : ℂ) / 4608))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 384))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((19 : ℂ) / 288) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((19 : ℂ) / 288) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => -((5773 : ℂ) / 442368) + ((109573 : ℂ) / 191102976) * (q : ℂ) ^ 2
        + ((361 : ℂ) / 12230590464) * (q : ℂ) ^ 4)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((19 : ℂ) / 288) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 4, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => ((1 : ℂ) / 4) * (q : ℂ)
        | 1 => (1 : ℂ)
        | 2 => -((1 : ℂ) / 12) * (q : ℂ)
        | 3 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.cos (2 * (i : ℂ) * z) -
      (Complex.cos (2 * z) -
      q / 4 * (1 / 3 * Complex.cos (4 * z) - 1) +
      q ^ 2 / 128 * (1 / 3 * Complex.cos (6 * z) - 76 / 9 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => -((19 : ℂ) / 1152) * 1 + ((19 : ℂ) / 3456) * Complex.cos (4 * z)
        - ((19 : ℂ) / 110592) * Complex.cos (6 * z) * (q : ℂ))
      (fun q => by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf
        simp only [Complex.cos_zero]
        ring_nf)
      (by fun_prop)
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.25: the expansion of `se₂(z, q)` to `O(q³)`. -/
theorem p3q_se2 (z : ℂ) :
    (fun q : ℝ => mathieuSe 2 z q - (Complex.sin (2 * z) - q / 12 * Complex.sin (4 * z) +
      q ^ 2 / 128 * (1 / 3 * Complex.sin (6 * z) - 4 / 9 * Complex.sin (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_BE 0 (N := 3) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (4 : ℂ) - ((1 : ℂ) / 12) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 12) * (q : ℂ)
      | 2 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => -((5 : ℂ) / 1152))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 4608))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 384))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 288) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((1 : ℂ) / 288) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => -((13 : ℂ) / 442368) + ((7 : ℂ) / 191102976) * (q : ℂ) ^ 2
        + ((1 : ℂ) / 12230590464) * (q : ℂ) ^ 4)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((1 : ℂ) / 288) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 3, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => (1 : ℂ)
        | 1 => -((1 : ℂ) / 12) * (q : ℂ)
        | 2 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.sin ((2 * (i : ℂ) + 2) * z) -
      (Complex.sin (2 * z) - q / 12 * Complex.sin (4 * z) +
      q ^ 2 / 128 * (1 / 3 * Complex.sin (6 * z) - 4 / 9 * Complex.sin (2 * z)))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => ((1 : ℂ) / 3456) * Complex.sin (4 * z)
        - ((1 : ℂ) / 110592) * Complex.sin (6 * z) * (q : ℂ))
      (fun q => by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf)
      (by fun_prop)
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.26 for `m = 3`: the expansion of `ce₃(z, q)` to `O(q³)`. -/
theorem p3q_ce3 {m : ℕ} (hm : m = 3) (z : ℂ) :
    (fun q : ℝ => mathieuCe m z q - (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_AO 1 (N := 4) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (9 : ℂ) + ((1 : ℂ) / 16) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 8) * (q : ℂ) + ((1 : ℂ) / 64) * (q : ℂ) ^ 2
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 16) * (q : ℂ)
      | 3 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 128) - ((1 : ℂ) / 1024) * (q : ℂ))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 64))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((7 : ℂ) / 1280))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 10240))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 640))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((5 : ℂ) / 512) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((5 : ℂ) / 512) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 3) (by decide)
      (s := fun q : ℝ => ((1 : ℂ) / 256) - ((259 : ℂ) / 6553600) * (q : ℂ)
        - ((5 : ℂ) / 65536) * (q : ℂ) ^ 2 - ((991 : ℂ) / 335544320) * (q : ℂ) ^ 3
        + ((25 : ℂ) / 67108864) * (q : ℂ) ^ 4 + ((101 : ℂ) / 4294967296) * (q : ℂ) ^ 5)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((5 : ℂ) / 512) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 4, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => ((1 : ℂ) / 8) * (q : ℂ) + ((1 : ℂ) / 64) * (q : ℂ) ^ 2
        | 1 => (1 : ℂ)
        | 2 => -((1 : ℂ) / 16) * (q : ℂ)
        | 3 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.cos ((2 * (i : ℂ) + 1) * z) -
      (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => -((5 : ℂ) / 4096) * Complex.cos (1 * z)
        + ((5 : ℂ) / 8192) * Complex.cos (5 * z)
        - ((5 : ℂ) / 32768) * Complex.cos (1 * z) * (q : ℂ)
        - ((1 : ℂ) / 65536) * Complex.cos (7 * z) * (q : ℂ))
      (fun q => by
        subst hm; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf
        simp only [Complex.cos_neg]
        ring_nf)
      (by fun_prop)
  subst hm
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.27 for `m = 3`: the expansion of `se₃(z, q)` to `O(q³)`. -/
theorem p3q_se3 {m : ℕ} (hm : m = 3) (z : ℂ) :
    (fun q : ℝ => mathieuSe m z q - (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_BO 1 (N := 4) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (9 : ℂ) + ((1 : ℂ) / 16) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 8) * (q : ℂ) - ((1 : ℂ) / 64) * (q : ℂ) ^ 2
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 16) * (q : ℂ)
      | 3 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 128) + ((1 : ℂ) / 1024) * (q : ℂ))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 64))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((7 : ℂ) / 1280))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 10240))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 640))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((5 : ℂ) / 512) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((5 : ℂ) / 512) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 3) (by decide)
      (s := fun q : ℝ => -((1 : ℂ) / 256) - ((259 : ℂ) / 6553600) * (q : ℂ)
        + ((5 : ℂ) / 65536) * (q : ℂ) ^ 2 - ((991 : ℂ) / 335544320) * (q : ℂ) ^ 3
        - ((25 : ℂ) / 67108864) * (q : ℂ) ^ 4 + ((101 : ℂ) / 4294967296) * (q : ℂ) ^ 5)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((5 : ℂ) / 512) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 4, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => ((1 : ℂ) / 8) * (q : ℂ) - ((1 : ℂ) / 64) * (q : ℂ) ^ 2
        | 1 => (1 : ℂ)
        | 2 => -((1 : ℂ) / 16) * (q : ℂ)
        | 3 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.sin ((2 * (i : ℂ) + 1) * z) -
      (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => -((5 : ℂ) / 4096) * Complex.sin (1 * z)
        + ((5 : ℂ) / 8192) * Complex.sin (5 * z)
        + ((5 : ℂ) / 32768) * Complex.sin (1 * z) * (q : ℂ)
        - ((1 : ℂ) / 65536) * Complex.sin (7 * z) * (q : ℂ))
      (fun q => by
        subst hm; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf
        simp only [Complex.sin_neg]
        ring_nf)
      (by fun_prop)
  subst hm
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.26 for `m = 4`: the expansion of `ce₄(z, q)` to `O(q³)`. -/
theorem p3q_ce4 {m : ℕ} (hm : m = 4) (z : ℂ) :
    (fun q : ℝ => mathieuCe m z q - (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_AE 2 (by norm_num) (N := 5) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (16 : ℂ) + ((1 : ℂ) / 30) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2
      | 1 => ((1 : ℂ) / 12) * (q : ℂ)
      | 2 => (1 : ℂ)
      | 3 => -((1 : ℂ) / 20) * (q : ℂ)
      | 4 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 5 := ⟨i - 5, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 5760))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((11 : ℂ) / 1440))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((13 : ℂ) / 4800))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 28800))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 960))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((17 : ℂ) / 3600) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((17 : ℂ) / 3600) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => -((799 : ℂ) / 69120000) - ((116467 : ℂ) / 373248000000) * (q : ℂ) ^ 2
        + ((4913 : ℂ) / 3981312000000) * (q : ℂ) ^ 4)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((17 : ℂ) / 3600) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 5, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2
        | 1 => ((1 : ℂ) / 12) * (q : ℂ)
        | 2 => (1 : ℂ)
        | 3 => -((1 : ℂ) / 20) * (q : ℂ)
        | 4 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.cos (2 * (i : ℂ) * z) -
      (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => -((17 : ℂ) / 43200) * Complex.cos (2 * z)
        + ((17 : ℂ) / 72000) * Complex.cos (6 * z) - ((17 : ℂ) / 691200) * 1 * (q : ℂ)
        - ((17 : ℂ) / 3456000) * Complex.cos (8 * z) * (q : ℂ))
      (fun q => by
        subst hm; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf
        simp only [Complex.cos_zero]
        ring_nf)
      (by fun_prop)
  subst hm
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.27 for `m = 4`: the expansion of `se₄(z, q)` to `O(q³)`. -/
theorem p3q_se4 {m : ℕ} (hm : m = 4) (z : ℂ) :
    (fun q : ℝ => mathieuSe m z q - (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_BE 1 (N := 4) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (16 : ℂ) + ((1 : ℂ) / 30) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 12) * (q : ℂ)
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 20) * (q : ℂ)
      | 3 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 360))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((13 : ℂ) / 4800))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 28800))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 960))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((17 : ℂ) / 3600) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((17 : ℂ) / 3600) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => -((4549 : ℂ) / 69120000) + ((74783 : ℂ) / 373248000000) * (q : ℂ) ^ 2
        + ((289 : ℂ) / 11943936000000) * (q : ℂ) ^ 4)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((17 : ℂ) / 3600) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 4, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => ((1 : ℂ) / 12) * (q : ℂ)
        | 1 => (1 : ℂ)
        | 2 => -((1 : ℂ) / 20) * (q : ℂ)
        | 3 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.sin ((2 * (i : ℂ) + 2) * z) -
      (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => -((17 : ℂ) / 43200) * Complex.sin (2 * z)
        + ((17 : ℂ) / 72000) * Complex.sin (6 * z)
        - ((17 : ℂ) / 3456000) * Complex.sin (8 * z) * (q : ℂ))
      (fun q => by
        subst hm; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf
        simp only [Complex.sin_zero]
        ring_nf)
      (by fun_prop)
  subst hm
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.26 for `m = 5`: the expansion of `ce₅(z, q)` to `O(q³)`. -/
theorem p3q_ce5 {m : ℕ} (hm : m = 5) (z : ℂ) :
    (fun q : ℝ => mathieuCe m z q - (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_AO 2 (N := 5) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (25 : ℂ) + ((1 : ℂ) / 48) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
      | 1 => ((1 : ℂ) / 16) * (q : ℂ)
      | 2 => (1 : ℂ)
      | 3 => -((1 : ℂ) / 24) * (q : ℂ)
      | 4 => ((1 : ℂ) / 1344) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 5 := ⟨i - 5, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 384) - ((1 : ℂ) / 18432) * (q : ℂ))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 768))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((13 : ℂ) / 8064))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 64512))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 1344))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((13 : ℂ) / 4608) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((13 : ℂ) / 4608) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => -((5737 : ℂ) / 346816512) + ((8437 : ℂ) / 2397195730944) * (q : ℂ) ^ 2
        + ((8957 : ℂ) / 153420526780416) * (q : ℂ) ^ 4)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((13 : ℂ) / 4608) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 5, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
        | 1 => ((1 : ℂ) / 16) * (q : ℂ)
        | 2 => (1 : ℂ)
        | 3 => -((1 : ℂ) / 24) * (q : ℂ)
        | 4 => ((1 : ℂ) / 1344) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.cos ((2 * (i : ℂ) + 1) * z) -
      (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => -((13 : ℂ) / 73728) * Complex.cos (3 * z)
        + ((13 : ℂ) / 110592) * Complex.cos (7 * z)
        - ((13 : ℂ) / 1769472) * Complex.cos (1 * z) * (q : ℂ)
        - ((13 : ℂ) / 6193152) * Complex.cos (9 * z) * (q : ℂ))
      (fun q => by
        subst hm; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf)
      (by fun_prop)
  subst hm
  exact (h.add h2).congr_left fun q => by ring

/-- DLMF 28.6.27 for `m = 5`: the expansion of `se₅(z, q)` to `O(q³)`. -/
theorem p3q_se5 {m : ℕ} (hm : m = 5) (z : ℂ) :
    (fun q : ℝ => mathieuSe m z q - (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  have h := p3q_expand_BO 2 (N := 5) (K := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (p := fun q : ℝ => (25 : ℂ) + ((1 : ℂ) / 48) * (q : ℂ) ^ 2)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
      | 1 => ((1 : ℂ) / 16) * (q : ℂ)
      | 2 => (1 : ℂ)
      | 3 => -((1 : ℂ) / 24) * (q : ℂ)
      | 4 => ((1 : ℂ) / 1344) * (q : ℂ) ^ 2
      | _ => 0)
    (fun q i hi => by obtain ⟨j, rfl⟩ : ∃ j, i = j + 5 := ⟨i - 5, by omega⟩; rfl)
    (fun _ => rfl)
    (by intro i hi; interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop))
    (by
      intro i hi
      interval_cases i
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 384) - ((1 : ℂ) / 18432) * (q : ℂ))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 768))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((13 : ℂ) / 8064))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 64512))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 3) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 1344))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop))
    (c := fun q : ℝ => (1 : ℂ) - ((13 : ℂ) / 4608) * (q : ℂ) ^ 2)
    (by simpa using ((by fun_prop : Continuous fun q : ℝ =>
      (1 : ℂ) - ((13 : ℂ) / 4608) * (q : ℂ) ^ 2).tendsto 0))
    (p3q_isBigO_of_eq (e := 4) (by decide)
      (s := fun q : ℝ => -((5737 : ℂ) / 346816512) + ((8437 : ℂ) / 2397195730944) * (q : ℂ) ^ 2
        + ((8957 : ℂ) / 153420526780416) * (q : ℂ) ^ 4)
      (fun q => by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring)
      (by fun_prop)) z
  have h2 : (fun q : ℝ =>
      (fun q : ℝ => (1 : ℂ) - ((13 : ℂ) / 4608) * (q : ℂ) ^ 2) q *
      ∑ i ∈ Finset.range 5, (fun (q : ℝ) (i : ℕ) => match i with
        | 0 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2
        | 1 => ((1 : ℂ) / 16) * (q : ℂ)
        | 2 => (1 : ℂ)
        | 3 => -((1 : ℂ) / 24) * (q : ℂ)
        | 4 => ((1 : ℂ) / 1344) * (q : ℂ) ^ 2
        | _ => 0) q i * Complex.sin ((2 * (i : ℂ) + 1) * z) -
      (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q : ℝ => q ^ 3) :=
    p3q_isBigO_of_eq (e := 3) le_rfl
      (s := fun q : ℝ => -((13 : ℂ) / 73728) * Complex.sin (3 * z)
        + ((13 : ℂ) / 110592) * Complex.sin (7 * z)
        - ((13 : ℂ) / 1769472) * Complex.sin (1 * z) * (q : ℂ)
        - ((13 : ℂ) / 6193152) * Complex.sin (9 * z) * (q : ℂ))
      (fun q => by
        subst hm; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring_nf)
      (by fun_prop)
  subst hm
  exact (h.add h2).congr_left fun q => by ring

end DLMF.Mathieu
