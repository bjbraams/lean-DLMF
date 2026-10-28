/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Stirling
public import DLMF.BernoulliEuler.Explicit
public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Permutation cycles and excedances

Cycle notation, insertion bijections and excedance decompositions for finite permutations.

Source references and common attribution are retained in
`DLMF.Combinatorics.Permutations`.
-/

@[expose] public section

noncomputable section

open Finset Equiv

open Polynomial hiding bernoulli

namespace DLMF.Combinatorics

/-- The permutation (26.13.2), `1 2 3 4 5 6 7 8 ↦ 3 5 2 4 7 8 1 6`, in `0`-based form. -/
def dlmfExamplePerm : Perm (Fin 8) where
  toFun := ![2, 4, 1, 3, 6, 7, 0, 5]
  invFun := ![6, 2, 0, 3, 1, 7, 4, 5]
  left_inv := by decide
  right_inv := by decide

/-- (26.13.2): the example permutation is `(1,3,2,5,7)(4)(6,8)` in cycle notation (`0`-based:
`c[0, 2, 1, 4, 6] * c[5, 7]`, the fixed point dropped). -/
@[dlmf 26.13.E2]
theorem dlmfExamplePerm_eq_cycles : dlmfExamplePerm = c[0, 2, 1, 4, 6] * c[5, 7] := by
  decide

/-- The number of cycles of `σ`, fixed points included: the length of its cycle type
`(a_1, …, a_n)` counted with multiplicity, `a_1 + ⋯ + a_n`. -/
@[dlmf 26.13]
def numCycles {n : ℕ} (σ : Perm (Fin n)) : ℕ := σ.partition.parts.card

/-- (26.13.3): the Stirling cycle number `[n k]`, the number of permutations of `{1, …, n}` with
exactly `k` cycles, is `|s(n, k)|`, with DLMF's signed `s(n, k)` = ACQ26A's
`signedStirlingFirst n k`. The count itself is `card_perm_numCycles` (§26.8(i), in
`DLMF.Combinatorics.Stirling`): Mathlib's unsigned `Nat.stirlingFirst n k`. -/
@[dlmf 26.13.E3]
theorem card_numCycles_eq_abs_signedStirlingFirst (n k : ℕ) :
    (#{σ : Perm (Fin n) | numCycles σ = k} : ℤ) = |signedStirlingFirst n k| := by
  have h := card_perm_numCycles n k
  unfold numCycles
  rw [h, signedStirlingFirst, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]

/-- (26.13.4), first form: `d(n) = n! ∑_{j=0}^n (-1)^j/j!`; `d(n)` is Mathlib's
`numDerangements n`, the number of fixed-point-free permutations
(`card_derangements_eq_numDerangements`). -/
@[dlmf 26.13.E4]
theorem numDerangements_eq_factorial_mul_sum (n : ℕ) :
    (numDerangements n : ℚ) = n.factorial * ∑ j ∈ range (n + 1), (-1 : ℚ) ^ j / j.factorial := by
  have h := numDerangements_sum n
  have h' : (numDerangements n : ℚ) = ((numDerangements n : ℤ) : ℚ) := by push_cast; rfl
  rw [h', h, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp only [mem_range] at hk; omega
  have hfac := Nat.factorial_mul_ascFactorial k (n - k)
  rw [Nat.add_sub_cancel' hk'] at hfac
  have hf : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [← hfac]
  push_cast
  field_simp

/-- (26.13.4), second form, corrected range: `d(n) = ⌊(n! + e - 2)/e⌋` for `n ≥ 1` (at `n = 0`
the right side is `0`, while `d(0) = 1`). -/
@[dlmf 26.13.E4 "domain: n ≥ 1 (fails at n = 0)"]
theorem numDerangements_eq_floor {n : ℕ} (hn : 1 ≤ n) :
    (numDerangements n : ℤ) = ⌊(n.factorial + Real.exp 1 - 2) / Real.exp 1⌋ := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [eq_comm, Int.floor_eq_iff]
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | rfl | h4
  · have : numDerangements 1 = 0 := by decide
    rw [this]; push_cast
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_lt_iff₀ hepos]; norm_num [Nat.factorial]; linarith
  · have : numDerangements 2 = 1 := by decide
    rw [this]; push_cast
    norm_num [Nat.factorial, div_self hepos.ne']
  · have : numDerangements 3 = 2 := by decide
    rw [this]; push_cast
    norm_num [Nat.factorial]
    constructor
    · rw [le_div_iff₀ hepos]; linarith
    · rw [div_lt_iff₀ hepos]; linarith
  · -- the remainder `n!/e - d(n)` is at most `(n+2)/(n+1)^2 ≤ 6/25` in absolute value
    have hd : (numDerangements n : ℝ) =
        n.factorial * ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j / j.factorial := by
      have := numDerangements_eq_factorial_mul_sum n
      have h' := congrArg (fun x : ℚ => (x : ℝ)) this
      push_cast at h'
      exact h'
    have hb := Real.exp_bound (x := -1) (by norm_num) (n := n + 1) (by omega)
    simp only [abs_neg, abs_one, one_pow, one_mul] at hb
    have hexp : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    rw [hexp] at hb
    set R := (n.factorial : ℝ) / Real.exp 1 - numDerangements n with hR
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hRb : |R| ≤ (n + 2) / ((n + 1) * (n + 1)) := by
      have : R = n.factorial * ((Real.exp 1)⁻¹ -
          ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i / i.factorial) := by
        rw [hR, hd]; ring
      rw [this, abs_mul, abs_of_pos hfac]
      calc (n.factorial : ℝ) * |(Real.exp 1)⁻¹ - ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i / i.factorial|
          ≤ n.factorial * (((n + 1).succ : ℕ) / ((n + 1).factorial * ((n + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hb hfac.le
        _ = (n + 2) / ((n + 1) * (n + 1)) := by
            rw [Nat.factorial_succ]; push_cast; field_simp; ring
    have hsmall : (n + 2 : ℝ) / ((n + 1) * (n + 1)) ≤ 6 / 25 := by
      have h4' : (4 : ℝ) ≤ n := by exact_mod_cast h4
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hR1 := (abs_le.mp (hRb.trans hsmall))
    have hy : ((n.factorial : ℝ) + Real.exp 1 - 2) / Real.exp 1 =
        numDerangements n + R + 1 - 2 / Real.exp 1 := by
      rw [hR]; field_simp; ring
    rw [hy]
    have h2e1 : 2 / Real.exp 1 < 0.7358 := by rw [div_lt_iff₀ hepos]; linarith
    have h2e2 : 0.7357 < 2 / Real.exp 1 := by rw [lt_div_iff₀ hepos]; linarith
    push_cast
    constructor <;> linarith [hR1.1, hR1.2]

/-- (26.13.5): a cycle `(j_1, j_2, …, j_k)` (the permutation `j_i ↦ j_{i+1}`, `j_k ↦ j_1`,
Mathlib's `List.formPerm`) is the product `(j_1, j_2)(j_2, j_3)⋯(j_{k-1}, j_k)` of `k - 1`
transpositions (composition read from right to left). -/
@[dlmf 26.13.E5]
theorem formPerm_eq_prod_swap {α : Type*} [DecidableEq α] (l : List α) :
    l.formPerm = (List.zipWith Equiv.swap l l.tail).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => simp
    | cons y l =>
      rw [List.formPerm_cons_cons, ih]
      simp [List.zipWith_cons_cons, List.prod_cons]

/-- §26.13: a permutation with cycle type `(a_1, …, a_n)` is a product of
`n - (a_1 + ⋯ + a_n)` transpositions, and of no fewer. Proof: TauCeti's
`Equiv.Perm.isLeast_card_sub_orbitCount` (orbits counted with `TauCeti.orbitCount`). -/
@[dlmf 26.13]
theorem exists_swap_factorization_numCycles {n : ℕ} (σ : Perm (Fin n)) :
    (∃ l : List (Perm (Fin n)), (∀ τ ∈ l, τ.IsSwap) ∧ l.prod = σ ∧ l.length = n - numCycles σ) ∧
      ∀ l : List (Perm (Fin n)), (∀ τ ∈ l, τ.IsSwap) → l.prod = σ → n - numCycles σ ≤ l.length := by
  -- TauCeti's reflection length `Equiv.Perm.isLeast_card_sub_orbitCount`
  have h := σ.isLeast_card_sub_orbitCount
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, σ.orbitCount_eq_card_parts_partition] at h
  exact ⟨h.1, fun l hl hp => h.2 ⟨l, hl, hp, rfl⟩⟩

/-- §26.13, the example: `(1,3,2,5,7)(6,8) = (1,3)(2,3)(2,5)(5,7)(6,8)` (`0`-based). -/
@[dlmf 26.13]
theorem dlmfExamplePerm_eq_swaps :
    dlmfExamplePerm = swap 0 2 * swap 1 2 * swap 1 4 * swap 4 6 * swap 5 7 := by
  decide

/-- (26.13.6): for `j < k`, `(j, k) = (k-1, k)(k-2, k-1)⋯(j+1, j+2)(j, j+1)(j+1, j+2)⋯(k-1, k)`,
a product of `2k - 2j - 1` adjacent transpositions (stated in `Perm ℕ`; a permutation of
`{1, …, n}` is a permutation of `ℕ` fixing the other points). -/
@[dlmf 26.13.E6]
theorem swap_eq_prod_adjacent {j k : ℕ} (hjk : j < k) :
    swap j k = ((List.range' (j + 1) (k - j - 1)).reverse.map fun i => swap i (i + 1)).prod *
      swap j (j + 1) * ((List.range' (j + 1) (k - j - 1)).map fun i => swap i (i + 1)).prod := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + 1 + d := ⟨k - j - 1, by omega⟩
  clear hjk
  induction d with
  | zero => simp
  | succ d ih =>
    have hr : List.range' (j + 1) (j + 1 + (d + 1) - j - 1) =
        List.range' (j + 1) (j + 1 + d - j - 1) ++ [j + 1 + d] := by
      rw [show j + 1 + (d + 1) - j - 1 = (j + 1 + d - j - 1) + 1 by omega, List.range'_concat]
      congr 2; omega
    rw [hr, List.reverse_append, List.map_append, List.map_append, List.prod_append,
      List.prod_append]
    simp only [List.reverse_singleton, List.map_singleton, List.prod_cons, List.prod_nil, mul_one]
    have hconj : swap j (j + 1 + (d + 1)) =
        swap (j + 1 + d) (j + 1 + d + 1) * swap j (j + 1 + d) *
          swap (j + 1 + d) (j + 1 + d + 1) := by
      rw [swap_mul_swap_mul_swap (by omega) (by omega), swap_comm]
      congr 1
    rw [hconj, ih]
    simp only [mul_assoc]

/-- An adjacent transposition of `{1, …, n}`: `(a, a+1)`. -/
def IsAdjacentSwap {n : ℕ} (τ : Perm (Fin n)) : Prop :=
  ∃ a b : Fin n, (b : ℕ) = a + 1 ∧ τ = swap a b

/-! ### §26.14 Order notation -/

/-- The inversion number of a word `w`: pairs of positions `j < k` with `w j > w k`
((26.14.1); extended to multiset permutations in §26.16). -/
@[dlmf 26.14.E1]
def wordInversions {n : ℕ} (w : Fin n → ℕ) : ℕ := #{p : Fin n × Fin n | p.1 < p.2 ∧ w p.2 < w p.1}

/-- The descent positions of a word `w` (`0`-based): `j` with `w j > w (j+1)`. -/
@[dlmf 26.14.i]
def wordDescentSet {n : ℕ} (w : Fin n → ℕ) : Finset ℕ :=
  (range n).filter fun j => ∃ h : j + 1 < n, w ⟨j + 1, h⟩ < w ⟨j, by omega⟩

/-- The major index (26.14.2): the sum of the (`1`-based) positions of the first elements of
the descents. -/
@[dlmf 26.14.E2]
def wordMajorIndex {n : ℕ} (w : Fin n → ℕ) : ℕ := ∑ j ∈ wordDescentSet w, (j + 1)

/-- `inv(σ)` (26.14.1). -/
@[dlmf 26.14.E1]
def inversionNumber {n : ℕ} (σ : Perm (Fin n)) : ℕ := wordInversions fun i => (σ i : ℕ)

/-- The number of descents of `σ`. -/
@[dlmf 26.14.i]
def descentNumber {n : ℕ} (σ : Perm (Fin n)) : ℕ := #(wordDescentSet fun i => (σ i : ℕ))

/-- `maj(σ)` (26.14.2). -/
@[dlmf 26.14.E2]
def majorIndex {n : ℕ} (σ : Perm (Fin n)) : ℕ := wordMajorIndex fun i => (σ i : ℕ)

/-- §26.13 and §26.14(i), the example `35247816`: `inv = 11`, the descents are `52` and `81`,
`maj = 2 + 6 = 8`. -/
@[dlmf 26.14.i]
theorem dlmfExamplePerm_stats :
    inversionNumber dlmfExamplePerm = 11 ∧ descentNumber dlmfExamplePerm = 2 ∧
      majorIndex dlmfExamplePerm = 8 := by
  decide

/-! ### Insertion bijections (proof round 2) -/

/-- Membership in the descent set of a permutation. -/
lemma q26b_mem_descentSet {n : ℕ} (σ : Perm (Fin n)) (j : ℕ) :
    j ∈ wordDescentSet (fun i => (σ i : ℕ)) ↔ ∃ h : j + 1 < n, σ ⟨j + 1, h⟩ < σ ⟨j, by omega⟩ := by
  simp only [wordDescentSet, mem_filter, mem_range, Fin.lt_def]
  constructor
  · rintro ⟨-, h, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨by omega, h, h'⟩

/-- The only permutation without descents is the identity. -/
lemma q26b_descentNumber_eq_zero_iff {n : ℕ} (σ : Perm (Fin n)) : descentNumber σ = 0 ↔ σ = 1 := by
  constructor
  · intro h
    have hD : ∀ j (hj : j + 1 < n), σ ⟨j, by omega⟩ < σ ⟨j + 1, hj⟩ := by
      intro j hj
      have hj' : j ∉ wordDescentSet (fun i => (σ i : ℕ)) := by
        rw [descentNumber, Finset.card_eq_zero] at h; rw [h]; exact Finset.notMem_empty j
      rw [q26b_mem_descentSet] at hj'
      have hj'' : ∀ h : j + 1 < n, σ ⟨j, by omega⟩ ≤ σ ⟨j + 1, h⟩ :=
        fun h => not_lt.mp fun h' => hj' ⟨h, h'⟩
      have hne : σ ⟨j, by omega⟩ ≠ σ ⟨j + 1, hj⟩ := fun h' => by
        have := σ.injective h'; simp [Fin.ext_iff] at this
      exact lt_of_le_of_ne (hj'' hj) hne
    rcases n with _ | m
    · exact Subsingleton.elim _ _
    have hmono : StrictMono σ := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      exact hD i (by omega)
    have := hmono.range_inj_of_wellFoundedLT strictMono_id
    have h2 : (⇑σ : Fin (m + 1) → Fin (m + 1)) = id := this.mp (by simp)
    exact Equiv.ext fun i => congrFun h2 i
  · rintro rfl
    rw [descentNumber, Finset.card_eq_zero]
    refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
    obtain ⟨h, h'⟩ := (q26b_mem_descentSet _ j).1 hj
    simp only [Perm.one_apply, Fin.mk_lt_mk] at h'
    omega

/-- A permutation of `Fin n` has at most `n - 1` descents. -/
lemma q26b_descentNumber_le {n : ℕ} (σ : Perm (Fin n)) : descentNumber σ ≤ n - 1 := by
  unfold descentNumber
  have hsub : wordDescentSet (fun i => (σ i : ℕ)) ⊆ range (n - 1) := by
    intro j hj
    simp only [wordDescentSet, mem_filter, mem_range] at hj
    obtain ⟨_, h, _⟩ := hj
    simp only [mem_range]; omega
  simpa using card_le_card hsub

/-- The descents of `rev ∘ σ` are the ascents of `σ`. -/
lemma q26b_descentNumber_rev {n : ℕ} (σ : Perm (Fin n)) :
    descentNumber (Fin.revPerm * σ) = n - 1 - descentNumber σ := by
  have hsub : wordDescentSet (fun i => (σ i : ℕ)) ⊆ range (n - 1) := by
    intro j hj
    obtain ⟨h, -⟩ := (q26b_mem_descentSet σ j).1 hj
    simp only [mem_range]; omega
  have hset : wordDescentSet (fun i => ((Fin.revPerm * σ : Perm (Fin n)) i : ℕ)) =
      range (n - 1) \ wordDescentSet (fun i => (σ i : ℕ)) := by
    ext j
    rw [q26b_mem_descentSet, mem_sdiff, q26b_mem_descentSet, mem_range]
    simp only [Perm.coe_mul, Function.comp_apply, Fin.revPerm_apply, Fin.rev_lt_rev, not_exists]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨by omega, fun _ h'' => absurd (h'.trans h'') (lt_irrefl _)⟩
    · rintro ⟨h, h'⟩
      have hj : j + 1 < n := by omega
      refine ⟨hj, ?_⟩
      have := not_lt.mp (h' hj)
      have hne : σ ⟨j, by omega⟩ ≠ σ ⟨j + 1, hj⟩ := fun h'' => by
        have := σ.injective h''; simp [Fin.ext_iff] at this
      exact lt_of_le_of_ne this hne
  rw [descentNumber, hset, card_sdiff_of_subset hsub, card_range]
  rfl

/-- The inversion number as a sum over pairs of positions. -/
lemma r26b_inversionNumber_eq_sum_pair {n : ℕ} (σ : Perm (Fin n)) :
    inversionNumber σ = ∑ x : Fin n × Fin n, if x.1 < x.2 ∧ σ x.2 < σ x.1 then 1 else 0 := by
  rw [inversionNumber, wordInversions, card_filter]
  simp only [Fin.val_fin_lt]

/-- An adjacent transposition on the right changes the inversion number by `±1`. -/
lemma r26b_inversionNumber_mul_swap {n : ℕ} (σ : Perm (Fin n)) {a b : Fin n}
    (hab : (b : ℕ) = a + 1) :
    inversionNumber (σ * swap a b) + (if σ b < σ a then 1 else 0) =
      inversionNumber σ + (if σ a < σ b then 1 else 0) := by
  rw [r26b_inversionNumber_eq_sum_pair, r26b_inversionNumber_eq_sum_pair]
  set s := swap a b
  rw [← (Equiv.prodCongr s s).sum_comp]
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Perm.coe_mul, Function.comp_apply]
  have hss : ∀ x, s (s x) = x := fun x => swap_apply_self a b x
  simp only [hss]
  have hpt : ∀ x : Fin n × Fin n,
      (if s x.1 < s x.2 ∧ σ x.2 < σ x.1 then 1 else 0) +
        (if x = (a, b) ∧ σ b < σ a then 1 else 0) =
      (if x.1 < x.2 ∧ σ x.2 < σ x.1 then 1 else 0) +
        (if x = (b, a) ∧ σ a < σ b then 1 else 0) := by
    rintro ⟨p, q⟩
    have hne : a ≠ b := fun h => by rw [h] at hab; omega
    by_cases h1 : (p, q) = (a, b)
    · simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have : ¬ (p, q) = (q, p) := fun h => hne (Prod.mk.inj h).1
      simp only [s, swap_apply_left, swap_apply_right, this, false_and, ite_false, true_and,
        add_zero]
      have hpq : p < q := by rw [Fin.lt_def]; omega
      simp [hpq, not_lt.mpr hpq.le]
    by_cases h2 : (p, q) = (b, a)
    · simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp only [s, swap_apply_left, swap_apply_right, h1, false_and, ite_false, true_and,
        add_zero]
      have hpq : q < p := by rw [Fin.lt_def]; omega
      simp [hpq, not_lt.mpr hpq.le]
    simp only [h1, h2, false_and, ite_false, add_zero]
    have key : s p < s q ↔ p < q := by
      simp only [s, swap_apply_def, Fin.lt_def]
      simp only [Prod.mk.injEq, not_and] at h1 h2
      split_ifs with c1 c2 c3 c4 c5 c6 c7 c8 <;> simp only [Fin.ext_iff] at * <;> omega
    simp only [key]
  have := Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset (Fin n × Fin n))) => hpt x
  rw [sum_add_distrib, sum_add_distrib] at this
  simp only [ite_and, sum_ite_eq', mem_univ, ite_true] at this
  simpa only [ite_and] using this

/-- `inv(σ⁻¹) = inv(σ)`. -/
lemma r26b_inversionNumber_inv {n : ℕ} (σ : Perm (Fin n)) :
    inversionNumber σ⁻¹ = inversionNumber σ := by
  unfold inversionNumber wordInversions
  refine card_bij (fun x _ => (σ⁻¹ x.2, σ⁻¹ x.1)) ?_ ?_ ?_
  · rintro ⟨p, q⟩ h
    simp only [mem_filter, mem_univ, true_and, Fin.val_fin_lt] at h ⊢
    exact ⟨h.2, by simpa using h.1⟩
  · rintro ⟨p, q⟩ _ ⟨p', q'⟩ _ h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    rw [h.1, h.2]
  · rintro ⟨p, q⟩ h
    refine ⟨(σ q, σ p), ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, Fin.val_fin_lt] at h ⊢
    exact ⟨by simpa using h.2, by simpa using h.1⟩

/-- An adjacent transposition is an involution. -/
lemma r26b_isAdjacentSwap_inv {n : ℕ} {τ : Perm (Fin n)} (h : IsAdjacentSwap τ) : τ⁻¹ = τ := by
  obtain ⟨a, b, -, rfl⟩ := h
  exact swap_inv a b

/-- Right multiplication by an adjacent transposition raises `inv` by at most one. -/
lemma r26b_inversionNumber_mul_adj_le {n : ℕ} (σ : Perm (Fin n)) {τ : Perm (Fin n)}
    (hτ : IsAdjacentSwap τ) : inversionNumber (σ * τ) ≤ inversionNumber σ + 1 := by
  obtain ⟨a, b, hab, rfl⟩ := hτ
  have := r26b_inversionNumber_mul_swap σ hab
  split_ifs at this <;> omega

/-- §26.13: the inversion number is the least number of adjacent transpositions whose product
is `σ`. -/
@[dlmf 26.13]
theorem inversionNumber_eq_min_adjacent {n : ℕ} (σ : Perm (Fin n)) :
    (∃ l : List (Perm (Fin n)), (∀ τ ∈ l, IsAdjacentSwap τ) ∧ l.prod = σ ∧
        l.length = inversionNumber σ) ∧
      ∀ l : List (Perm (Fin n)), (∀ τ ∈ l, IsAdjacentSwap τ) → l.prod = σ →
        inversionNumber σ ≤ l.length := by
  refine ⟨?_, ?_⟩
  · induction h : inversionNumber σ generalizing σ with
    | zero =>
      refine ⟨[], by simp, ?_, rfl⟩
      by_contra hne
      have hd : descentNumber σ ≠ 0 := fun h' => hne ((q26b_descentNumber_eq_zero_iff σ).1 h').symm
      obtain ⟨j, hj⟩ := Finset.card_ne_zero.mp hd
      obtain ⟨hj1, hj2⟩ := (q26b_mem_descentSet σ j).1 hj
      have : 0 < inversionNumber σ := by
        unfold inversionNumber wordInversions
        exact card_pos.mpr ⟨(⟨j, by omega⟩, ⟨j + 1, hj1⟩),
          mem_filter.mpr ⟨mem_univ _, by simp [Fin.lt_def], hj2⟩⟩
      omega
    | succ m ih =>
      have hne : σ ≠ 1 := fun h' => by
        subst h'
        have : inversionNumber (1 : Perm (Fin n)) = 0 := by
          unfold inversionNumber wordInversions
          rw [card_eq_zero, filter_eq_empty_iff]
          rintro ⟨p, q⟩ _ ⟨h1, h2⟩
          simp only [Perm.one_apply, Fin.val_fin_lt] at h1 h2
          exact absurd (h1.trans h2) (lt_irrefl _)
        omega
      have hd : descentNumber σ ≠ 0 := fun h' => hne ((q26b_descentNumber_eq_zero_iff σ).1 h')
      obtain ⟨j, hj⟩ := Finset.card_ne_zero.mp hd
      obtain ⟨hj1, hj2⟩ := (q26b_mem_descentSet σ j).1 hj
      set a : Fin n := ⟨j, by omega⟩
      set b : Fin n := ⟨j + 1, hj1⟩
      have hab : (b : ℕ) = a + 1 := rfl
      have key := r26b_inversionNumber_mul_swap σ hab
      have hba : σ b < σ a := hj2
      rw [ite_eq_left hba, ite_eq_right (not_lt.mpr hba.le), h] at key
      obtain ⟨l, hl1, hl2, hl3⟩ := ih (σ * swap a b) (by omega)
      refine ⟨l ++ [swap a b], ?_, ?_, ?_⟩
      · intro τ hτ
        rcases List.mem_append.mp hτ with hτ | hτ
        · exact hl1 τ hτ
        · rw [List.mem_singleton.mp hτ]; exact ⟨a, b, hab, rfl⟩
      · rw [List.prod_append, hl2]; simp
      · simp [hl3]
  · intro l
    induction l generalizing σ with
    | nil =>
      intro _ h
      simp only [List.prod_nil] at h
      subst h
      unfold inversionNumber wordInversions
      simp only [List.length_nil, nonpos_iff_eq_zero, card_eq_zero, filter_eq_empty_iff]
      rintro ⟨p, q⟩ _ ⟨h1, h2⟩
      simp only [Perm.one_apply, Fin.val_fin_lt] at h1 h2
      exact absurd (h1.trans h2) (lt_irrefl _)
    | cons τ l ih =>
      intro hl h
      simp only [List.prod_cons] at h
      have hτ := hl τ (List.mem_cons_self ..)
      have h1 := ih l.prod (fun τ' h' => hl τ' (List.mem_cons_of_mem _ h')) rfl
      rw [← h, ← r26b_inversionNumber_inv, mul_inv_rev, r26b_isAdjacentSwap_inv hτ]
      have h2 := r26b_inversionNumber_mul_adj_le (l.prod)⁻¹ hτ
      rw [r26b_inversionNumber_inv] at h2
      simp only [List.length_cons]
      omega

/-- The Eulerian number `⟨n k⟩`: permutations of `{1, …, n}` with exactly `k` descents
(DLMF §26.14(i)). -/
@[dlmf 26.14.i]
def eulerianNumber (n k : ℕ) : ℕ := #{σ : Perm (Fin n) | descentNumber σ = k}

/-- The number of excedances `σ(j) > j` of `σ`. -/
def excedanceNumber {n : ℕ} (σ : Perm (Fin n)) : ℕ := #{j : Fin n | j < σ j}

/-- The number of weak excedances `σ(j) ≥ j` of `σ`. -/
def weakExcedanceNumber {n : ℕ} (σ : Perm (Fin n)) : ℕ := #{j : Fin n | j ≤ σ j}

/-- Insertion of the letter `0` at position `p` into the word `σ + 1`. -/
noncomputable def r26b_insMin {n : ℕ} : Fin (n + 2) × Perm (Fin (n + 1)) ≃ Perm (Fin (n + 2)) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.inv _)).trans
    (Perm.decomposeFin'.symm.trans (Equiv.inv _))

/-- The inserted letter `0` sits at position `p`. -/
lemma r26b_insMin_same {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    r26b_insMin (p, σ) p = 0 := by
  simp [r26b_insMin]

/-- The other letters are those of `σ`, shifted up by one. -/
lemma r26b_insMin_succAbove {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) (m : Fin (n + 1)) :
    r26b_insMin (p, σ) (p.succAbove m) = (σ m).succ := by
  have := Perm.decomposeFin'Symm_symm_succAbove p σ⁻¹ (σ m)
  rw [show σ⁻¹ (σ m) = m from σ.symm_apply_apply m] at this
  simpa [r26b_insMin] using this

/-- Letters before the insertion position. -/
lemma r26b_insMin_lt {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) {j : ℕ} (hj : j < p) :
    r26b_insMin (p, σ) ⟨j, by omega⟩ = (σ ⟨j, by omega⟩).succ := by
  have h : (⟨j, by omega⟩ : Fin (n + 2)) = p.succAbove ⟨j, by omega⟩ := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, hj])]; rfl
  rw [h, r26b_insMin_succAbove]

/-- Letters after the insertion position. -/
lemma r26b_insMin_gt {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) {j : ℕ} (hj : p < j)
    (hjn : j < n + 2) :
    r26b_insMin (p, σ) ⟨j, hjn⟩ = (σ ⟨j - 1, by omega⟩).succ := by
  have h : (⟨j, hjn⟩ : Fin (n + 2)) = p.succAbove ⟨j - 1, by omega⟩ := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
    ext; simp; omega
  rw [h, r26b_insMin_succAbove]

/-- The letter at the insertion position. -/
lemma r26b_insMin_eq {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) {j : ℕ} (hj : j = p)
    (hjn : j < n + 2) : r26b_insMin (p, σ) ⟨j, hjn⟩ = 0 := by
  have h : (⟨j, hjn⟩ : Fin (n + 2)) = p := Fin.ext hj
  rw [h, r26b_insMin_same]

/-- The descent indicator of a word at a natural position. -/
def r26b_dInd {N : ℕ} (w : Fin N → ℕ) (j : ℕ) : ℕ := if j ∈ wordDescentSet w then 1 else 0

/-- The descent indicator after inserting the minimum at position `p`. -/
lemma r26b_dInd_insMin {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) (j : ℕ) :
    r26b_dInd (fun i => (r26b_insMin (p, σ) i : ℕ)) j =
      if j + 1 < p then r26b_dInd (fun i => (σ i : ℕ)) j else if j + 1 = p then 1
      else if j = p then 0 else r26b_dInd (fun i => (σ i : ℕ)) (j - 1) := by
  set τ := r26b_insMin (p, σ)
  have hp := p.isLt
  by_cases h1 : j + 1 < p
  · rw [ite_eq_left h1]
    unfold r26b_dInd
    congr 1
    simp only [q26b_mem_descentSet, eq_iff_iff]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨by omega, ?_⟩
      rwa [r26b_insMin_lt p σ h1, r26b_insMin_lt p σ (by omega), Fin.succ_lt_succ_iff] at h'
    · rintro ⟨h, h'⟩
      refine ⟨by omega, ?_⟩
      rwa [r26b_insMin_lt p σ h1, r26b_insMin_lt p σ (by omega), Fin.succ_lt_succ_iff]
  rw [ite_eq_right h1]
  by_cases h2 : j + 1 = p
  · rw [ite_eq_left h2, r26b_dInd, ite_eq_left]
    rw [q26b_mem_descentSet]
    refine ⟨by omega, ?_⟩
    rw [r26b_insMin_eq p σ h2, r26b_insMin_lt p σ (by omega)]
    exact Fin.succ_pos _
  rw [ite_eq_right h2]
  by_cases h3 : j = p
  · rw [ite_eq_left h3, r26b_dInd, ite_eq_right]
    rw [q26b_mem_descentSet]
    rintro ⟨h, h'⟩
    rw [r26b_insMin_eq p σ h3] at h'
    exact absurd h' (Fin.not_lt_zero _)
  rw [ite_eq_right h3]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold r26b_dInd
  congr 1
  simp only [q26b_mem_descentSet, eq_iff_iff]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨by omega, ?_⟩
    rwa [r26b_insMin_gt p σ (by omega) h, r26b_insMin_gt p σ (by omega), Fin.succ_lt_succ_iff]
      at h'
  · rintro ⟨h, h'⟩
    refine ⟨by omega, ?_⟩
    rwa [r26b_insMin_gt p σ (by omega) (by omega), r26b_insMin_gt p σ (by omega),
      Fin.succ_lt_succ_iff]

/-- Descent positions of a word of length `N` are below `N - 1`. -/
lemma r26b_wordDescentSet_subset {N : ℕ} (w : Fin N → ℕ) : wordDescentSet w ⊆ range (N - 1) := by
  intro j hj
  simp only [wordDescentSet, mem_filter, mem_range] at hj
  obtain ⟨_, h, _⟩ := hj
  simp only [mem_range]; omega

/-- A weighted sum over the descent set as a sum of indicators. -/
lemma r26b_sum_descentSet {N M : ℕ} (w : Fin N → ℕ) (hM : N ≤ M + 1) (f : ℕ → ℕ) :
    ∑ j ∈ wordDescentSet w, f j = ∑ j ∈ range M, r26b_dInd w j * f j := by
  have hsub : wordDescentSet w ⊆ range M :=
    (r26b_wordDescentSet_subset w).trans (range_subset_range.mpr (by omega))
  rw [← Finset.sum_subset hsub (f := fun j => r26b_dInd w j * f j)]
  · refine sum_congr rfl fun j hj => ?_
    simp [r26b_dInd, hj]
  · intro j _ hj
    simp [r26b_dInd, hj]

/-- No descent at or beyond the last position. -/
lemma r26b_dInd_eq_zero {N : ℕ} (w : Fin N → ℕ) {j : ℕ} (hj : N ≤ j + 1) : r26b_dInd w j = 0 := by
  have : j ∉ wordDescentSet w := fun h => by
    have := mem_range.mp (r26b_wordDescentSet_subset w h); omega
  simp [r26b_dInd, this]

/-- Weighted descent sums under insertion of the minimum. -/
lemma r26b_sum_descentSet_insMin {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) (f : ℕ → ℕ) :
    ∑ j ∈ wordDescentSet (fun i => (r26b_insMin (p, σ) i : ℕ)), f j +
        (if 1 ≤ (p : ℕ) then r26b_dInd (fun i => (σ i : ℕ)) (p - 1) * f (p - 1) else 0) =
      ∑ j ∈ wordDescentSet (fun i => (σ i : ℕ)), (if j < p then f j else f (j + 1)) +
        (if 1 ≤ (p : ℕ) then f (p - 1) else 0) := by
  have hp := p.isLt
  set d := r26b_dInd (fun i => (σ i : ℕ))
  rw [r26b_sum_descentSet _ (M := n + 2) (by omega), r26b_sum_descentSet _ (M := n + 1) (by omega)]
  have e1 : ∀ j, r26b_dInd (fun i => (r26b_insMin (p, σ) i : ℕ)) j * f j =
      (if j + 1 < p then d j * f j else 0) + (if j = p - 1 ∧ 1 ≤ (p : ℕ) then f j else 0) +
        (if p < j then d (j - 1) * f j else 0) := by
    intro j
    rw [r26b_dInd_insMin]
    split_ifs <;> first | omega | simp [d]
  have e2 : ∀ j, d j * (if j < p then f j else f (j + 1)) =
      (if j + 1 < p then d j * f j else 0) + (if j = p - 1 ∧ 1 ≤ (p : ℕ) then d j * f j else 0) +
        (if (p : ℕ) ≤ j then d j * f (j + 1) else 0) := by
    intro j
    split_ifs <;> omega
  rw [sum_congr rfl fun j _ => e1 j, sum_congr rfl fun j _ => e2 j]
  simp only [sum_add_distrib]
  have h3 : ∑ j ∈ range (n + 2), (if p < j then d (j - 1) * f j else 0) =
      ∑ j ∈ range (n + 1), (if (p : ℕ) ≤ j then d j * f (j + 1) else 0) := by
    rw [sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.not_lt_zero, ite_false, add_zero]
    exact sum_congr rfl fun j _ => by congr 1; exact propext ⟨fun h => by omega, fun h => by omega⟩
  have h1 : ∑ j ∈ range (n + 2), (if j + 1 < p then d j * f j else 0) =
      ∑ j ∈ range (n + 1), (if j + 1 < p then d j * f j else 0) := by
    rw [sum_range_succ, ite_eq_right (by omega), add_zero]
  have h2 : ∀ g : ℕ → ℕ, ∀ M, (p : ℕ) ≤ M →
      ∑ j ∈ range M, (if j = p - 1 ∧ 1 ≤ (p : ℕ) then g j else 0) =
        if 1 ≤ (p : ℕ) then g (p - 1) else 0 := by
    intro g M hM
    split_ifs with hp1
    · simp only [hp1, and_true]
      rw [Finset.sum_ite_eq']
      rw [ite_eq_left (by simp; omega)]
    · exact sum_eq_zero fun j _ => ite_eq_right (by omega)
  rw [h3, h1, h2 _ _ (by omega), h2 _ _ (by omega)]
  split_ifs <;> ring

/-- The descent indicator is `0` or `1`. -/
lemma r26b_dInd_le_one {N : ℕ} (w : Fin N → ℕ) (j : ℕ) : r26b_dInd w j ≤ 1 := by
  unfold r26b_dInd; split_ifs <;> omega

/-- The descent number after inserting the minimum at position `p`. -/
lemma r26b_descentNumber_insMin {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    descentNumber (r26b_insMin (p, σ)) = descentNumber σ +
      (if 1 ≤ (p : ℕ) ∧ r26b_dInd (fun i => (σ i : ℕ)) (p - 1) = 0 then 1 else 0) := by
  have h := r26b_sum_descentSet_insMin p σ (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one, ite_self] at h
  have h1 := r26b_dInd_le_one (fun i => (σ i : ℕ)) (p - 1)
  unfold descentNumber
  split_ifs at h ⊢ with h2 h3 h3 <;> omega

/-- The descent number as a sum of descent indicators. -/
lemma r26b_sum_dInd_perm {n : ℕ} (σ : Perm (Fin n)) :
    ∑ j ∈ range n, r26b_dInd (fun i => (σ i : ℕ)) j = descentNumber σ := by
  have := r26b_sum_descentSet (fun i => (σ i : ℕ)) (M := n) (by omega) (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at this
  exact this.symm

/-- The number of insertion positions giving `K` descents. -/
lemma r26b_card_insMin_descent {n : ℕ} (σ : Perm (Fin (n + 1))) (K : ℕ) :
    #{p : Fin (n + 2) | descentNumber (r26b_insMin (p, σ)) = K} =
      (if descentNumber σ = K then descentNumber σ + 1 else 0) +
        (if descentNumber σ + 1 = K then n + 1 - descentNumber σ else 0) := by
  set d := r26b_dInd (fun i => (σ i : ℕ))
  set h : ℕ → ℕ := fun p => if 1 ≤ p ∧ d (p - 1) = 0 then 1 else 0 with hh
  have hle : ∀ p, h p ≤ 1 := fun p => by simp only [hh]; split_ifs <;> omega
  rw [card_filter]
  simp_rw [r26b_descentNumber_insMin]
  rw [Fin.sum_univ_eq_sum_range (fun p => if descentNumber σ + h p = K then 1 else 0)]
  have hpt : ∀ p, (if descentNumber σ + h p = K then 1 else 0) =
      (if descentNumber σ = K then 1 - h p else 0) +
        (if descentNumber σ + 1 = K then h p else 0) := by
    intro p
    have := hle p
    split_ifs <;> omega
  rw [sum_congr rfl fun p _ => hpt p, sum_add_distrib]
  -- the sums of `h`
  have hH : ∑ p ∈ range (n + 2), h p + descentNumber σ = n + 1 := by
    rw [sum_range_succ', ← r26b_sum_dInd_perm σ]
    have h0 : h 0 = 0 := by simp [hh]
    rw [h0, add_zero, ← sum_add_distrib]
    refine (sum_congr rfl fun j _ => ?_).trans (show ∑ _j ∈ range (n + 1), (1 : ℕ) = n + 1 by simp)
    have := r26b_dInd_le_one (fun i => (σ i : ℕ)) j
    simp only [hh, Nat.add_sub_cancel, d]
    split_ifs <;> omega
  have hH' : ∑ p ∈ range (n + 2), (1 - h p) + ∑ p ∈ range (n + 2), h p = n + 2 := by
    rw [← sum_add_distrib]
    refine (sum_congr rfl fun p _ => ?_).trans (show ∑ _j ∈ range (n + 2), (1 : ℕ) = n + 2 by simp)
    have := hle p; omega
  by_cases h1 : descentNumber σ = K
  · have h2 : ¬ descentNumber σ + 1 = K := by omega
    simp only [ite_eq_left h1, ite_eq_right h2, sum_const_zero, add_zero]
    omega
  · simp only [ite_eq_right h1, sum_const_zero, zero_add]
    by_cases h2 : descentNumber σ + 1 = K
    · simp only [ite_eq_left h2]; omega
    · simp only [ite_eq_right h2, sum_const_zero]

/-- (26.14.8) in `ℕ`. -/
lemma r26b_eulerian_succ (n k : ℕ) :
    eulerianNumber (n + 2) (k + 1) =
      (k + 2) * eulerianNumber (n + 1) (k + 1) + (n + 1 - k) * eulerianNumber (n + 1) k := by
  unfold eulerianNumber
  rw [card_filter, ← (r26b_insMin (n := n)).sum_comp, Fintype.sum_prod_type_right]
  simp_rw [← card_filter, r26b_card_insMin_descent, sum_add_distrib]
  rw [card_filter, card_filter, mul_sum, mul_sum]
  congr 1
  · exact sum_congr rfl fun σ _ => by split_ifs <;> simp_all
  · exact sum_congr rfl fun σ _ => by split_ifs <;> simp_all

/-- `⟨n, k+1⟩ = 0` for `n ≤ k + 1`, `n ≥ 1`. -/
lemma r26b_eulerianNumber_eq_zero {n k : ℕ} (hk : n ≤ k + 1) (hn : 1 ≤ n) :
    eulerianNumber n (k + 1) = 0 := by
  unfold eulerianNumber
  rw [card_eq_zero, filter_eq_empty_iff]
  intro σ _ h
  have := q26b_descentNumber_le σ
  omega

/-- The inversion number as a double sum. -/
lemma r26b_inversionNumber_eq_sum {n : ℕ} (σ : Perm (Fin n)) :
    inversionNumber σ = ∑ a : Fin n, ∑ b : Fin n, if a < b ∧ σ b < σ a then 1 else 0 := by
  rw [inversionNumber, wordInversions, card_filter, Fintype.sum_prod_type]
  simp only [Fin.val_fin_lt]

/-- Inversions under the first-letter decomposition. -/
lemma r26b_inversionNumber_decomposeFin' {n : ℕ} (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    inversionNumber (Perm.decomposeFin'Symm i σ) = inversionNumber σ + i := by
  rw [r26b_inversionNumber_eq_sum, r26b_inversionNumber_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (n := n + 1), Perm.decomposeFin'Symm_zero,
    Perm.decomposeFin'Symm_succ, lt_self_iff_false, false_and, ite_false, zero_add, Fin.succ_pos,
    true_and, Fin.succ_lt_succ_iff, Fin.succAbove_lt_succAbove_iff, Fin.not_lt_zero]
  rw [add_comm]
  congr 1
  rw [Fintype.sum_equiv σ (fun b => if i.succAbove (σ b) < i then 1 else 0)
    (fun m => if i.succAbove m < i then 1 else 0) (fun _ => rfl)]
  simp only [Fin.succAbove_lt_iff_castSucc_lt]
  rw [← card_filter]
  simp only [Fin.lt_def, Fin.val_castSucc]
  rw [Fin.card_filter_val_lt]
  omega

/-- The increment of the major index when the minimum is inserted at position `p`. -/
def r26b_majInc (D : Finset ℕ) (p : ℕ) : ℕ :=
  #(D.filter (p ≤ ·)) + if 1 ≤ p ∧ p - 1 ∉ D then p else 0

/-- The major-index increments are distinct and lie in `range (n + 2)`. -/
lemma r26b_majInc_injOn {n : ℕ} {D : Finset ℕ} (hD : D ⊆ range n) :
    Set.InjOn (r26b_majInc D) (range (n + 2)) ∧
      ∀ p ∈ range (n + 2), r26b_majInc D p ∈ range (n + 2) := by
  have split : ∀ a b, a ≤ b → #(D.filter (a ≤ ·)) =
      #(D.filter (b ≤ ·)) + #(D.filter fun j => a ≤ j ∧ j < b) := by
    intro a b hab
    rw [← card_filter_add_card_filter_not (s := D.filter (a ≤ ·)) (fun j => b ≤ j),
      filter_filter, filter_filter]
    congr 2
    · exact filter_congr fun j _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    · exact filter_congr fun j _ => ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩
  have mle : ∀ a b, b - 1 ∉ D → #(D.filter fun j => a ≤ j ∧ j < b) ≤ b - 1 - a := by
    intro a b hb
    calc #(D.filter fun j => a ≤ j ∧ j < b) ≤ #(Ico a (b - 1)) := by
          refine card_le_card fun j hj => ?_
          simp only [mem_filter] at hj
          have : j ≠ b - 1 := fun h => hb (h ▸ hj.1)
          simp only [mem_Ico]; omega
      _ = b - 1 - a := Nat.card_Ico _ _
  have mge : ∀ a b, a < b → b - 1 ∈ D → 1 ≤ #(D.filter fun j => a ≤ j ∧ j < b) := by
    intro a b hab hb
    exact card_pos.mpr ⟨b - 1, mem_filter.mpr ⟨hb, by omega, by omega⟩⟩
  have gle : ∀ a, #(D.filter (a ≤ ·)) ≤ n - a := by
    intro a
    calc #(D.filter (a ≤ ·)) ≤ #(Ico a n) := by
          refine card_le_card fun j hj => ?_
          simp only [mem_filter] at hj
          have := mem_range.mp (hD hj.1)
          simp only [mem_Ico]; omega
      _ = n - a := Nat.card_Ico _ _
  refine ⟨?_, fun p hp => ?_⟩
  · have key : ∀ p p', p < p' → r26b_majInc D p ≠ r26b_majInc D p' := by
      intro p p' hpp'
      have h1 := split p p' hpp'.le
      unfold r26b_majInc
      by_cases hp' : p' - 1 ∈ D
      · have h2 := mge p p' hpp' hp'
        rw [ite_eq_right (c := 1 ≤ p' ∧ p' - 1 ∉ D) (fun h => h.2 hp')]
        split_ifs <;> omega
      · have h2 := mle p p' hp'
        rw [ite_eq_left (c := 1 ≤ p' ∧ p' - 1 ∉ D) ⟨by omega, hp'⟩]
        split_ifs <;> omega
    intro p _ p' _ h
    rcases lt_trichotomy p p' with hl | rfl | hl
    · exact absurd h (key p p' hl)
    · rfl
    · exact absurd h.symm (key p' p hl)
  · have := gle p
    have hp' := mem_range.mp hp
    rw [mem_range]
    unfold r26b_majInc
    split_ifs <;> omega

/-- The major-index increments run over `0, …, n + 1`. -/
lemma r26b_sum_pow_majInc (q : ℂ) {n : ℕ} {D : Finset ℕ} (hD : D ⊆ range n) :
    ∑ p ∈ range (n + 2), q ^ r26b_majInc D p = ∑ i ∈ range (n + 2), q ^ i := by
  obtain ⟨hinj, hmap⟩ := r26b_majInc_injOn hD
  rw [← sum_image (f := fun i => q ^ i) hinj]
  congr 1
  refine eq_of_subset_of_card_le (fun i hi => ?_) ?_
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp hi; exact hmap p hp
  · rw [card_image_of_injOn hinj]

/-- The major index after inserting the minimum at position `p`. -/
lemma r26b_majorIndex_insMin {n : ℕ} (p : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    majorIndex (r26b_insMin (p, σ)) =
      majorIndex σ + r26b_majInc (wordDescentSet fun i => (σ i : ℕ)) p := by
  have h := r26b_sum_descentSet_insMin p σ (fun j => j + 1)
  set D := wordDescentSet fun i => (σ i : ℕ)
  have hs : ∑ j ∈ D, (if j < p then j + 1 else j + 1 + 1) =
      majorIndex σ + #(D.filter ((p : ℕ) ≤ ·)) := by
    rw [majorIndex, wordMajorIndex, card_filter, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> omega
  rw [hs] at h
  unfold majorIndex wordMajorIndex at h ⊢
  unfold r26b_majInc
  have hd : r26b_dInd (fun i => (σ i : ℕ)) (p - 1) = if (p : ℕ) - 1 ∈ D then 1 else 0 := rfl
  rw [hd] at h
  by_cases h1 : 1 ≤ (p : ℕ)
  · rw [Nat.sub_add_cancel h1] at h
    by_cases h2 : (p : ℕ) - 1 ∈ D
    · simp only [h1, h2, ite_true, not_true_eq_false, and_false, ite_false, one_mul] at h ⊢
      omega
    · simp only [h1, h2, ite_true, not_false_eq_true, and_self, ite_false, zero_mul] at h ⊢
      omega
  · simp only [h1, ite_false, false_and] at h ⊢
    omega

/-- The excedance number as a sum of indicators. -/
lemma r26b_excedanceNumber_eq_sum {n : ℕ} (σ : Perm (Fin n)) :
    excedanceNumber σ = ∑ j : Fin n, if j < σ j then 1 else 0 := by
  rw [excedanceNumber, card_filter]

/-- Inserting `0` as a fixed point keeps the excedances. -/
lemma r26b_excedance_decomposeFin_zero {n : ℕ} (e : Perm (Fin n)) :
    excedanceNumber (Perm.decomposeFin.symm (0, e)) = excedanceNumber e := by
  rw [r26b_excedanceNumber_eq_sum, r26b_excedanceNumber_eq_sum, Fin.sum_univ_succ]
  simp [Perm.decomposeFin_symm_apply_zero, Perm.decomposeFin_symm_apply_succ, Fin.succ_lt_succ_iff]

/-- Inserting `0` into a cycle before `q + 1`. -/
lemma r26b_excedance_decomposeFin_succ {n : ℕ} (q : Fin n) (e : Perm (Fin n)) :
    excedanceNumber (Perm.decomposeFin.symm (q.succ, e)) + (if e⁻¹ q < q then 1 else 0) =
      excedanceNumber e + 1 := by
  rw [r26b_excedanceNumber_eq_sum, r26b_excedanceNumber_eq_sum, Fin.sum_univ_succ]
  simp only [Perm.decomposeFin_symm_apply_zero, Perm.decomposeFin_symm_apply_succ, Fin.succ_pos,
    ite_true]
  have h1 : ∀ x : Fin n, (if x.succ < swap 0 q.succ (e x).succ then 1 else 0) =
      (if x < e x ∧ e x ≠ q then 1 else 0) := by
    intro x
    by_cases hx : e x = q
    · rw [hx, swap_apply_right]; simp
    · rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => hx (Fin.succ_injective _ h))]
      simp [Fin.succ_lt_succ_iff, hx]
  have h2 : ∀ x : Fin n, (if x < e x then 1 else 0) =
      (if x < e x ∧ e x ≠ q then 1 else 0) + (if x < e x ∧ e x = q then 1 else 0) := by
    intro x
    by_cases hx : e x = q <;> simp [hx]
  have h3 : ∑ x : Fin n, (if x < e x ∧ e x = q then 1 else 0) = if e⁻¹ q < q then 1 else 0 := by
    rw [Finset.sum_eq_single (e⁻¹ q)]
    · simp
    · intro x _ hx
      rw [ite_eq_right]
      rintro ⟨-, h⟩
      exact hx (by rw [← h]; simp)
    · simp
  simp_rw [h1, h2, sum_add_distrib, h3]
  ring

/-- Excedances counted by values. -/
lemma r26b_card_excedance_eq {n : ℕ} (e : Perm (Fin n)) :
    #{q : Fin n | e⁻¹ q < q} = excedanceNumber e := by
  rw [excedanceNumber]
  refine card_bij (fun q _ => e⁻¹ q) ?_ ?_ ?_
  · intro q hq; simp only [mem_filter, mem_univ, true_and] at hq ⊢; simpa using hq
  · intro a _ b _ h; exact e⁻¹.injective h
  · intro x hx
    refine ⟨e x, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hx ⊢; simpa using hx

/-- The number of cycle insertions giving `K` excedances. -/
lemma r26b_card_decomposeFin_excedance {n : ℕ} (e : Perm (Fin n)) (K : ℕ) :
    #{p : Fin (n + 1) | excedanceNumber (Perm.decomposeFin.symm (p, e)) = K} =
      (if excedanceNumber e = K then excedanceNumber e + 1 else 0) +
        (if excedanceNumber e + 1 = K then n - excedanceNumber e else 0) := by
  rw [card_filter, Fin.sum_univ_succ, r26b_excedance_decomposeFin_zero]
  have hxe := (r26b_card_excedance_eq e).symm
  set x := excedanceNumber e
  set h : Fin n → ℕ := fun q => if e⁻¹ q < q then 0 else 1 with hh
  have hle : ∀ q, h q ≤ 1 := fun q => by simp only [hh]; split_ifs <;> omega
  have hexc : ∀ q, excedanceNumber (Perm.decomposeFin.symm (q.succ, e)) = x + h q := by
    intro q
    have := r26b_excedance_decomposeFin_succ q e
    simp only [hh]; split_ifs at this ⊢ <;> omega
  simp_rw [hexc]
  have hpt : ∀ q, (if x + h q = K then 1 else 0) =
      (if x = K then 1 - h q else 0) + (if x + 1 = K then h q else 0) := by
    intro q
    have := hle q
    split_ifs <;> omega
  rw [sum_congr rfl fun q _ => hpt q, sum_add_distrib]
  have hH : ∑ q, h q + x = n := by
    rw [hxe, card_filter, ← sum_add_distrib]
    refine (sum_congr rfl fun q _ => ?_).trans (show ∑ _q : Fin n, (1 : ℕ) = n by simp)
    simp only [hh]; split_ifs <;> omega
  have hH' : ∑ q, (1 - h q) + ∑ q, h q = n := by
    rw [← sum_add_distrib]
    refine (sum_congr rfl fun q _ => ?_).trans (show ∑ _q : Fin n, (1 : ℕ) = n by simp)
    have := hle q; omega
  by_cases h1 : x = K
  · have h2 : ¬ x + 1 = K := by omega
    simp only [ite_eq_left h1, ite_eq_right h2, sum_const_zero, add_zero]
    omega
  · simp only [ite_eq_right h1, sum_const_zero, zero_add]
    by_cases h2 : x + 1 = K
    · simp only [ite_eq_left h2]; omega
    · simp only [ite_eq_right h2, sum_const_zero]

/-- The recurrence of the excedance counts. -/
lemma r26b_excedance_succ (n K : ℕ) :
    #{σ : Perm (Fin (n + 1)) | excedanceNumber σ = K} =
      (K + 1) * #{σ : Perm (Fin n) | excedanceNumber σ = K} +
        (if 1 ≤ K then (n + 1 - K) * #{σ : Perm (Fin n) | excedanceNumber σ = K - 1} else 0) := by
  rw [card_filter, ← (Perm.decomposeFin (n := n)).symm.sum_comp, Fintype.sum_prod_type_right]
  simp_rw [← card_filter, r26b_card_decomposeFin_excedance, sum_add_distrib]
  rw [card_filter, mul_sum]
  congr 1
  · exact sum_congr rfl fun σ _ => by split_ifs <;> simp_all
  · split_ifs with hK
    · rw [card_filter, mul_sum]
      exact sum_congr rfl fun σ _ => by split_ifs <;> omega
    · exact sum_eq_zero fun σ _ => by rw [ite_eq_right]; omega

/-- (26.14.9), the descent-reversal bijection (used before its statement below). -/
lemma r26b_eulerianNumber_symm {n k : ℕ} (hk : k < n) :
    eulerianNumber n k = eulerianNumber n (n - 1 - k) := by
  unfold eulerianNumber
  refine Finset.card_bij (fun σ _ => Fin.revPerm * σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [q26b_descentNumber_rev, hσ]
  · intro σ _ τ _ h
    exact mul_left_cancel h
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ
    refine ⟨Fin.revPerm * τ, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      rw [q26b_descentNumber_rev, hτ]
      have := q26b_descentNumber_le τ
      omega
    · rw [← mul_assoc]
      ext i; simp

/-- The Eulerian recurrence in the form `⟨n+1, K⟩ = (K+1)⟨n, K⟩ + (n+1-K)⟨n, K-1⟩`, all `n`. -/
lemma r26b_eulerian_rec (n K : ℕ) :
    eulerianNumber (n + 1) K = (K + 1) * eulerianNumber n K +
      (if 1 ≤ K then (n + 1 - K) * eulerianNumber n (K - 1) else 0) := by
  have h0 : ∀ m, eulerianNumber m 0 = 1 := fun m => by
    unfold eulerianNumber
    rw [Finset.card_eq_one]
    exact ⟨1, by ext σ; simp [q26b_descentNumber_eq_zero_iff]⟩
  rcases K with _ | k
  · simp [h0]
  rcases n with _ | m
  · rw [r26b_eulerianNumber_eq_zero (by omega) le_rfl]
    have : eulerianNumber 0 (k + 1) = 0 := by
      unfold eulerianNumber
      rw [card_eq_zero, filter_eq_empty_iff]
      intro σ _ h
      simp [descentNumber, wordDescentSet] at h
    rw [this]
    rcases k with _ | k
    · simp [h0]
    · simp
  · rw [r26b_eulerian_succ]
    simp only [show 1 ≤ k + 1 from by omega, ite_true, Nat.add_sub_cancel]
    congr 2
    omega

end DLMF.Combinatorics
end
end
