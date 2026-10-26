/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Stirling
public import DLMF.BernoulliEuler.Explicit
public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.CrossRefAttribute
public import DLMFMathlib.Combinatorics.Q26bSurjections
public import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Permutations: cycle, order and matrix notation (DLMF §§26.13–26.15)

`𝔖_n` is `Equiv.Perm (Fin n)`. Positions and values are `0, …, n-1` in Lean against DLMF's
`1, …, n`; all statistics below are invariant under this shift (the major index adds `1` to
each descent position, as DLMF counts positions from `1`).

* Cycle notation: Mathlib's `c[…]` (`Cycle.formPerm`) and `List.formPerm`; the number of cycles
  (fixed points included) is `numCycles σ = σ.partition.parts.card`. The Stirling cycle numbers
  `[n k]` are Mathlib's unsigned `Nat.stirlingFirst n k` (DLMF's `|s(n, k)|`, with the signed
  `signedStirlingFirst` of `DLMF.Combinatorics.Stirling`).
* Order notation: words `w : Fin n → ℕ` with `wordInversions`, `wordDescentSet`,
  `wordMajorIndex`; for permutations `inversionNumber`, `descentNumber`, `majorIndex`. These
  word statistics are reused for multiset permutations (§26.16).
* Eulerian numbers `⟨n k⟩` are `eulerianNumber n k`, the number of `σ ∈ 𝔖_n` with `k` descents.
* Matrix notation: `σ.permMatrix R` (Mathlib) has entry `1` at `(j, σ j)`. Rook numbers
  `r_j(B)` (`rookNumber`), the rook polynomial `R(x, B)` (`rookPolynomial`), hit numbers
  `N_k(B)` (`hitNumber`) and `N(x, B)` (`hitPolynomial`) are over `ℤ[X]`.

Corrections: (26.13.4), second form `d(n) = ⌊(n! + e - 2)/e⌋`, fails at `n = 0`
(`d(0) = 1`, the right side is `0`); it is acquired for `n ≥ 1`.

## References

* NIST DLMF §§26.13–26.15.
-/

@[expose] public section

noncomputable section

open Finset Equiv
open Polynomial hiding bernoulli

namespace DLMF.Combinatorics

/-! ### §26.13 Cycle notation -/

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


/-- `⟨0 k⟩ = δ_{0k}` (restated before its tagged form (26.14.13) below). -/
lemma r26b_eulerianNumber_zero_left (k : ℕ) : eulerianNumber 0 k = if k = 0 then 1 else 0 := by
  unfold eulerianNumber
  have h0 : ∀ σ : Perm (Fin 0), descentNumber σ = 0 := fun σ => by
    simp [descentNumber, wordDescentSet]
  split_ifs with hk
  · subst hk
    rw [Finset.filter_true_of_mem fun σ _ => h0 σ, card_univ]; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ h
    exact hk (h ▸ h0 σ)

/-- The falling-factorial identity behind the Worpitzky induction. -/
lemma r26b_desc_key (n : ℕ) (x : ℂ) (k : ℕ) :
    (n + 1 : ℂ) * x * (descPochhammer ℂ n).eval (x + k) =
      (k + 1) * (descPochhammer ℂ (n + 1)).eval (x + k) +
        (n - k) * (descPochhammer ℂ (n + 1)).eval (x + k + 1) := by
  rw [descPochhammer_succ_eval, descPochhammer_succ_left, eval_mul, eval_X, eval_comp,
    eval_sub, eval_X, eval_one, add_sub_cancel_right]
  ring

/-- Worpitzky (26.14.5) multiplied by `n!`, summed to `n`, for all `n`. -/
lemma r26b_worpitzky_aux (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * (descPochhammer ℂ n).eval (x + k) =
      n.factorial * x ^ n := by
  induction n with
  | zero => simp [r26b_eulerianNumber_zero_left]
  | succ n ih =>
    have hz : eulerianNumber n (n + 1) = 0 := by
      rcases n with _ | m
      · simp [r26b_eulerianNumber_zero_left]
      · exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
    have hsplit : ∀ k, (eulerianNumber (n + 1) k : ℂ) * (descPochhammer ℂ (n + 1)).eval (x + k) =
        ((k : ℂ) + 1) * (eulerianNumber n k : ℂ) * (descPochhammer ℂ (n + 1)).eval (x + k) +
        (if 1 ≤ k then ((n + 1 - k : ℕ) : ℂ) * (eulerianNumber n (k - 1) : ℂ) else 0) *
          (descPochhammer ℂ (n + 1)).eval (x + k) := by
      intro k; rw [r26b_eulerian_rec]; push_cast; split_ifs <;> ring
    rw [sum_congr rfl fun k _ => hsplit k, sum_add_distrib]
    rw [sum_range_succ' (fun k => ((if 1 ≤ k then ((n + 1 - k : ℕ) : ℂ) *
      (eulerianNumber n (k - 1) : ℂ) else 0) * (descPochhammer ℂ (n + 1)).eval (x + k)))]
    rw [sum_range_succ (fun k => ((k : ℂ) + 1) * (eulerianNumber n k : ℂ) *
      (descPochhammer ℂ (n + 1)).eval (x + k)), hz]
    have h10 : ¬ (1 ≤ 0) := by omega
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.le_add_left, ite_true,
      Nat.add_sub_cancel, ite_eq_right h10, Nat.factorial_succ]
    rw [← sum_add_distrib, show (((n + 1) * n.factorial : ℕ) : ℂ) * x ^ (n + 1) =
      ((n + 1 : ℂ) * x) * (n.factorial * x ^ n) by push_cast; ring, ← ih, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have := r26b_desc_key n x k
    rw [show n + 1 - (k + 1) = n - k by omega, Nat.cast_sub hk']
    push_cast
    simp only [add_assoc] at this ⊢
    linear_combination (-(eulerianNumber n k : ℂ)) * this


/-- Worpitzky at natural arguments: `mⁿ = ∑ₖ ⟨n k⟩ C(m+k, n)`. -/
lemma r26b_worpitzky_nat (n m : ℕ) :
    m ^ n = ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n := by
  have h := r26b_worpitzky_aux n (m : ℂ)
  have e : ∀ k : ℕ, (descPochhammer ℂ n).eval ((m : ℂ) + k) =
      ((n.factorial * (m + k).choose n : ℕ) : ℂ) := by
    intro k
    rw [show (m : ℂ) + k = ((m + k : ℕ) : ℂ) by push_cast; ring,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  simp_rw [e] at h
  have h' : ((n.factorial * ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n : ℕ) : ℂ) =
      ((n.factorial * m ^ n : ℕ) : ℂ) := by
    push_cast at h ⊢
    rw [← h, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have := Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n) (Nat.cast_injective h')
  exact this.symm

/-- Uniqueness of coefficients in the binomial basis `C(m, j)`. -/
lemma r26b_binom_basis_unique (n : ℕ) (a b : ℕ → ℕ)
    (h : ∀ m : ℕ, ∑ j ∈ range (n + 1), m.choose j * a j = ∑ j ∈ range (n + 1), m.choose j * b j) :
    ∀ j ≤ n, a j = b j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hm := h j
    have hs : ∀ c : ℕ → ℕ, ∑ i ∈ range (n + 1), j.choose i * c i =
        ∑ i ∈ range j, j.choose i * c i + c j := by
      intro c
      rw [← sum_range_add_sum_Ico _ (show j + 1 ≤ n + 1 by omega), sum_range_succ,
        Nat.choose_self, one_mul, sum_eq_zero (s := Ico (j + 1) (n + 1)) fun i hi => by
          rw [Nat.choose_eq_zero_of_lt (by simp at hi; omega), zero_mul], add_zero]
    rw [hs, hs, sum_congr rfl fun i hi => by rw [ih i (mem_range.mp hi) (by simp at hi; omega)]]
      at hm
    omega

/-- `j! S(n, j) = ∑ₖ ⟨n k⟩ C(k, n-j)` (Worpitzky and Vandermonde). -/
lemma r26b_factorial_mul_stirlingSecond (n j : ℕ) (hj : j ≤ n) :
    j.factorial * Nat.stirlingSecond n j =
      ∑ k ∈ range (n + 1), eulerianNumber n k * k.choose (n - j) := by
  refine r26b_binom_basis_unique n (fun j => j.factorial * Nat.stirlingSecond n j)
    (fun j => ∑ k ∈ range (n + 1), eulerianNumber n k * k.choose (n - j)) (fun m => ?_) j hj
  have h1 := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m n
  simp only [Nat.descFactorial_eq_factorial_mul_choose] at h1
  calc ∑ j ∈ range (n + 1), m.choose j * (j.factorial * Nat.stirlingSecond n j) = m ^ n := by
        rw [h1]; exact sum_congr rfl fun j _ => by ring
    _ = ∑ k ∈ range (n + 1), eulerianNumber n k * (m + k).choose n := r26b_worpitzky_nat n m
    _ = ∑ k ∈ range (n + 1), eulerianNumber n k *
          ∑ j ∈ range (n + 1), m.choose j * k.choose (n - j) := by
        refine sum_congr rfl fun k _ => ?_
        rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => m.choose i * k.choose j)]
    _ = _ := by
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- The orthogonality `∑_t (-1)^t C(k+t, k) C(l, k+t) = δ_{lk}` for `l ≤ k + N`. -/
lemma r26b_alt_choose_orth (k l N : ℕ) (hl : l ≤ k + N) :
    ∑ t ∈ range (N + 1), (-1 : ℤ) ^ t * (k + t).choose k * l.choose (k + t) =
      if l = k then 1 else 0 := by
  have e : ∀ t, ((k + t).choose k : ℤ) * l.choose (k + t) = l.choose k * (l - k).choose t := by
    intro t
    have := Nat.choose_mul (n := l) (k := k + t) (s := k) (by omega)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast (by rw [mul_comm]; exact this)
  simp_rw [mul_assoc, e]
  by_cases hlk : k ≤ l
  · obtain ⟨d, rfl⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
    rw [Nat.add_sub_cancel_left]
    rw [← sum_range_add_sum_Ico _ (show d + 1 ≤ N + 1 by omega)]
    rw [sum_eq_zero (s := Ico (d + 1) (N + 1)) fun t ht => by
      rw [Nat.choose_eq_zero_of_lt (n := d) (by simp at ht; omega)]; simp, add_zero]
    have := Int.alternating_sum_range_choose (n := d)
    simp_rw [mul_left_comm _ ((k + d).choose k : ℤ)]
    rw [← mul_sum, this]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [ite_eq_right hd, ite_eq_right (by omega)]; simp
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun t _ => ?_
    rw [Nat.choose_eq_zero_of_lt (by omega : l < k)]; simp

/-- The right side of (26.14.6). -/
def r26b_eulA (n k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (n + 1).choose j * (k + 1 - j) ^ n

/-- The right side of (26.14.6) at `n = 0`. -/
lemma r26b_eulA_zero (K : ℕ) : r26b_eulA 0 K = if K = 0 then 1 else 0 := by
  unfold r26b_eulA
  split_ifs with hK
  · subst hK; simp
  · obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    simp only [pow_zero, mul_one, zero_add]
    rw [← Finset.sum_range_add_sum_Ico _ (show 2 ≤ k + 1 + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Ico 2 (k + 1 + 1)) fun j hj => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hj; omega)]; simp]
    simp [sum_range_succ]

/-- The right side of (26.14.6) satisfies the Eulerian recurrence. -/
lemma r26b_eulA_succ (n k : ℕ) :
    r26b_eulA (n + 1) (k + 1) =
      (k + 2) * r26b_eulA n (k + 1) + ((n : ℤ) + 1 - (k + 1)) * r26b_eulA n k := by
  unfold r26b_eulA
  rw [sum_range_succ' _ (k + 1), sum_range_succ' _ (k + 1), mul_add, mul_sum, mul_sum]
  have h0 : (-1 : ℤ) ^ 0 * ((n + 1 + 1).choose 0 : ℕ) *
        (((k + 1 : ℕ) : ℤ) + 1 - ((0 : ℕ) : ℤ)) ^ (n + 1) =
      ((k : ℤ) + 2) * ((-1) ^ 0 * ((n + 1).choose 0 : ℕ) *
        (((k + 1 : ℕ) : ℤ) + 1 - ((0 : ℕ) : ℤ)) ^ n) := by
    simp only [Nat.choose_zero_right]; push_cast; ring
  rw [h0]
  conv_rhs => rw [add_right_comm, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  · 
    have hi' : i < k + 1 := mem_range.mp hi
    have h := Nat.choose_succ_right_eq (n + 1) i
    rw [Nat.choose_succ_succ]
    push_cast
    have h' : ((n + 1).choose (i + 1) : ℤ) * (i + 1) = ((n + 1).choose i) * ((n : ℤ) + 1 - i) := by
      rcases le_or_gt i (n + 1) with hin | hin
      · have := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast [Nat.cast_sub hin] at this
        linear_combination this
      · rw [Nat.choose_eq_zero_of_lt hin, Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [show (k : ℤ) + 1 + 1 - (i + 1) = k + 1 - i by ring]
    rw [pow_succ]
    simp only [Nat.succ_eq_add_one] at *
    linear_combination ((-1 : ℤ) ^ i * ((k : ℤ) + 1 - i) ^ n) * h'

/-- §26.14(i): `⟨n k⟩` is also the number of permutations with exactly `k` excedances. -/
@[dlmf 26.14.i]
theorem eulerianNumber_eq_card_excedance (n k : ℕ) :
    eulerianNumber n k = #{σ : Perm (Fin n) | excedanceNumber σ = k} := by
  induction n generalizing k with
  | zero =>
    have h : ∀ σ : Perm (Fin 0), excedanceNumber σ = 0 := fun σ => by simp [excedanceNumber]
    simp only [h]
    unfold eulerianNumber
    have h' : ∀ σ : Perm (Fin 0), descentNumber σ = 0 := fun σ => by
      simp [descentNumber, wordDescentSet]
    simp only [h']
  | succ n ih =>
    rw [r26b_eulerian_rec, r26b_excedance_succ, ih, ih]

/-- §26.14(i): for `n ≥ 1`, `⟨n k⟩` is also the number of permutations with exactly `k + 1`
weak excedances (for `n = 0` there are no weak excedances while `⟨0 0⟩ = 1`). -/
@[dlmf 26.14.i]
theorem eulerianNumber_eq_card_weakExcedance {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    eulerianNumber n k = #{σ : Perm (Fin n) | weakExcedanceNumber σ = k + 1} := by
  have hcomp : ∀ σ : Perm (Fin n), weakExcedanceNumber σ + excedanceNumber σ⁻¹ = n := by
    intro σ
    have h1 : excedanceNumber σ⁻¹ = #{j : Fin n | σ j < j} := by
      rw [excedanceNumber]
      refine card_bij (fun i _ => σ⁻¹ i) ?_ ?_ ?_
      · intro i hi; simp only [mem_filter, mem_univ, true_and] at hi ⊢; simpa using hi
      · intro a _ b _ h; exact σ⁻¹.injective h
      · intro j hj
        refine ⟨σ j, ?_, by simp⟩
        simp only [mem_filter, mem_univ, true_and] at hj ⊢; simpa using hj
    rw [h1, weakExcedanceNumber]
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun j => j ≤ σ j)
    simp only [not_le, card_univ, Fintype.card_fin] at this
    exact this
  have hle : ∀ σ : Perm (Fin n), excedanceNumber σ ≤ n := fun σ =>
    (card_le_univ _).trans (by simp)
  by_cases hk : k < n
  · rw [r26b_eulerianNumber_symm hk, eulerianNumber_eq_card_excedance]
    refine card_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_
    · intro σ hσ
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      have := hcomp σ⁻¹
      rw [inv_inv] at this
      omega
    · intro a _ b _ h; exact inv_injective h
    · intro τ hτ
      refine ⟨τ⁻¹, ?_, inv_inv τ⟩
      simp only [mem_filter, mem_univ, true_and] at hτ ⊢
      have := hcomp τ
      have := hle τ⁻¹
      omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [r26b_eulerianNumber_eq_zero (by omega) hn, eq_comm, card_eq_zero, filter_eq_empty_iff]
    intro σ _ h
    have := hcomp σ
    omega

/-- Table 26.14.1, a few entries: `⟨3 1⟩ = 4`, `⟨4 1⟩ = 11`, `⟨5 2⟩ = 66`. -/
@[dlmf 26.14.T1]
theorem eulerianNumber_table :
    eulerianNumber 3 1 = 4 ∧ eulerianNumber 4 1 = 11 ∧ eulerianNumber 5 2 = 66 := by
  decide +kernel

/-- (26.14.3): `∑_σ q^{inv σ} = ∑_σ q^{maj σ} = ∏_{j=1}^n (1 - q^j)/(1 - q)` for `q ≠ 1`. -/
@[dlmf 26.14.E3]
theorem sum_pow_inversionNumber {q : ℂ} (hq : q ≠ 1) (n : ℕ) :
    ∑ σ : Perm (Fin n), q ^ inversionNumber σ = ∏ j ∈ Icc 1 n, (1 - q ^ j) / (1 - q) ∧
      ∑ σ : Perm (Fin n), q ^ majorIndex σ = ∏ j ∈ Icc 1 n, (1 - q ^ j) / (1 - q) := by
  refine ⟨?_, ?_⟩
  ·   have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq.symm
      induction n with
      | zero => simp [inversionNumber, wordInversions]
      | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega), ← ih]
        rcases n with _ | n
        · simp [inversionNumber, wordInversions, div_self hq']
        rw [← (Perm.decomposeFin' (n := n)).symm.sum_comp, Fintype.sum_prod_type]
        simp only [Perm.decomposeFin'_symm, r26b_inversionNumber_decomposeFin', pow_add,
          ← Finset.mul_sum, ← Finset.sum_mul]
        congr 1
        rw [Fin.sum_univ_eq_sum_range (fun i => q ^ i), eq_div_iff hq', mul_comm, mul_neg_geom_sum]
        ring
  ·   have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq.symm
      induction n with
      | zero => simp [majorIndex, wordMajorIndex, wordDescentSet]
      | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega), ← ih]
        rcases n with _ | n
        · simp [majorIndex, wordMajorIndex, wordDescentSet, div_self hq']
        rw [← (r26b_insMin (n := n)).sum_comp, Fintype.sum_prod_type_right]
        simp only [r26b_majorIndex_insMin, pow_add, ← Finset.mul_sum]
        rw [Finset.sum_mul]
        refine sum_congr rfl fun σ _ => ?_
        congr 1
        rw [Fin.sum_univ_eq_sum_range
          (fun p => q ^ r26b_majInc (wordDescentSet fun i => (σ i : ℕ)) p),
          r26b_sum_pow_majInc q (by simpa using r26b_wordDescentSet_subset (fun i => (σ i : ℕ))),
          eq_div_iff hq', mul_comm, mul_neg_geom_sum]
        ring

/-- (26.14.4): `∑_{n,k} ⟨n k⟩ x^k tⁿ/n! = (1 - x)/(exp((x - 1)t) - x)` for `|x| < 1`, `|t| < 1`. -/
@[dlmf 26.14.E4]
theorem hasSum_eulerianNumber {x t : ℂ} (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) :
    HasSum (fun nk : ℕ × ℕ => (eulerianNumber nk.1 nk.2 : ℂ) * x ^ nk.2 * t ^ nk.1 / nk.1.factorial)
      ((1 - x) / (Complex.exp ((x - 1) * t) - x)) := by
  sorry

/-- (26.14.5), Worpitzky's identity: `∑_{k=0}^{n-1} ⟨n k⟩ C(x + k, n) = xⁿ` for `n ≥ 1` and
every `x ∈ ℂ`, with `C(y, n) = y(y-1)⋯(y-n+1)/n!`. -/
@[dlmf 26.14.E5]
theorem worpitzky {n : ℕ} (hn : 1 ≤ n) (x : ℂ) :
    ∑ k ∈ range n, (eulerianNumber n k : ℂ) * ((descPochhammer ℂ n).eval (x + k) / n.factorial) =
      x ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := r26b_worpitzky_aux (m + 1) x
  rw [sum_range_succ, r26b_eulerianNumber_eq_zero (n := m + 1) (k := m) le_rfl hn] at h
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  have hf : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp_rw [mul_div_assoc']
  rw [← sum_div, h]
  field_simp

/-- (26.14.6) for every `n`, including `n = 0` (stronger than DLMF). -/
lemma r26b_eulerianNumber_eq_eulA (n k : ℕ) : (eulerianNumber n k : ℤ) = r26b_eulA n k := by
  induction n generalizing k with
  | zero => rw [r26b_eulerianNumber_zero_left, r26b_eulA_zero]; split_ifs <;> simp
  | succ n ih =>
    rw [r26b_eulerian_rec]
    rcases k with _ | k
    · simp [ih, r26b_eulA]
    rw [r26b_eulA_succ, ← ih, ← ih]
    simp only [show 1 ≤ k + 1 from by omega, ite_true, Nat.add_sub_cancel]
    by_cases hkn : k ≤ n
    · push_cast [Nat.cast_sub hkn]; ring
    · have hz : eulerianNumber n k = 0 := by
        rcases n with _ | m
        · rw [r26b_eulerianNumber_zero_left]; simp; omega
        · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
      have hz' : eulerianNumber n (k + 1) = 0 := by
        rcases n with _ | m
        · rw [r26b_eulerianNumber_zero_left]; simp
        · exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
      simp [hz, hz']

/-- (26.14.6): `⟨n k⟩ = ∑_{j=0}^k (-1)^j C(n+1, j) (k+1-j)ⁿ` for `n ≥ 1`. -/
@[dlmf 26.14.E6]
theorem eulerianNumber_eq_sum {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (eulerianNumber n k : ℤ) =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (n + 1).choose j * (k + 1 - j) ^ n := by
  exact (fun _ => r26b_eulerianNumber_eq_eulA n k) hn

/-- (26.14.7): `⟨n k⟩ = ∑_{j=0}^{n-k} (-1)^{n-k-j} j! C(n-j, k) S(n, j)`, with
`S = Nat.stirlingSecond`. -/
@[dlmf 26.14.E7]
theorem eulerianNumber_eq_sum_stirlingSecond (n k : ℕ) :
    (eulerianNumber n k : ℤ) = ∑ j ∈ range (n - k + 1),
      (-1 : ℤ) ^ (n - k - j) * j.factorial * (n - j).choose k * Nat.stirlingSecond n j := by
  by_cases hkn : k ≤ n
  · rw [← sum_range_reflect]
    have step : ∀ t ∈ range (n - k + 1), (-1 : ℤ) ^ (n - k - (n - k + 1 - 1 - t)) *
        (n - k + 1 - 1 - t).factorial * (n - (n - k + 1 - 1 - t)).choose k *
          Nat.stirlingSecond n (n - k + 1 - 1 - t) =
        ∑ l ∈ range (n + 1), (eulerianNumber n l : ℤ) *
          ((-1 : ℤ) ^ t * (k + t).choose k * l.choose (k + t)) := by
      intro t ht
      have ht' := mem_range.mp ht
      have h := r26b_factorial_mul_stirlingSecond n (n - k + 1 - 1 - t) (by omega)
      rw [show n - (n - k + 1 - 1 - t) = k + t by omega] at h
      have h' : ((n - k + 1 - 1 - t).factorial : ℤ) * Nat.stirlingSecond n (n - k + 1 - 1 - t) =
          ∑ l ∈ range (n + 1), (eulerianNumber n l : ℤ) * l.choose (k + t) := by
        exact_mod_cast h
      rw [show n - k - (n - k + 1 - 1 - t) = t by omega,
        show n - (n - k + 1 - 1 - t) = k + t by omega]
      calc (-1 : ℤ) ^ t * ((n - k + 1 - 1 - t).factorial : ℤ) * ((k + t).choose k : ℤ) *
            (Nat.stirlingSecond n (n - k + 1 - 1 - t) : ℤ) =
          (-1 : ℤ) ^ t * ((k + t).choose k : ℤ) * (((n - k + 1 - 1 - t).factorial : ℤ) *
            Nat.stirlingSecond n (n - k + 1 - 1 - t)) := by ring
        _ = _ := by
          rw [h', mul_sum]
          exact sum_congr rfl fun l _ => by ring
    rw [sum_congr rfl step, sum_comm]
    simp_rw [← mul_sum]
    rw [sum_congr rfl fun l hl => by
      rw [r26b_alt_choose_orth k l (n - k) (by have := mem_range.mp hl; omega)]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' (range (n + 1)) k, ite_eq_left (mem_range.mpr (by omega))]
  · have hz : eulerianNumber n k = 0 := by
      rcases n with _ | m
      · rw [r26b_eulerianNumber_zero_left, ite_eq_right (by omega)]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact r26b_eulerianNumber_eq_zero (by omega) (by omega)
    rw [hz, show n - k = 0 by omega]
    simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

/-- (26.14.8): `⟨n k⟩ = (k+1)⟨n-1, k⟩ + (n-k)⟨n-1, k-1⟩` for `n ≥ 2` and `k ≥ 1` (for `k = 0`
see (26.14.14)); the coefficient `n - k` is an integer. -/
@[dlmf 26.14.E8]
theorem eulerianNumber_recurrence {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (eulerianNumber n k : ℤ) =
      (k + 1) * eulerianNumber (n - 1) k + ((n : ℤ) - k) * eulerianNumber (n - 1) (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [r26b_eulerian_succ]
  simp only [show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel]
  by_cases hj : j ≤ m + 1
  · push_cast [hj]
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [r26b_eulerianNumber_eq_zero (by omega) (by omega),
      r26b_eulerianNumber_eq_zero (n := m + 1) (k := i) (by omega) (by omega)]
    simp

/-- (26.14.9): `⟨n k⟩ = ⟨n, n-1-k⟩` for `n ≥ 1` and `k ≤ n - 1` (for `k ≥ n` both sides are
`0` in DLMF's convention). -/
@[dlmf 26.14.E9]
theorem eulerianNumber_symm {n k : ℕ} (hk : k < n) :
    eulerianNumber n k = eulerianNumber n (n - 1 - k) :=
  r26b_eulerianNumber_symm hk

/-- A permutation of `Fin n` has at most `n - 1` descents. -/
lemma c26b_descentNumber_lt {n : ℕ} (hn : 1 ≤ n) (σ : Perm (Fin n)) : descentNumber σ < n := by
  unfold descentNumber
  have hsub : wordDescentSet (fun i => (σ i : ℕ)) ⊆ range (n - 1) := by
    intro j hj
    simp only [wordDescentSet, mem_filter, mem_range] at hj
    obtain ⟨_, h, _⟩ := hj
    simp only [mem_range]; omega
  have := card_le_card hsub
  simp only [card_range] at this
  omega

/-- (26.14.10): `∑_{k=0}^{n-1} ⟨n k⟩ = n!` for `n ≥ 1`. -/
@[dlmf 26.14.E10]
theorem sum_eulerianNumber {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range n, eulerianNumber n k = n.factorial := by
  unfold eulerianNumber
  rw [← Finset.card_biUnion]
  · have : (range n).biUnion (fun k => ({σ : Perm (Fin n) | descentNumber σ = k} : Finset _)) =
        univ := by
      ext σ
      simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and, iff_true]
      exact ⟨_, c26b_descentNumber_lt hn σ, rfl⟩
    rw [this, card_univ, Fintype.card_perm, Fintype.card_fin]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter] at h1 h2
    exact hij (h1.2.symm.trans h2.2)

/-- The alternating sum of Eulerian numbers in the form of (24.6.11). -/
lemma r26b_alt_sum_eulerian (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * eulerianNumber n k =
      ∑ K ∈ Icc 1 (n + 1), ∑ j ∈ range K,
        (-1 : ℚ) ^ (j + 1) * ((n + 1).choose K : ℚ) * (j : ℚ) ^ n := by
  have h6 : ∀ k, ((eulerianNumber n k : ℤ) : ℚ) = ∑ j ∈ range (k + 1),
      (-1 : ℚ) ^ j * (n + 1).choose j * ((k : ℚ) + 1 - j) ^ n := by
    intro k
    rw [eulerianNumber_eq_sum hn k]
    push_cast; rfl
  simp only [Int.cast_natCast] at h6
  simp_rw [h6, mul_sum]
  rw [sum_sigma', sum_sigma']
  have hterm : ∀ k j, j ≤ k → j ≤ n + 1 →
      (-1 : ℚ) ^ k * ((-1 : ℚ) ^ j * ((n + 1).choose j : ℚ) * ((k : ℚ) + 1 - j) ^ n) =
        (-1 : ℚ) ^ (k + 1 - j + 1) * ((n + 1).choose (n + 1 - j) : ℚ) *
          (((k + 1 - j : ℕ) : ℚ)) ^ n := by
    intro k j hjk hjn
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
    rw [Nat.choose_symm hjn, show j + d + 1 - j = d + 1 by omega]
    push_cast
    rw [show (j : ℚ) + d + 1 - j = d + 1 by ring]
    have h2 : ((-1 : ℚ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [pow_add, pow_add, pow_add]
    linear_combination (-(1 : ℚ)) ^ d * ((n + 1).choose j : ℚ) * ((d : ℚ) + 1) ^ n * h2
  refine sum_bij_ne_zero (fun x _ _ => ⟨n + 1 - x.2, x.1 + 1 - x.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hx _
    simp only [mem_sigma, mem_range, mem_Icc] at hx ⊢
    omega
  · rintro ⟨k, j⟩ hx _ ⟨k', j'⟩ hx' _ h
    simp only [mem_sigma, mem_range] at hx hx'
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : j = j' := by omega
    subst this
    have : k = k' := by have := eq_of_heq h2; omega
    subst this
    rfl
  · rintro ⟨K, j⟩ hy hne
    simp only [mem_sigma, mem_range, mem_Icc] at hy
    have hj : j ≠ 0 := by
      rintro rfl; apply hne; simp [zero_pow (by omega : n ≠ 0)]
    refine ⟨⟨j + n - K, n + 1 - K⟩, ?_, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]; omega
    · intro h0
      apply hne
      rw [hterm _ _ (by dsimp only; omega) (by dsimp only; omega)] at h0
      rw [← h0]
      dsimp only
      rw [show n + 1 - (n + 1 - K) = K by omega, show j + n - K + 1 - (n + 1 - K) = j by omega]
    · simp only [Sigma.mk.injEq]
      refine ⟨by omega, ?_⟩
      rw [heq_eq_eq]; omega
  · rintro ⟨k, j⟩ hx _
    simp only [mem_sigma, mem_range] at hx
    exact hterm k j (by omega) (by omega)

/-- (26.14.11): `B_m = m/(2^m (2^m - 1)) ∑_{k=0}^{m-2} (-1)^k ⟨m-1, k⟩` for `m ≥ 2`
(`bernoulli`, the Bernoulli numbers with `B_1 = -1/2`). -/
@[dlmf 26.14.E11]
theorem bernoulli_eq_sum_eulerianNumber {m : ℕ} (hm : 2 ≤ m) :
    bernoulli m = (m : ℚ) / (2 ^ m * (2 ^ m - 1)) *
      ∑ k ∈ range (m - 1), (-1 : ℚ) ^ k * eulerianNumber (m - 1) k := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, r26b_alt_sum_eulerian n (by omega),
    DLMF.BernoulliEuler.bernoulli_eq_explicit₁₁ (by omega), Nat.add_sub_cancel]

/-- (26.14.12): `S(n, m) = (1/m!) ∑_{k=0}^{n-1} ⟨n k⟩ C(k, n-m)` for `n ≥ m`, `n ≥ 1`. -/
@[dlmf 26.14.E12]
theorem stirlingSecond_eq_sum_eulerianNumber {n m : ℕ} (hmn : m ≤ n) (hn : 1 ≤ n) :
    (Nat.stirlingSecond n m : ℚ) =
      1 / m.factorial * ∑ k ∈ range n, (eulerianNumber n k : ℚ) * k.choose (n - m) := by
  have h := r26b_factorial_mul_stirlingSecond n m hmn
  rw [sum_range_succ] at h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [r26b_eulerianNumber_eq_zero (n := n' + 1) (k := n') le_rfl hn, zero_mul, add_zero] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast at hq
  rw [← hq]
  field_simp

/-- (26.14.13): `⟨0 k⟩ = δ_{0,k}`. -/
@[dlmf 26.14.E13]
theorem eulerianNumber_zero_left (k : ℕ) : eulerianNumber 0 k = if k = 0 then 1 else 0 := by
  unfold eulerianNumber
  have h0 : ∀ σ : Perm (Fin 0), descentNumber σ = 0 := fun σ => by
    simp [descentNumber, wordDescentSet]
  split_ifs with hk
  · subst hk
    rw [Finset.filter_true_of_mem fun σ _ => h0 σ, card_univ]; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ h
    exact hk (h ▸ h0 σ)

/-- (26.14.14): `⟨n 0⟩ = 1`. -/
@[dlmf 26.14.E14]
theorem eulerianNumber_zero_right (n : ℕ) : eulerianNumber n 0 = 1 := by
  unfold eulerianNumber
  rw [Finset.card_eq_one]
  exact ⟨1, by ext σ; simp [q26b_descentNumber_eq_zero_iff]⟩

/-- (26.14.15): `⟨n 1⟩ = 2ⁿ - n - 1` for `n ≥ 1`. -/
@[dlmf 26.14.E15]
theorem eulerianNumber_one_right {n : ℕ} (hn : 1 ≤ n) :
    (eulerianNumber n 1 : ℤ) = 2 ^ n - n - 1 := by
  induction n, hn using Nat.le_induction with
  | base => rw [r26b_eulerianNumber_eq_zero (n := 1) (k := 0) (by omega) le_rfl]; simp
  | succ m hm ih =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [r26b_eulerian_succ, eulerianNumber_zero_right]
    push_cast
    rw [ih]
    push_cast
    ring

/-- (26.14.16): `⟨n 2⟩ = 3ⁿ - (n+1) 2ⁿ + C(n+1, 2)` for `n ≥ 1`. -/
@[dlmf 26.14.E16]
theorem eulerianNumber_two_right {n : ℕ} (hn : 1 ≤ n) :
    (eulerianNumber n 2 : ℤ) = 3 ^ n - (n + 1) * 2 ^ n + (n + 1).choose 2 := by
  induction n, hn using Nat.le_induction with
  | base => rw [r26b_eulerianNumber_eq_zero (n := 1) (k := 1) (by omega) le_rfl]; simp
  | succ m hm ih =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [r26b_eulerian_succ]
    push_cast
    rw [ih, eulerianNumber_one_right (by omega)]
    have h1 : ((n + 1 + 1 + 1).choose 2 : ℤ) = (n + 2) + (n + 1 + 1).choose 2 := by
      rw [Nat.choose_succ_succ]; push_cast; simp
    have h2 : ((n + 1 + 1).choose 2 : ℤ) * 2 = (n + 2) * (n + 1) := by
      have key : ∀ m : ℕ, (m + 1).choose 2 * 2 = (m + 1) * m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [Nat.choose_succ_succ, add_mul, ih]; simp; ring
      exact_mod_cast key (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at h1 h2 ⊢
    rw [h1]
    linear_combination h2

/-! ### §26.15 Matrix notation -/

/-- (26.15.1): the matrix of the example permutation `35247816`: a `1` in row `j`, column
`σ(j)`. -/
@[dlmf 26.15.E1]
theorem dlmfExamplePerm_permMatrix :
    dlmfExamplePerm.permMatrix ℤ = !![0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0] := by
  decide +kernel

/-- (26.15.2): `inv(σ) = ∑ a_{gh} a_{kℓ}` over `1 ≤ g < k ≤ n`, `n ≥ h > ℓ ≥ 1`, where
`(a_{gh})` is the permutation matrix of `σ`. -/
@[dlmf 26.15.E2]
theorem inversionNumber_eq_sum_permMatrix {n : ℕ} (σ : Perm (Fin n)) :
    (inversionNumber σ : ℤ) = ∑ g : Fin n, ∑ k : Fin n, ∑ h : Fin n, ∑ l : Fin n,
      if g < k ∧ l < h then σ.permMatrix ℤ g h * σ.permMatrix ℤ k l else 0 := by
  have hP : ∀ i j, σ.permMatrix ℤ i j = if σ i = j then 1 else 0 := by
    intro i j
    simp [Perm.permMatrix, PEquiv.toMatrix_apply]
  simp_rw [hP]
  have : ∀ g k : Fin n, (∑ h : Fin n, ∑ l : Fin n,
      if g < k ∧ l < h then (if σ g = h then (1 : ℤ) else 0) * (if σ k = l then 1 else 0) else 0) =
      if g < k ∧ σ k < σ g then 1 else 0 := by
    intro g k
    rw [Finset.sum_eq_single (σ g)]
    · rw [Finset.sum_eq_single (σ k)]
      · simp
      · intro l _ hl; simp [Ne.symm hl]
      · simp
    · intro h _ hh
      refine sum_eq_zero fun l _ => ?_
      simp [Ne.symm hh]
    · simp
  simp_rw [this]
  rw [inversionNumber, wordInversions, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  push_cast
  simp only [Fin.val_fin_lt]

/-- A set of squares of the `n × n` board is nonattacking if no two share a row or a column. -/
def IsNonattacking {n : ℕ} (C : Finset (Fin n × Fin n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x.1 ≠ y.1 ∧ x.2 ≠ y.2

instance {n : ℕ} (C : Finset (Fin n × Fin n)) : Decidable (IsNonattacking C) := by
  unfold IsNonattacking; infer_instance

/-- `r_j(B)`: the number of ways of placing `j` nonattacking rooks on the squares of `B`
(`r_0(B) = 1`) (DLMF §26.15). -/
@[dlmf 26.15]
def rookNumber {n : ℕ} (B : Finset (Fin n × Fin n)) (j : ℕ) : ℕ :=
  #{C ∈ B.powerset | C.card = j ∧ IsNonattacking C}

/-- (26.15.3): the rook polynomial `R(x, B) = ∑_{j=0}^n r_j(B) x^j`. -/
@[dlmf 26.15.E3]
def rookPolynomial {n : ℕ} (B : Finset (Fin n × Fin n)) : ℤ[X] :=
  ∑ j ∈ range (n + 1), C (rookNumber B j : ℤ) * X ^ j

/-- `N_k(B)`: the number of `σ ∈ 𝔖_n` for which exactly `k` of the pairs `(j, σ(j))` lie in
`B` (DLMF §26.15). -/
@[dlmf 26.15]
def hitNumber {n : ℕ} (B : Finset (Fin n × Fin n)) (k : ℕ) : ℕ :=
  #{σ : Perm (Fin n) | #{j : Fin n | (j, σ j) ∈ B} = k}

/-- (26.15.6): `N(x, B) = ∑_{k=0}^n N_k(B) x^k`. -/
@[dlmf 26.15.E6]
def hitPolynomial {n : ℕ} (B : Finset (Fin n × Fin n)) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (hitNumber B k : ℤ) * X ^ k

/-- The diagonal board `{(1,1), …, (n,n)}`. -/
def diagonalBoard (n : ℕ) : Finset (Fin n × Fin n) := univ.image fun i => (i, i)

/-- §26.15: the derangements are the permutations avoiding the diagonal board,
`N_0(diag) = d(n)`. -/
@[dlmf 26.15]
theorem hitNumber_diagonalBoard_zero (n : ℕ) :
    hitNumber (diagonalBoard n) 0 = numDerangements n := by
  have key : ∀ σ : Perm (Fin n),
      #{j : Fin n | (j, σ j) ∈ diagonalBoard n} = 0 ↔ σ ∈ derangements (Fin n) := by
    intro σ
    have hmem : ∀ x : Fin n, (x, σ x) ∈ diagonalBoard n ↔ σ x = x := by
      intro x
      simp only [diagonalBoard, mem_image, mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨a, rfl, h⟩; exact h.symm
      · intro h; exact ⟨x, rfl, h.symm⟩
    change _ ↔ ∀ x, σ x ≠ x
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp only [mem_univ, true_implies, hmem]
  unfold hitNumber
  rw [← Fintype.card_fin n, ← card_derangements_eq_numDerangements (Fin n), Fintype.card_fin,
    Fintype.card_subtype]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  exact key σ

/-- §26.15: for the derangement board, `r_j(B) = C(n, j)`. -/
@[dlmf 26.15]
theorem rookNumber_diagonalBoard (n j : ℕ) : rookNumber (diagonalBoard n) j = n.choose j := by
  have hcard : (diagonalBoard n).card = n := by
    rw [diagonalBoard, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    simp
  unfold rookNumber
  rw [show n.choose j = (diagonalBoard n).card.choose j by rw [hcard], ← Finset.card_powersetCard,
    Finset.powersetCard_eq_filter]
  congr 1
  refine Finset.filter_congr fun C hC => ?_
  rw [mem_powerset] at hC
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro x hx y hy hxy
  obtain ⟨a, -, rfl⟩ := mem_image.mp (hC hx)
  obtain ⟨b, -, rfl⟩ := mem_image.mp (hC hy)
  have hab : a ≠ b := fun h => hxy (h ▸ rfl)
  exact ⟨hab, hab⟩

/-- A nonattacking placement has at most `n` rooks. -/
lemma q26b_card_le_of_nonattacking {n : ℕ} {C : Finset (Fin n × Fin n)} (hC : IsNonattacking C) :
    #C ≤ n := by
  have : #(C.image Prod.fst) = #C := card_image_of_injOn fun x hx y hy h => by
    by_contra hne; exact (hC x hx y hy hne).1 h
  rw [← this]
  exact (card_le_univ _).trans (by simp)

/-- The rook polynomial as a sum over nonattacking placements. -/
lemma q26b_rookPolynomial_eq_sum {n : ℕ} (B : Finset (Fin n × Fin n)) :
    rookPolynomial B = ∑ D ∈ B.powerset.filter IsNonattacking, (X : ℤ[X]) ^ #D := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun D => #D) (t := range (n + 1))
    (fun D hD => by
      simp only [mem_filter] at hD
      rw [mem_range]; exact Nat.lt_succ_of_le (q26b_card_le_of_nonattacking hD.2))]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun D hD => by rw [(mem_filter.mp hD).2]), sum_const, nsmul_eq_mul,
    rookNumber, Finset.filter_filter]
  simp only [map_natCast]
  congr 3
  exact Finset.filter_congr fun D _ => and_comm

/-- (26.15.4): if no square of `B₁` shares a row or column with a square of `B₂`, then
`R(x, B₁ ∪ B₂) = R(x, B₁) R(x, B₂)`. -/
@[dlmf 26.15.E4]
theorem rookPolynomial_union {n : ℕ} {B₁ B₂ : Finset (Fin n × Fin n)}
    (h : ∀ x ∈ B₁, ∀ y ∈ B₂, x.1 ≠ y.1 ∧ x.2 ≠ y.2) :
    rookPolynomial (B₁ ∪ B₂) = rookPolynomial B₁ * rookPolynomial B₂ := by
  classical
  have hdisj : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    exact (h x hx x hx2).1 rfl
  simp only [q26b_rookPolynomial_eq_sum]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · rintro ⟨C₁, C₂⟩ hp
    simp only [mem_product, mem_filter, mem_powerset] at hp ⊢
    refine ⟨union_subset_union hp.1.1 hp.2.1, ?_⟩
    intro x hx y hy hxy
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hp.1.2 x hx y hy hxy
    · exact h x (hp.1.1 hx) y (hp.2.1 hy)
    · have := h y (hp.1.1 hy) x (hp.2.1 hx); exact ⟨this.1.symm, this.2.symm⟩
    · exact hp.2.2 x hx y hy hxy
  · rintro ⟨C₁, C₂⟩ hp ⟨D₁, D₂⟩ hq hCD
    simp only [mem_product, mem_filter, mem_powerset] at hp hq
    simp only at hCD
    have key : ∀ (E₁ E₂ : Finset (Fin n × Fin n)), E₁ ⊆ B₁ → E₂ ⊆ B₂ →
        (E₁ ∪ E₂).filter (· ∈ B₁) = E₁ ∧ (E₁ ∪ E₂).filter (· ∈ B₂) = E₂ := by
      intro E₁ E₂ h1 h2
      constructor
      · ext x
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨hx | hx, hb⟩
          · exact hx
          · exact absurd hb (Finset.disjoint_right.mp hdisj (h2 hx))
        · intro hx; exact ⟨Or.inl hx, h1 hx⟩
      · ext x
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨hx | hx, hb⟩
          · exact absurd hb (Finset.disjoint_left.mp hdisj (h1 hx))
          · exact hx
        · intro hx; exact ⟨Or.inr hx, h2 hx⟩
    obtain ⟨h1, h2⟩ := key C₁ C₂ hp.1.1 hp.2.1
    obtain ⟨h3, h4⟩ := key D₁ D₂ hq.1.1 hq.2.1
    rw [hCD] at h1 h2
    exact Prod.ext (h1.symm.trans h3) (h2.symm.trans h4)
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC
    refine ⟨(C.filter (· ∈ B₁), C.filter (· ∈ B₂)), ?_, ?_⟩
    · simp only [mem_product, mem_filter, mem_powerset]
      refine ⟨⟨fun x hx => (mem_filter.mp hx).2, fun x hx y hy => hC.2 x (mem_filter.mp hx).1 y
        (mem_filter.mp hy).1⟩, fun x hx => (mem_filter.mp hx).2, fun x hx y hy => hC.2 x
        (mem_filter.mp hx).1 y (mem_filter.mp hy).1⟩
    · ext x
      simp only [mem_union, mem_filter]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        rcases mem_union.mp (hC.1 hx) with hb | hb
        · exact Or.inl ⟨hx, hb⟩
        · exact Or.inr ⟨hx, hb⟩
  · rintro ⟨C₁, C₂⟩ hp
    simp only [mem_product, mem_filter, mem_powerset] at hp
    rw [card_union_of_disjoint (Finset.disjoint_of_subset_left hp.1.1
      (Finset.disjoint_of_subset_right hp.2.1 hdisj)), pow_add]

/-- (26.15.5): for `(j, k) ∈ B`, `R(x, B) = x R(x, B∖[j,k]) + R(x, B∖(j,k))`, where `B∖[j,k]`
removes row `j` and column `k` and `B∖(j,k)` removes the square `(j, k)`. -/
@[dlmf 26.15.E5]
theorem rookPolynomial_delete {n : ℕ} {B : Finset (Fin n × Fin n)} {j k : Fin n}
    (hjk : (j, k) ∈ B) :
    rookPolynomial B =
      X * rookPolynomial (B.filter fun x => x.1 ≠ j ∧ x.2 ≠ k) +
        rookPolynomial (B.erase (j, k)) := by
  classical
  simp only [q26b_rookPolynomial_eq_sum]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun D => (j, k) ∈ D)]
  congr 1
  · rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun D _ => insert (j, k) D) ?_ ?_ ?_ ?_
    · intro D hD
      simp only [mem_filter, mem_powerset] at hD ⊢
      refine ⟨⟨insert_subset hjk (hD.1.trans (filter_subset _ _)), ?_⟩, mem_insert_self _ _⟩
      intro x hx y hy hxy
      have hrc : ∀ z ∈ D, z.1 ≠ j ∧ z.2 ≠ k := fun z hz => (mem_filter.mp (hD.1 hz)).2
      rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · have := hrc y hy; exact ⟨this.1.symm, this.2.symm⟩
      · exact hrc x hx
      · exact hD.2 x hx y hy hxy
    · intro D hD D' hD' h
      simp only [mem_filter, mem_powerset] at hD hD'
      have hn : ∀ E : Finset (Fin n × Fin n), E ⊆ B.filter (fun x => x.1 ≠ j ∧ x.2 ≠ k) →
          (j, k) ∉ E := fun E hE hm => by simpa using (mem_filter.mp (hE hm)).2
      rw [← erase_insert (hn D hD.1), h, erase_insert (hn D' hD'.1)]
    · intro D hD
      simp only [mem_filter, mem_powerset] at hD
      refine ⟨D.erase (j, k), ?_, insert_erase hD.2⟩
      simp only [mem_filter, mem_powerset]
      refine ⟨fun x hx => ?_, fun x hx y hy hxy =>
        hD.1.2 x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) hxy⟩
      rw [mem_filter]
      refine ⟨hD.1.1 (mem_of_mem_erase hx), ?_⟩
      have h1 := hD.1.2 x (mem_of_mem_erase hx) (j, k) hD.2 (ne_of_mem_erase hx)
      exact h1
    · intro D hD
      simp only [mem_filter, mem_powerset] at hD
      have : (j, k) ∉ D := fun hm => by simpa using (mem_filter.mp (hD.1 hm)).2
      rw [card_insert_of_notMem this, pow_succ, mul_comm]
  · rw [Finset.filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext D
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun x hx => mem_erase.mpr ⟨fun h => h3 (h ▸ hx), h1 hx⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans (erase_subset _ _), h2, fun h => (mem_erase.mp (h1 h)).1 rfl⟩

/-- The number of permutations of `Fin n` fixing every point of `R` is `(n - #R)!`. -/
lemma q26b_card_perm_fix {n : ℕ} (R : Finset (Fin n)) :
    #{τ : Perm (Fin n) | ∀ r ∈ R, τ r = r} = (n - #R).factorial := by
  classical
  rw [← Fintype.card_subtype]
  have e := Perm.subtypeEquivSubtypePerm (fun a : Fin n => a ∉ R)
  rw [← Fintype.card_congr (e.trans (Equiv.subtypeEquivRight fun τ => by simp))]
  rw [Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-- The number of permutations containing a nonattacking placement `C` is `(n - #C)!`. -/
lemma q26b_card_perm_extend {n : ℕ} {C : Finset (Fin n × Fin n)} (hC : IsNonattacking C) :
    #{σ : Perm (Fin n) | ∀ x ∈ C, σ x.1 = x.2} = (n - #C).factorial := by
  classical
  have hinj1 : Function.Injective fun x : C => x.1.1 := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    by_contra hne
    exact (hC x hx y hy fun h' => hne (Subtype.ext h')).1 h
  have hinj2 : Function.Injective fun x : C => x.1.2 := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    by_contra hne
    exact (hC x hx y hy fun h' => hne (Subtype.ext h')).2 h
  obtain ⟨σ0, hσ0⟩ := q26b_exists_perm_comp_of_injective hinj1 hinj2
  have hσ0' : ∀ x ∈ C, σ0 x.1 = x.2 := fun x hx => (congrFun hσ0 ⟨x, hx⟩).symm
  have hR : #(C.image Prod.fst) = #C := card_image_of_injOn fun x hx y hy h => by
    by_contra hne; exact (hC x hx y hy hne).1 h
  rw [← hR, ← q26b_card_perm_fix]
  refine Finset.card_bij (fun σ _ => σ0⁻¹ * σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
    rw [Perm.mul_apply, hσ x hx, ← hσ0' x hx]; simp
  · intro σ _ τ _ h; exact mul_left_cancel h
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ
    refine ⟨σ0 * τ, ?_, by rw [← mul_assoc, inv_mul_cancel, one_mul]⟩
    simp only [mem_filter, mem_univ, true_and]
    intro x hx
    rw [Perm.mul_apply, hτ x.1 (mem_image_of_mem _ hx), hσ0' x hx]

/-- (26.15.7): `N(x, B) = ∑_{k=0}^n r_k(B) (n-k)! (x-1)^k`. -/
@[dlmf 26.15.E7]
theorem hitPolynomial_eq {n : ℕ} (B : Finset (Fin n × Fin n)) :
    hitPolynomial B =
      ∑ k ∈ range (n + 1), C ((rookNumber B k * (n - k).factorial : ℕ) : ℤ) * (X - 1) ^ k := by
  classical
  set NA := B.powerset.filter IsNonattacking with hNA
  set J : Perm (Fin n) → Finset (Fin n) := fun σ => univ.filter fun j => (j, σ j) ∈ B
  -- Step 1
  have h1 : hitPolynomial B = ∑ σ : Perm (Fin n), (X : ℤ[X]) ^ #(J σ) := by
    rw [hitPolynomial, ← Finset.sum_fiberwise_of_maps_to (g := fun σ => #(J σ))
      (t := range (n + 1)) (s := univ) (fun σ _ => by
        rw [mem_range]; exact Nat.lt_succ_of_le ((card_le_univ _).trans (by simp)))]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun σ hσ => by rw [(mem_filter.mp hσ).2]), sum_const,
      nsmul_eq_mul, hitNumber]
    simp only [map_natCast]
    rfl
  -- Step 2
  have h2 : ∀ σ : Perm (Fin n), (X : ℤ[X]) ^ #(J σ) =
      ∑ D ∈ NA.filter (fun D => ∀ x ∈ D, σ x.1 = x.2), (X - 1) ^ #D := by
    intro σ
    have hX : (X : ℤ[X]) ^ #(J σ) = ∏ _j ∈ J σ, ((X - 1) + 1) := by
      rw [prod_const, sub_add_cancel]
    rw [hX, prod_add_one]
    simp only [prod_const]
    refine Finset.sum_bij (fun T _ => T.image fun j => (j, σ j)) ?_ ?_ ?_ ?_
    · intro T hT
      rw [mem_powerset] at hT
      simp only [mem_filter, hNA, mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp (hT hj)).2
      · intro x hx y hy hxy
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        obtain ⟨j, -, rfl⟩ := mem_image.mp hy
        have hij : i ≠ j := fun h => hxy (h ▸ rfl)
        exact ⟨hij, fun h => hij (σ.injective h)⟩
      · intro x hx
        obtain ⟨j, -, rfl⟩ := mem_image.mp hx
        rfl
    · intro T _ T' _ h
      have := congrArg (Finset.image Prod.fst) h
      simpa [Finset.image_image, Function.comp_def] using this
    · intro D hD
      simp only [mem_filter, hNA, mem_powerset] at hD
      refine ⟨D.image Prod.fst, ?_, ?_⟩
      · rw [mem_powerset]
        intro j hj
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
        simp only [J, mem_filter, mem_univ, true_and]
        rw [hD.2 x hx]
        exact hD.1.1 hx
      · ext x
        simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right]
        constructor
        · rintro ⟨j, ⟨k, hjk⟩, rfl⟩
          rw [hD.2 _ hjk]; exact hjk
        · intro hx
          exact ⟨x.1, ⟨x.2, hx⟩, by rw [hD.2 x hx]⟩
    · intro T _
      rw [card_image_of_injective _ (fun i j h => by simpa using congrArg Prod.fst h)]
  -- Step 3
  have h3 : ∑ σ : Perm (Fin n), (X : ℤ[X]) ^ #(J σ) =
      ∑ D ∈ NA, C (((n - #D).factorial : ℕ) : ℤ) * (X - 1) ^ #D := by
    simp_rw [h2, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun D hD => ?_
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    simp only [mem_filter, hNA, mem_powerset] at hD
    rw [q26b_card_perm_extend hD.2]
    simp
  -- Step 4
  rw [h1, h3, ← Finset.sum_fiberwise_of_maps_to (g := fun D => #D) (t := range (n + 1))
    (fun D hD => by
      simp only [hNA, mem_filter] at hD
      rw [mem_range]; exact Nat.lt_succ_of_le (q26b_card_le_of_nonattacking hD.2))]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun D hD => by rw [(mem_filter.mp hD).2]), sum_const, nsmul_eq_mul]
  have hr : #(NA.filter fun D => #D = k) = rookNumber B k := by
    rw [rookNumber, hNA, Finset.filter_filter]
    congr 1
    ext D; simp only [mem_filter]; tauto
  rw [hr]
  simp only [Nat.cast_mul, map_mul, map_natCast]
  ring

/-- (26.15.8): the number of permutations avoiding `B` is
`N_0(B) = N(0, B) = ∑_{k=0}^n (-1)^k r_k(B) (n-k)!`. -/
@[dlmf 26.15.E8]
theorem hitNumber_zero_eq {n : ℕ} (B : Finset (Fin n × Fin n)) :
    (hitNumber B 0 : ℤ) = (hitPolynomial B).eval 0 ∧
      (hitNumber B 0 : ℤ) =
        ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * rookNumber B k * (n - k).factorial := by
  have h0 : (hitPolynomial B).eval 0 = hitNumber B 0 := by
    simp only [hitPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  refine ⟨h0.symm, ?_⟩
  rw [← h0, hitPolynomial_eq]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one, zero_sub]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

/-- The ménage board `{(j, j), (j, j+1) | 1 ≤ j < n} ∪ {(n, n), (n, 1)}` (indices mod `n`). -/
def menageBoard (n : ℕ) [NeZero n] : Finset (Fin n × Fin n) :=
  univ.image (fun i => (i, i)) ∪ univ.image (fun i => (i, i + 1))

/-! ### Helpers for the ménage numbers (26.15.9)

The `2n` squares of the ménage board are arranged in a cycle `(0,0), (0,1), (1,1), (1,2), …`
in which two squares attack each other exactly when they are cyclically adjacent, so
`r_k` counts `k`-subsets of a `2n`-cycle without two adjacent elements. -/

section MenageHelpers

open Fin.NatCast


/-- `k`-subsets of `range M` without two consecutive elements. -/
def s26b_P (M k : ℕ) : ℕ := #{S ∈ (range M).powersetCard k | ∀ i ∈ S, i + 1 ∉ S}

theorem s26b_P_zero_right (M : ℕ) : s26b_P M 0 = 1 := by
  rw [s26b_P, powersetCard_zero, filter_true_of_mem (by simp), card_singleton]

theorem s26b_P_succ_succ (M k : ℕ) :
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

theorem s26b_P_zero_succ (k : ℕ) : s26b_P 0 (k + 1) = 0 := by
  simp [s26b_P]

theorem s26b_P_one_succ_succ (k : ℕ) : s26b_P 1 (k + 2) = 0 := by
  rw [s26b_P, powersetCard_eq_empty.mpr (by simp)]
  rfl

theorem s26b_P_one_one : s26b_P 1 1 = 1 := by decide

theorem s26b_P_eq (M k : ℕ) : s26b_P M k = (M + 1 - k).choose k := by
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

theorem s26b_P_shift (a M k : ℕ) :
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

theorem s26b_Q_zero (N : ℕ) : s26b_Q N 0 = 1 := by
  rw [s26b_Q, powersetCard_zero, filter_true_of_mem (by simp), card_singleton]

theorem s26b_Q_succ {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
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

theorem s26b_Q_formula {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : k ≤ n) :
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

theorem s26b_cast_eq_iff {n : ℕ} [NeZero n] {x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) :
    ((x : Fin n) = (y : Fin n)) ↔ x = y ∨ (x = 0 ∧ y = n) ∨ (x = n ∧ y = 0) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [Fin.ext_iff, Fin.val_natCast, Fin.val_natCast]
  rcases hx.lt_or_eq with hx | rfl <;> rcases hy.lt_or_eq with hy | rfl
  · rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]; omega
  · rw [Nat.mod_eq_of_lt hx, Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt hy, Nat.mod_self]; omega
  · simp

theorem s26b_image_ψ {n : ℕ} [NeZero n] : (range (2 * n)).image (s26b_ψ n) = menageBoard n := by
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

theorem s26b_injOn_ψ {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Set.InjOn (s26b_ψ n) (range (2 * n) : Set ℕ) := by
  intro a ha b hb h
  have ha := mem_range.mp ha; have hb := mem_range.mp hb
  simp only [s26b_ψ, Prod.mk.injEq] at h
  rw [s26b_cast_eq_iff (by omega) (by omega), s26b_cast_eq_iff (by omega) (by omega)] at h
  omega

theorem s26b_adj {n : ℕ} [NeZero n] (hn : 2 ≤ n) {a b : ℕ} (ha : a < 2 * n) (hb : b < 2 * n) :
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

theorem s26b_nonattacking_iff {n : ℕ} [NeZero n] (hn : 2 ≤ n) {S : Finset ℕ}
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

theorem s26b_filter_image_ψ {n : ℕ} [NeZero n] (hn : 2 ≤ n) {S : Finset ℕ}
    (hS : S ⊆ range (2 * n)) :
    (range (2 * n)).filter (fun m => s26b_ψ n m ∈ S.image (s26b_ψ n)) = S := by
  ext m
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hm, a, ha, e⟩
    rwa [← s26b_injOn_ψ hn (coe_subset.mpr hS ha) hm e]
  · intro hm; exact ⟨hS hm, m, hm, rfl⟩

theorem s26b_image_filter_ψ {n : ℕ} [NeZero n] {C : Finset (Fin n × Fin n)}
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

theorem s26b_rook_menage {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) :
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
theorem s26b_mem_NA {n : ℕ} {b : Fin n → ℕ} {m k : ℕ} {C : Finset (Fin n × Fin n)} :
    C ∈ s26b_NA b m k ↔ (∀ x ∈ C, (x.2 : ℕ) < b x.1 ∧ (x.1 : ℕ) < m) ∧ C.card = k ∧
      IsNonattacking C := by
  simp only [s26b_NA, mem_filter, mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun x hx => by simpa [s26b_fb, ferrersBoard] using h1 hx, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun x hx => by simpa [s26b_fb, ferrersBoard] using h1 x hx, h2⟩

/-- Distinct columns: a placement on `m` columns has at most `m` rooks. -/
theorem s26b_card_le {n : ℕ} {b : Fin n → ℕ} {m k : ℕ} {C : Finset (Fin n × Fin n)}
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
theorem s26b_NA_succ {n : ℕ} {b : Fin n → ℕ} (hb : Monotone b) (hbn : ∀ j, b j ≤ n) {m : ℕ}
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
theorem s26b_NA_zero {n : ℕ} (b : Fin n → ℕ) (m : ℕ) : #(s26b_NA b m 0) = 1 := by
  rw [card_eq_one]
  refine ⟨∅, ?_⟩
  ext C
  simp only [mem_singleton, s26b_mem_NA, card_eq_zero]
  constructor
  · exact fun h => h.2.1
  · rintro rfl; exact ⟨by simp, rfl, by simp [IsNonattacking]⟩

/-- No placement of more rooks than columns. -/
theorem s26b_NA_gt {n : ℕ} (b : Fin n → ℕ) {m k : ℕ} (h : m < k) : #(s26b_NA b m k) = 0 := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro C hC
  have := s26b_card_le hC
  omega

/-- All `n` columns give the rook numbers of the board. -/
theorem s26b_NA_full {n : ℕ} (b : Fin n → ℕ) (k : ℕ) :
    #(s26b_NA b n k) = rookNumber (ferrersBoard b) k := by
  have : s26b_fb b n = ferrersBoard b :=
    filter_true_of_mem fun (x : Fin n × Fin n) _ => x.1.isLt
  rw [s26b_NA, this, rookNumber]

/-- `(X + c) (x)_k = (x)_{k+1} + (c + k) (x)_k`. -/
theorem s26b_X_add_mul_desc (c : ℤ) (k : ℕ) :
    (X + C c) * descPochhammer ℤ k = descPochhammer ℤ (k + 1) + C (c + k) * descPochhammer ℤ k := by
  rw [descPochhammer_succ_right, map_add, map_natCast]; ring

/-- `b` extended by `0` to all of `ℕ`. -/
def s26b_bb {n : ℕ} (b : Fin n → ℕ) (j : ℕ) : ℕ := if h : j < n then b ⟨j, h⟩ else 0

/-- The column-by-column form of the Ferrers board identity. -/
theorem s26b_ferrers_poly {n : ℕ} {b : Fin n → ℕ} (hb : Monotone b) (hbn : ∀ j, b j ≤ n) :
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
theorem s26b_descPochhammer_coeff_unique (N : ℕ) (d : ℕ → ℤ)
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
