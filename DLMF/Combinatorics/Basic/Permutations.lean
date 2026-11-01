/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Perm
public import DLMF.QSeries.Basic.Calculus

/-!
# Permutation statistics, rook polynomials and `q`-multinomials (DLMF §§26.13–26.16)

The statistics of permutations and words used in DLMF §§26.13–26.16, the rook and hit numbers
of §26.15, and the `q`-multinomial coefficient of §26.16.

## Main definitions

* `numCycles`: the number of cycles of a permutation, fixed points included (DLMF §26.13).
* `wordInversions`, `wordDescentSet`, `wordMajorIndex`: inversions, descents and the major
  index of a word `w : Fin n → ℕ` (DLMF 26.14.1, 26.14.2).
* `inversionNumber`, `descentNumber`, `majorIndex`: the same statistics of a permutation.
* `eulerianNumber`: `⟨n k⟩`, the number of `σ ∈ 𝔖_n` with exactly `k` descents.
* `excedanceNumber`, `weakExcedanceNumber`: the numbers of (weak) excedances.
* `IsNonattacking`, `rookNumber`, `rookPolynomial`, `hitNumber`, `hitPolynomial`: rook
  placements and the polynomials 26.15.3, 26.15.6.
* `qMultinomial`: the `q`-multinomial coefficient (DLMF 26.16.1).

## Main results

* `descentNumber_eq_zero_iff`: the identity is the only permutation without descents.

## Implementation notes

Positions in words are `0`-based (`Fin n`); the major index adds `1` to each descent position,
as DLMF counts positions from `1`. The cycle and transposition results of §26.13 are in
`DLMF.Combinatorics.Permutations.CyclesAndExcedances`, the Eulerian-number identities in
`DLMF.Combinatorics.Permutations.EulerianNumbers`, the rook-polynomial identities in
`DLMF.Combinatorics.Permutations.RookPolynomials` and the multiset permutations in
`DLMF.Combinatorics.MultisetPermutations`.
-/

@[expose] public section

noncomputable section

open Finset Equiv Polynomial

namespace DLMF.Combinatorics

/-- The number of cycles of `σ`, fixed points included: the length of its cycle type
`(a_1, …, a_n)` counted with multiplicity, `a_1 + ⋯ + a_n`. -/
@[dlmf 26.13]
def numCycles {n : ℕ} (σ : Perm (Fin n)) : ℕ := σ.partition.parts.card

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

/-- The Eulerian number `⟨n k⟩`: permutations of `{1, …, n}` with exactly `k` descents
(DLMF §26.14(i)). -/
@[dlmf 26.14.i]
def eulerianNumber (n k : ℕ) : ℕ := #{σ : Perm (Fin n) | descentNumber σ = k}

/-- The number of excedances `σ(j) > j` of `σ`. -/
def excedanceNumber {n : ℕ} (σ : Perm (Fin n)) : ℕ := #{j : Fin n | j < σ j}

/-- The number of weak excedances `σ(j) ≥ j` of `σ`. -/
def weakExcedanceNumber {n : ℕ} (σ : Perm (Fin n)) : ℕ := #{j : Fin n | j ≤ σ j}

/-- Membership in the descent set of a permutation. -/
private lemma combBasic_mem_wordDescentSet_perm {n : ℕ} (σ : Perm (Fin n)) (j : ℕ) :
    j ∈ wordDescentSet (fun i => (σ i : ℕ)) ↔ ∃ h : j + 1 < n, σ ⟨j + 1, h⟩ < σ ⟨j, by omega⟩ := by
  simp only [wordDescentSet, mem_filter, mem_range, Fin.lt_def]
  constructor
  · rintro ⟨-, h, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨by omega, h, h'⟩


/-- The only permutation without descents is the identity. -/
lemma descentNumber_eq_zero_iff {n : ℕ} (σ : Perm (Fin n)) : descentNumber σ = 0 ↔ σ = 1 := by
  constructor
  · intro h
    have hD : ∀ j (hj : j + 1 < n), σ ⟨j, by omega⟩ < σ ⟨j + 1, hj⟩ := by
      intro j hj
      have hj' : j ∉ wordDescentSet (fun i => (σ i : ℕ)) := by
        rw [descentNumber, Finset.card_eq_zero] at h; rw [h]; exact Finset.notMem_empty j
      rw [combBasic_mem_wordDescentSet_perm] at hj'
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
    obtain ⟨h, h'⟩ := (combBasic_mem_wordDescentSet_perm _ j).1 hj
    simp only [Perm.one_apply, Fin.mk_lt_mk] at h'
    omega

/-- A set of squares of the `n × n` board is nonattacking if no two share a row or a column. -/
def IsNonattacking {n : ℕ} (C : Finset (Fin n × Fin n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x.1 ≠ y.1 ∧ x.2 ≠ y.2

/-- The nonattacking condition on a finite rook placement is decidable. -/
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

/-- (26.16.1): the `q`-multinomial coefficient
`[a_1+⋯+a_m; a_1, …, a_m]_q = ∏_{k=1}^{m-1} [a_k + a_{k+1} + ⋯ + a_m, a_k]_q`. -/
@[dlmf 26.16.E1]
def qMultinomial (q : ℂ) {m : ℕ} (a : Fin m → ℕ) : ℂ :=
  ∏ k : Fin m, DLMF.QSeries.qBinom q (∑ i ∈ univ.filter (k ≤ ·), a i) (a k)

end DLMF.Combinatorics

end

end
