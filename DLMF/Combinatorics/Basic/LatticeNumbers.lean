/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Delannoy, Motzkin and Narayana numbers (DLMF §26.6(i))

The lattice-path numbers of DLMF §26.6 that have no Mathlib counterpart, with their defining
recurrences and the explicit Narayana formula. The Catalan and large Schröder numbers are
Mathlib's `catalan` and `largeSchroder`.

## Main definitions

* `delannoy`: the Delannoy number `D(m, n)`, by the recurrence 26.6.10.
* `motzkin`: the Motzkin number `M(n)`, by the recurrence 26.6.11.
* `narayana`: the Narayana number `N(n, k)`, by the explicit formula 26.6.3, with `N(n, 0) = 0`.

## Main results

* `delannoy_zero_left`, `delannoy_zero_right`, `delannoy_succ_succ`: boundary values and the
  recurrence 26.6.10.
* `motzkin_eq`: the recurrence 26.6.11.
* `narayana_mul`, `narayana_eq`: the explicit formula 26.6.3.

## Implementation notes

The lattice-path interpretations, explicit sums, generating functions and the relations with
the Catalan numbers are in `DLMF.Combinatorics.LatticePaths`.
-/

@[expose] public section

noncomputable section

open Finset

namespace DLMF.Combinatorics

/-! ### Definitions (§26.6(i)) -/

/-- DLMF §26.6(i): the Delannoy number `D(m, n)`, defined by `D(0, n) = D(m, 0) = 1` and the
recurrence 26.6.10. -/
@[dlmf 26.6.i]
def delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | m + 1, n + 1 => delannoy m (n + 1) + delannoy (m + 1) n + delannoy m n

/-- Identity under the stated parameter and domain assumptions: `delannoy 0 n = 1`. -/
@[simp] theorem delannoy_zero_left (n : ℕ) : delannoy 0 n = 1 := by cases n <;> simp [delannoy]

/-- Identity under the stated parameter and domain assumptions: `delannoy m 0 = 1`. -/
@[simp] theorem delannoy_zero_right (m : ℕ) : delannoy m 0 = 1 := by cases m <;> simp [delannoy]

/-- DLMF 26.6.10: `D(m, n) = D(m, n-1) + D(m-1, n) + D(m-1, n-1)`, `m, n ≥ 1` (written with
`m + 1`, `n + 1`). -/
@[dlmf 26.6.E10]
theorem delannoy_succ_succ (m n : ℕ) :
    delannoy (m + 1) (n + 1) = delannoy (m + 1) n + delannoy m (n + 1) + delannoy m n := by
  rw [delannoy]; ring

/-- DLMF §26.6(i): the Motzkin number `M(n)`, defined by `M(0) = 1` and the recurrence 26.6.11,
`M(n+1) = M(n) + ∑_{i=0}^{n-1} M(i) M(n-1-i)`. -/
@[dlmf 26.6.i]
def motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 => motzkin n + ∑ i : Fin n,
      have := i.2
      have : n - 1 - i < n + 1 := by omega
      motzkin i * motzkin (n - 1 - i)

/-- DLMF 26.6.11: `M(n) = M(n-1) + ∑_{k=2}^{n} M(k-2) M(n-k)`, `n ≥ 2`. -/
@[dlmf 26.6.E11]
theorem motzkin_eq {n : ℕ} (hn : 2 ≤ n) :
    motzkin n = motzkin (n - 1) + ∑ k ∈ Icc 2 n, motzkin (k - 2) * motzkin (n - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [motzkin, Nat.add_sub_cancel]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => motzkin i * motzkin (m - 1 - i)) m]
  rw [show Icc 2 (m + 1) = (range m).map ⟨(· + 2), add_left_injective 2⟩ by
    ext k; simp only [mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨k - 2, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega, sum_map]
  refine sum_congr rfl fun i hi => ?_
  simp only [Function.Embedding.coeFn_mk, Nat.add_sub_cancel]
  congr 2; omega

/-- DLMF §26.6(i): the Narayana number `N(n, k) = C(n, k) C(n, k-1) / n` (26.6.3), with
`N(n, 0) = 0`. The division is exact (`narayana_mul`). -/
@[dlmf 26.6.i]
def narayana : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 => n.choose (k + 1) * n.choose k / n

/-- The divisibility behind `narayana`: `n ∣ C(n, k+1) C(n, k)`. -/
private lemma combBasic_dvd_choose_succ_mul_choose (n k : ℕ) :
    n ∣ n.choose (k + 1) * n.choose k := by
  rcases n with _ | a
  · simp
  · -- `(a+2) C(a+1,k+1) C(a+1,k) = (a+1) C(a,k) C(a+2,k+1)`
    have h1 := Nat.add_one_mul_choose_eq a k
    have h2 := Nat.add_one_mul_choose_eq (a + 1) k
    have key : (a + 1).choose (k + 1) * (a + 1).choose k * (a + 1 + 1) =
        (a + 1) * (a.choose k * (a + 1 + 1).choose (k + 1)) := by
      have : (a + 1).choose (k + 1) * (a + 1).choose k * (a + 1 + 1) * (k + 1) =
          (a + 1) * (a.choose k * (a + 1 + 1).choose (k + 1)) * (k + 1) := by
        calc _ = (a + 1).choose (k + 1) * ((a + 1 + 1) * (a + 1).choose k) * (k + 1) := by ring
          _ = (a + 1).choose (k + 1) * ((a + 1 + 1).choose (k + 1) * (k + 1)) * (k + 1) := by
            rw [h2]
          _ = ((a + 1).choose (k + 1) * (k + 1)) * (a + 1 + 1).choose (k + 1) * (k + 1) := by ring
          _ = _ := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    have hcop : Nat.Coprime (a + 1) (a + 1 + 1) :=
      Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    exact hcop.dvd_of_dvd_mul_right ⟨_, key⟩

/-- DLMF 26.6.3: `n N(n, k) = C(n, k) C(n, k-1)` for `k ≥ 1`. -/
theorem narayana_mul (n k : ℕ) : n * narayana n (k + 1) = n.choose (k + 1) * n.choose k := by
  rw [narayana, Nat.mul_div_cancel' (combBasic_dvd_choose_succ_mul_choose n k)]

/-- DLMF 26.6.3: `N(n, k) = (1/n) C(n, k) C(n, k-1)`, `n, k ≥ 1`. -/
@[dlmf 26.6.E3]
theorem narayana_eq {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (narayana n k : ℚ) = (n.choose k * n.choose (k - 1) : ℚ) / n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := narayana_mul n j
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Nat.add_sub_cancel, eq_div_iff hn', mul_comm]
  exact_mod_cast this

end DLMF.Combinatorics

end

end
