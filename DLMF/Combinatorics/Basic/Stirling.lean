/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Signed Stirling numbers of the first kind (DLMF §26.8(i))

DLMF's Stirling numbers of the first kind `s(n, k)` are signed: `(-1)^{n-k}` times the number
of permutations of `{1, …, n}` with exactly `k` cycles. Mathlib's `Nat.stirlingFirst n k` is the
unsigned number, so the DLMF function is `signedStirlingFirst n k`. DLMF's `S(n, k)` is Mathlib's
`Nat.stirlingSecond n k` itself.

## Main definitions

* `signedStirlingFirst`: DLMF's signed `s(n, k)`.

## Main results

* `signedStirlingFirst_zero_zero`, `signedStirlingFirst_zero_succ`,
  `signedStirlingFirst_succ_zero`, `signedStirlingFirst_eq_zero_of_lt`: boundary values.
* `neg_one_pow_mul_signedStirlingFirst`: the sign relation with `Nat.stirlingFirst`.
* `signedStirlingFirst_succ_succ`, `signedStirlingFirst_succ_zero'`: the recurrence 26.8.18.
* `signedStirlingFirst_self`, `signedStirlingFirst_one`: DLMF 26.8.1, 26.8.2.
* `signedStirlingFirst_zero_right`, `signedStirlingFirst_one_right`,
  `signedStirlingFirst_two_right`, `neg_signedStirlingFirst_pred_self`,
  `stirlingSecond_zero_one_right`, `stirlingSecond_two_right`: special values
  (DLMF 26.8.14–26.8.17).

## Implementation notes

The explicit forms, the falling-factorial expansions and the generating functions are in
`DLMF.Combinatorics.Stirling.DefinitionsAndSeries`; further identities and asymptotics are in
the other modules of `DLMF.Combinatorics.Stirling`.
-/

@[expose] public section

noncomputable section

open Finset

namespace DLMF.Combinatorics

/-- DLMF §26.8(i): the (signed) Stirling number of the first kind
`s(n, k) = (-1)^{n-k} · #{permutations of {1,…,n} with exactly k cycles}`, written with
Mathlib's unsigned `Nat.stirlingFirst`. It is `0` for `k > n`. -/
@[dlmf 26.8.i]
def signedStirlingFirst (n k : ℕ) : ℤ := (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst 0 0 = 1`. -/
@[simp] theorem signedStirlingFirst_zero_zero : signedStirlingFirst 0 0 = 1 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_zero]

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst 0 (k + 1) =
0`. -/
@[simp] theorem signedStirlingFirst_zero_succ (k : ℕ) : signedStirlingFirst 0 (k + 1) = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_zero_succ]

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst (n + 1) 0 =
0`. -/
@[simp] theorem signedStirlingFirst_succ_zero (n : ℕ) : signedStirlingFirst (n + 1) 0 = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_succ_zero]

/-- Identity under the stated parameter and domain assumptions: `signedStirlingFirst n k = 0`. -/
theorem signedStirlingFirst_eq_zero_of_lt {n k : ℕ} (h : n < k) : signedStirlingFirst n k = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_eq_zero_of_lt h]

/-- The sign relation: `(-1)^{n-k} s(n, k)` is the unsigned Stirling number. -/
theorem neg_one_pow_mul_signedStirlingFirst (n k : ℕ) :
    (-1) ^ (n - k) * signedStirlingFirst n k = Nat.stirlingFirst n k := by
  rw [signedStirlingFirst, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-- DLMF 26.8.18: `s(n, k) = s(n-1, k-1) - (n-1) s(n-1, k)`, written with `n + 1`, `k + 1`
(valid for all `n, k ≥ 0`). -/
@[dlmf 26.8.E18]
theorem signedStirlingFirst_succ_succ (n k : ℕ) :
    signedStirlingFirst (n + 1) (k + 1) =
      signedStirlingFirst n k - n * signedStirlingFirst n (k + 1) := by
  simp only [signedStirlingFirst, Nat.stirlingFirst_succ_succ, Nat.add_sub_add_right]
  push_cast
  rcases lt_or_ge k n with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
    have e1 : k + 1 + d - k = d + 1 := by omega
    have e2 : k + 1 + d - (k + 1) = d := by omega
    rw [e1, e2, pow_succ]; ring
  · rw [Nat.stirlingFirst_eq_zero_of_lt (by omega : n < k + 1), Nat.sub_eq_zero_of_le h]
    simp

/-- DLMF 26.8.18 at `k = 0`: `s(n+1, 0) = -n s(n, 0)` (both sides vanish). -/
@[dlmf 26.8.E18]
theorem signedStirlingFirst_succ_zero' (n : ℕ) :
    signedStirlingFirst (n + 1) 0 = -(n * signedStirlingFirst n 0) := by
  cases n <;> simp

/-! ### Basic values -/

/-- DLMF 26.8.1: `s(n, n) = 1`. -/
@[dlmf 26.8.E1]
theorem signedStirlingFirst_self (n : ℕ) : signedStirlingFirst n n = 1 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_self]

/-- DLMF 26.8.2: `s(1, k) = δ_{1,k}`. -/
@[dlmf 26.8.E2]
theorem signedStirlingFirst_one (k : ℕ) : signedStirlingFirst 1 k = if k = 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · simp
  · simp [signedStirlingFirst_self]
  · simp [signedStirlingFirst_eq_zero_of_lt (by omega : 1 < k + 2)]

/-! ### Special values (§26.8(iii)) -/

/-- DLMF 26.8.14 (first): `s(n, 0) = 0` for `n ≥ 1`. -/
@[dlmf 26.8.E14]
theorem signedStirlingFirst_zero_right {n : ℕ} (hn : 1 ≤ n) : signedStirlingFirst n 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp

/-- DLMF 26.8.14 (second): `s(n, 1) = (-1)^{n-1} (n-1)!` for `n ≥ 1`. -/
@[dlmf 26.8.E14]
theorem signedStirlingFirst_one_right {n : ℕ} (hn : 1 ≤ n) :
    signedStirlingFirst n 1 = (-1) ^ (n - 1) * ((n - 1).factorial : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [signedStirlingFirst, Nat.stirlingFirst_one_right]

/-- The unsigned `c(n+1, 2) = n! H_n`. -/
private lemma combBasic_stirlingFirst_succ_two (n : ℕ) :
    (Nat.stirlingFirst (n + 1) 2 : ℚ) = n.factorial * harmonic n := by
  induction n with
  | zero => simp [Nat.stirlingFirst_eq_zero_of_lt]
  | succ n ih =>
    rw [Nat.stirlingFirst_succ_succ, Nat.stirlingFirst_one_right]
    push_cast
    rw [ih, harmonic_succ, Nat.factorial_succ]
    push_cast
    field_simp

/-- DLMF 26.8.15: `s(n, 2) = (-1)ⁿ (n-1)! (1 + 1/2 + ⋯ + 1/(n-1))` for `n ≥ 1`
(`harmonic (n-1)` is the harmonic number `H_{n-1}`). -/
@[dlmf 26.8.E15]
theorem signedStirlingFirst_two_right {n : ℕ} (hn : 1 ≤ n) :
    (signedStirlingFirst n 2 : ℚ) = (-1) ^ n * (n - 1).factorial * harmonic (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · simp [signedStirlingFirst, Nat.stirlingFirst_eq_zero_of_lt]
  · simp only [signedStirlingFirst, Nat.add_sub_cancel]
    push_cast
    rw [combBasic_stirlingFirst_succ_two, pow_succ, pow_succ]
    ring

/-- DLMF 26.8.16: `-s(n, n-1) = S(n, n-1) = C(n, 2)` for `n ≥ 1`. -/
@[dlmf 26.8.E16]
theorem neg_signedStirlingFirst_pred_self {n : ℕ} (hn : 1 ≤ n) :
    -signedStirlingFirst n (n - 1) = Nat.stirlingSecond n (n - 1) ∧
      (Nat.stirlingSecond n (n - 1) : ℤ) = n.choose 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, signedStirlingFirst, Nat.stirlingFirst_succ_self_left,
    Nat.stirlingSecond_succ_self_left, show m + 1 - m = 1 by omega]
  simp

/-- DLMF 26.8.17 (first two): `S(n, 0) = 0` and `S(n, 1) = 1` for `n ≥ 1`. -/
@[dlmf 26.8.E17]
theorem stirlingSecond_zero_one_right {n : ℕ} (hn : 1 ≤ n) :
    Nat.stirlingSecond n 0 = 0 ∧ Nat.stirlingSecond n 1 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨Nat.stirlingSecond_succ_zero m, Nat.stirlingSecond_one_right m⟩

/-- DLMF 26.8.17 (third): `S(n, 2) = 2^{n-1} - 1` for `n ≥ 1`. -/
@[dlmf 26.8.E17]
theorem stirlingSecond_two_right {n : ℕ} (hn : 1 ≤ n) :
    (Nat.stirlingSecond n 2 : ℤ) = 2 ^ (n - 1) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero => simp [Nat.stirlingSecond_eq_zero_of_lt]
  | succ m ih =>
    rw [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_one_right]
    push_cast
    rw [ih (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

end DLMF.Combinatorics

end

end
