/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Strict positivity of Stirling numbers

Temme, *Special Functions*, Chapter 1, (1.26)–(1.29), pp. 18–20
(synopsis TEM-01-15). Mathlib's numbers of the first kind are unsigned;
the signed first-kind convention follows by multiplying by `(-1)^(n-k)`.
-/

@[expose] public section

namespace Nat

/-- Unsigned Stirling numbers of the first kind are positive in their nonzero triangle.
Temme, *Special Functions*, Chapter 1, (1.26)–(1.29), synopsis TEM-01-15. -/
theorem stirlingFirst_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    0 < stirlingFirst n k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    obtain ⟨k, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    by_cases hkzero : k = 0
    · subst k
      simpa only [zero_add, stirlingFirst_one_right] using factorial_pos n
    · rw [stirlingFirst_succ_succ]
      have hpos := ih (Nat.pos_of_ne_zero hkzero) (by omega : k ≤ n)
      omega

/-- Stirling numbers of the second kind are positive in their nonzero triangle.
Temme, *Special Functions*, Chapter 1, (1.26)–(1.29), synopsis TEM-01-15. -/
theorem stirlingSecond_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    0 < stirlingSecond n k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    obtain ⟨k, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    by_cases hkzero : k = 0
    · subst k
      simp only [stirlingSecond_one_right, zero_lt_one]
    · rw [stirlingSecond_succ_succ]
      have hpos := ih (Nat.pos_of_ne_zero hkzero) (by omega : k ≤ n)
      omega

end Nat
