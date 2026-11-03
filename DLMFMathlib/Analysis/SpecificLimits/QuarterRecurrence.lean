/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Decay of sequences dominated by a quarter of their neighbours

A nonnegative bounded sequence with `f (k+1) ≤ (f k + f (k+2))/4` for all large `k` (a
discrete maximum principle, as for the minimal solutions of diagonally dominant three-term
recurrences) halves at each step, hence decays geometrically.

## Main results

* `succ_le_half_of_le_add_div_four`: `f (k+1) ≤ f k / 2` from the threshold on.
* `le_mul_half_pow_of_le_add_div_four`: the bound `f k ≤ M 2^J (1/2)^k`.
-/

@[expose] public section

/-- A nonnegative bounded sequence with `f (k+1) ≤ (f k + f (k+2))/4` for `k ≥ J` satisfies
`f (k+1) ≤ f k / 2` for `k ≥ J`. -/
theorem succ_le_half_of_le_add_div_four {f : ℕ → ℝ} (h0 : ∀ k, 0 ≤ f k) {B : ℝ}
    (hB : ∀ k, f k ≤ B) {J : ℕ} (h : ∀ k ≥ J, f (k + 1) ≤ (f k + f (k + 2)) / 4) :
    ∀ k ≥ J, f (k + 1) ≤ f k / 2 := by
  intro k hk
  by_contra hlt
  push Not at hlt
  have key : ∀ i : ℕ, f (k + i) / 2 < f (k + i + 1) ∧ 2 ^ i * f (k + 1) ≤ f (k + 1 + i) := by
    intro i
    induction i with
    | zero => exact ⟨by simpa using hlt, by simp⟩
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih
      have hr := h (k + i) (by omega)
      have hnn := h0 (k + i)
      have e1 : k + (i + 1) = k + i + 1 := by ring
      have e2 : k + i + 1 + 1 = k + i + 2 := by ring
      have e3 : k + 1 + (i + 1) = k + i + 2 := by ring
      have e4 : k + 1 + i = k + i + 1 := by ring
      rw [e1, e2, e3]
      rw [e4] at h2
      have hlt2 : 2 * f (k + i + 1) < f (k + i + 2) := by linarith
      have hnn1 := h0 (k + i + 1)
      refine ⟨by linarith, ?_⟩
      rw [pow_succ]; nlinarith
  have hpos : 0 < f (k + 1) := lt_of_le_of_lt (div_nonneg (h0 k) zero_le_two) hlt
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (B / f (k + 1)) (by norm_num : (1 : ℝ) < 2)
  have := (key i).2
  have hb := hB (k + 1 + i)
  rw [div_lt_iff₀ hpos] at hi
  linarith

/-- Geometric decay with ratio `1/2`: under the hypotheses of `succ_le_half_of_le_add_div_four`
and a bound `f k ≤ M` for `k ≤ J`, `f k ≤ M 2^J (1/2)^k` for all `k`. -/
theorem le_mul_half_pow_of_le_add_div_four {f : ℕ → ℝ} (h0 : ∀ k, 0 ≤ f k) {B : ℝ}
    (hB : ∀ k, f k ≤ B) {J : ℕ} (h : ∀ k ≥ J, f (k + 1) ≤ (f k + f (k + 2)) / 4) {M : ℝ}
    (hM : ∀ k ≤ J, f k ≤ M) : ∀ k, f k ≤ M * 2 ^ J * (1 / 2) ^ k := by
  have hhalf := succ_le_half_of_le_add_div_four h0 hB h
  have hM0 : 0 ≤ M := (h0 0).trans (hM 0 (Nat.zero_le _))
  have hdec : ∀ i, f (J + i) ≤ M * (1 / 2) ^ i := by
    intro i
    induction i with
    | zero => simpa using hM J le_rfl
    | succ i ih =>
      have := hhalf (J + i) (by omega)
      rw [← add_assoc, pow_succ]; linarith
  intro k
  rcases le_or_gt k J with hk | hk
  · refine (hM k hk).trans ?_
    have : (1 : ℝ) ≤ 2 ^ J * (1 / 2) ^ k := by
      rw [show J = k + (J - k) by omega, pow_add, mul_comm (2 ^ k : ℝ), mul_assoc,
        ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, mul_one]
      exact one_le_pow₀ (by norm_num)
    nlinarith
  · obtain ⟨i, rfl⟩ : ∃ i, k = J + i := ⟨k - J, by omega⟩
    refine (hdec i).trans (le_of_eq ?_)
    rw [pow_add, ← mul_assoc, mul_assoc M, ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      one_pow, mul_one]
