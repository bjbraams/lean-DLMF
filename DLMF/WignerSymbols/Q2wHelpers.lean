/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic

/-!
# Factorial and cast helpers for the Wigner symbols (DLMF Chapter 34)

Rewriting lemmas for `factQ` and `invFactQ` at natural-number arguments with numeral offsets,
and the tactics `q2w_casts` and `q2w_fin` that turn a closed-form evaluation of a `3j` or `6j`
symbol (after substitution of natural-number parameters) into a rational-function identity
and close it. Used by the single-term and two-term evaluations in
`DLMF.WignerSymbols.ThreeJ` and `DLMF.WignerSymbols.SixJ`.
-/

@[expose] public noncomputable section

namespace DLMF.WignerSymbols

/-- `(1 + n)! = (1 + n) n!`. -/
theorem q2w_factorial_one_add (n : ℕ) :
    ((1 + n).factorial : ℝ) = ((1 + n : ℕ) : ℝ) * (n.factorial : ℝ) := by
  rw [Nat.add_comm, Nat.factorial_succ]; push_cast; ring

/-- Fold a numeral plus a natural-number cast into one cast. -/
theorem q2w_ofNat_add (k m : ℕ) [k.AtLeastTwo] :
    (no_index (OfNat.ofNat k) : ℚ) + (m : ℚ) = ((OfNat.ofNat k + m : ℕ) : ℚ) := by push_cast; ring
/-- Fold a natural-number cast times a numeral into one cast. -/
lemma q2w_mul_ofNat (k m : ℕ) [k.AtLeastTwo] :
    (m : ℚ) * (no_index (OfNat.ofNat k) : ℚ) = ((m * OfNat.ofNat k : ℕ) : ℚ) := by push_cast; ring
/-- `1! = 1`. -/
@[simp] theorem q2w_factQ_one : factQ 1 = 1 := by simp [factQ]
/-- `1/1! = 1`. -/
@[simp] theorem q2w_invFactQ_one : invFactQ 1 = 1 := by simp [invFactQ, factQ]
/-- `factQ` at a numeral. -/
theorem q2w_factQ_ofNat (k : ℕ) [k.AtLeastTwo] :
    factQ (no_index (OfNat.ofNat k) : ℚ) = ((OfNat.ofNat k : ℕ).factorial : ℝ) := by
  rw [← factQ_natCast]; norm_num
/-- `invFactQ` at a numeral. -/
theorem q2w_invFactQ_ofNat (k : ℕ) [k.AtLeastTwo] :
    invFactQ (no_index (OfNat.ofNat k) : ℚ) = ((OfNat.ofNat k : ℕ).factorial : ℝ)⁻¹ := by
  rw [← invFactQ_natCast]; norm_num

/-- `(2 + n)! = (2 + n) (1 + n)!`. -/
theorem q2w_factorial_two_add (n : ℕ) :
    ((2 + n).factorial : ℝ) = ((2 + n : ℕ) : ℝ) * ((1 + n).factorial : ℝ) := by
  rw [show 2 + n = (1 + n) + 1 by omega, Nat.factorial_succ]; push_cast; ring
/-- `(3 + n)! = (3 + n) (2 + n)!`. -/
theorem q2w_factorial_three_add (n : ℕ) :
    ((3 + n).factorial : ℝ) = ((3 + n : ℕ) : ℝ) * ((2 + n).factorial : ℝ) := by
  rw [show 3 + n = (2 + n) + 1 by omega, Nat.factorial_succ]; push_cast; ring
/-- `(4 + n)! = (4 + n) (3 + n)!`. -/
theorem q2w_factorial_four_add (n : ℕ) :
    ((4 + n).factorial : ℝ) = ((4 + n : ℕ) : ℝ) * ((3 + n).factorial : ℝ) := by
  rw [show 4 + n = (3 + n) + 1 by omega, Nat.factorial_succ]; push_cast; ring

/-- `1/(n-1)! = n/n!`, including `n = 0` (both sides vanish). -/
theorem q2w_invFactQ_neg_one_add (n : ℕ) :
    invFactQ (-1 + (n : ℚ)) = (n : ℝ) * ((n.factorial : ℝ))⁻¹ := by
  rcases n with _ | m
  · rw [invFactQ_of_neg (by norm_num)]; simp
  · rw [invFactQ_of_eq (n := m) (by push_cast; ring), Nat.factorial_succ]
    push_cast
    field_simp

/-- `1/(n-2)! = n(n-1)/n!`, including `n = 0, 1` (both sides vanish). -/
lemma q2w_invFactQ_neg_two_add (n : ℕ) :
    invFactQ (-2 + (n : ℚ)) = (n : ℝ) * ((n : ℝ) - 1) * ((n.factorial : ℝ))⁻¹ := by
  rcases n with _ | _ | m
  · rw [invFactQ_of_neg (by norm_num)]; simp
  · rw [invFactQ_of_neg (by norm_num)]; simp
  · rw [invFactQ_of_eq (n := m) (by push_cast; ring), Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `1/(-1)! = 0`. -/
theorem q2w_invFactQ_neg_one : invFactQ (-1) = 0 := invFactQ_of_neg (by norm_num)

/-- `1/(-k)! = 0` for a numeral `k ≥ 2`. -/
lemma q2w_invFactQ_neg_ofNat (k : ℕ) [k.AtLeastTwo] :
    invFactQ (-(no_index (OfNat.ofNat k) : ℚ)) = 0 :=
  invFactQ_of_neg (by
    have : (2 : ℚ) ≤ (OfNat.ofNat k : ℚ) := by
      rw [← Nat.cast_ofNat (R := ℚ) (n := k)]; exact_mod_cast Nat.AtLeastTwo.prop
    linarith)

/-- `√x = R / √Y` when `x = R² / Y` with `R, Y ≥ 0`. -/
theorem q2w_sqrt_eq_div {x R Y : ℝ} (hR : 0 ≤ R) (hY : 0 ≤ Y) (hx : x = R ^ 2 / Y) :
    Real.sqrt x = R / Real.sqrt Y := by
  rw [hx, Real.sqrt_div' _ hY, Real.sqrt_sq hR]

/-- Rewrite the factorials of natural-number arguments (left side normalized by `ring_nf`). -/
macro "q2w_casts" : tactic => `(tactic| (
  push_cast
  conv_lhs => ring_nf
  set_option linter.unusedSimpArgs false in simp only [w34_one_add_natCast,
  q2w_ofNat_add, q2w_mul_ofNat, ← Nat.cast_add, factQ_natCast, invFactQ_natCast,
  w34_factQ_zero, w34_invFactQ_zero, q2w_factQ_one, q2w_invFactQ_one, q2w_factQ_ofNat,
  q2w_invFactQ_ofNat, q2w_invFactQ_neg_one_add, q2w_invFactQ_neg_two_add,
  q2w_invFactQ_neg_one, q2w_invFactQ_neg_ofNat, mul_one,
  one_mul]))

/-- Peel numeral offsets off factorials, clear denominators and close by `ring`. -/
macro "q2w_fin" : tactic => `(tactic| (
  (set_option linter.unusedSimpArgs false in
    simp only [Nat.add_assoc, q2w_factorial_one_add, q2w_factorial_two_add,
      q2w_factorial_three_add, q2w_factorial_four_add, Nat.factorial_two, Nat.factorial_one])
  push_cast
  field_simp (disch := first | positivity | (ring_nf; positivity))
  ring))

/-- Nonnegativity of products and quotients of factorials and reciprocal factorials. -/
macro "q2w_nonneg" : tactic => `(tactic|
  repeat (first | apply mul_nonneg | apply div_nonneg | exact w34_invFactQ_nonneg _ |
    (positivity) | (unfold factQ; positivity)))

end DLMF.WignerSymbols
