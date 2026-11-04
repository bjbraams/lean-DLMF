/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic

/-!
# Factorial and cast helpers for the Wigner symbols

Rewriting lemmas for `ratFactorial` and `ratInvFactorial` at natural-number arguments with numeral
offsets, and the tactics `wigner_cast_ring` and `wigner_fin_simp` that turn a closed-form evaluation
of a `3j` or `6j` symbol (after substitution of natural-number parameters) into a
rational-function identity and close it. They are used by the single-term and two-term
evaluations in `DLMF.WignerSymbols.ThreeJ` and `DLMF.WignerSymbols.SixJ`.

## Main results

* `natCast_factorial_one_add`, `natCast_factorial_two_add`: factorial recursions with numeral
  offsets.
* `ratInvFactorial_neg_one_add`, `ratInvFactorial_neg_two_add`: `1/(n-1)! = n/n!` and
  `1/(n-2)! = n(n-1)/n!`, including the cases where both sides vanish.
* `ratInvFactorial_neg_one`, `ratInvFactorial_neg_ofNat`: reciprocal factorials at negative
  integers.
* `ratInvFactorial_sub_one_of_eq_intCast`: `1/(t-1)! = t/t!` at every integer `t`.
-/

@[expose] public noncomputable section

namespace DLMF.WignerSymbols

/-- `(1 + n)! = (1 + n) n!`. -/
theorem natCast_factorial_one_add (n : ℕ) :
    ((1 + n).factorial : ℝ) = ((1 + n : ℕ) : ℝ) * (n.factorial : ℝ) := by
  rw [Nat.add_comm, Nat.factorial_succ]; push_cast; ring

/-- Fold a numeral plus a natural-number cast into one cast. -/
theorem ofNat_add_natCast (k m : ℕ) [k.AtLeastTwo] :
    (no_index (OfNat.ofNat k) : ℚ) + (m : ℚ) = ((OfNat.ofNat k + m : ℕ) : ℚ) := by push_cast; ring
/-- Fold a natural-number cast times a numeral into one cast. -/
lemma natCast_mul_ofNat (k m : ℕ) [k.AtLeastTwo] :
    (m : ℚ) * (no_index (OfNat.ofNat k) : ℚ) = ((m * OfNat.ofNat k : ℕ) : ℚ) := by push_cast; ring
/-- `1! = 1`. -/
@[simp] theorem ratFactorial_one : ratFactorial 1 = 1 := by simp [ratFactorial]
/-- `1/1! = 1`. -/
@[simp] theorem ratInvFactorial_one : ratInvFactorial 1 = 1 := by
    simp [ratInvFactorial, ratFactorial]
/-- `ratFactorial` at a numeral. -/
theorem ratFactorial_ofNat (k : ℕ) [k.AtLeastTwo] :
    ratFactorial (no_index (OfNat.ofNat k) : ℚ) = ((OfNat.ofNat k : ℕ).factorial : ℝ) := by
  rw [← ratFactorial_natCast]; norm_num
/-- `ratInvFactorial` at a numeral. -/
theorem ratInvFactorial_ofNat (k : ℕ) [k.AtLeastTwo] :
    ratInvFactorial (no_index (OfNat.ofNat k) : ℚ) = ((OfNat.ofNat k : ℕ).factorial : ℝ)⁻¹ := by
  rw [← ratInvFactorial_natCast]; norm_num

/-- `(2 + n)! = (2 + n) (1 + n)!`. -/
theorem natCast_factorial_two_add (n : ℕ) :
    ((2 + n).factorial : ℝ) = ((2 + n : ℕ) : ℝ) * ((1 + n).factorial : ℝ) := by
  rw [show 2 + n = (1 + n) + 1 by omega, Nat.factorial_succ]; push_cast; ring
/-- `(3 + n)! = (3 + n) (2 + n)!`. -/
theorem natCast_factorial_three_add (n : ℕ) :
    ((3 + n).factorial : ℝ) = ((3 + n : ℕ) : ℝ) * ((2 + n).factorial : ℝ) := by
  rw [show 3 + n = (2 + n) + 1 by omega, Nat.factorial_succ]; push_cast; ring
/-- `(4 + n)! = (4 + n) (3 + n)!`. -/
theorem natCast_factorial_four_add (n : ℕ) :
    ((4 + n).factorial : ℝ) = ((4 + n : ℕ) : ℝ) * ((3 + n).factorial : ℝ) := by
  rw [show 4 + n = (3 + n) + 1 by omega, Nat.factorial_succ]; push_cast; ring

/-- `1/(n-1)! = n/n!`, including `n = 0` (both sides vanish). -/
theorem ratInvFactorial_neg_one_add (n : ℕ) :
    ratInvFactorial (-1 + (n : ℚ)) = (n : ℝ) * ((n.factorial : ℝ))⁻¹ := by
  rcases n with _ | m
  · rw [ratInvFactorial_of_neg (by norm_num)]; simp
  · rw [ratInvFactorial_of_eq (n := m) (by push_cast; ring), Nat.factorial_succ]
    push_cast
    field_simp

/-- `1/(n-2)! = n(n-1)/n!`, including `n = 0, 1` (both sides vanish). -/
lemma ratInvFactorial_neg_two_add (n : ℕ) :
    ratInvFactorial (-2 + (n : ℚ)) = (n : ℝ) * ((n : ℝ) - 1) * ((n.factorial : ℝ))⁻¹ := by
  rcases n with _ | _ | m
  · rw [ratInvFactorial_of_neg (by norm_num)]; simp
  · rw [ratInvFactorial_of_neg (by norm_num)]; simp
  · rw [ratInvFactorial_of_eq (n := m) (by push_cast; ring), Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `1/(-1)! = 0`. -/
theorem ratInvFactorial_neg_one : ratInvFactorial (-1) = 0 := ratInvFactorial_of_neg (by norm_num)

/-- `1/(-k)! = 0` for a numeral `k ≥ 2`. -/
lemma ratInvFactorial_neg_ofNat (k : ℕ) [k.AtLeastTwo] :
    ratInvFactorial (-(no_index (OfNat.ofNat k) : ℚ)) = 0 :=
  ratInvFactorial_of_neg (by
    have : (2 : ℚ) ≤ (OfNat.ofNat k : ℚ) := by
      rw [← Nat.cast_ofNat (R := ℚ) (n := k)]; exact_mod_cast Nat.AtLeastTwo.prop
    linarith)

/-- `1/(t-1)! = t/t!` for an integer `t` (both sides vanish for `t ≤ 0`). -/
theorem ratInvFactorial_sub_one_of_eq_intCast {t : ℚ} {n : ℤ} (h : t = n) :
    ratInvFactorial (t - 1) = (t : ℝ) * ratInvFactorial t := by
  subst h
  rcases lt_or_ge n 1 with hn | hn
  · have hn1 : (n : ℚ) < 1 := by exact_mod_cast hn
    rw [ratInvFactorial_of_neg (by linarith)]
    rcases lt_or_ge n 0 with hn' | hn'
    · rw [ratInvFactorial_of_neg (by exact_mod_cast hn'), mul_zero]
    · have : n = 0 := by omega
      subst this; simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨(n - 1).toNat, by omega⟩
    rw [ratInvFactorial_of_eq (n := k) (by push_cast; ring),
      ratInvFactorial_of_eq (n := k + 1) (by push_cast; ring), Nat.factorial_succ]
    push_cast
    field_simp

/-- `√x = R / √Y` when `x = R² / Y` with `R, Y ≥ 0`. -/
theorem sqrt_eq_div_sqrt_of_eq {x R Y : ℝ} (hR : 0 ≤ R) (hY : 0 ≤ Y) (hx : x = R ^ 2 / Y) :
    Real.sqrt x = R / Real.sqrt Y := by
  rw [hx, Real.sqrt_div' _ hY, Real.sqrt_sq hR]

/-- Rewrite the factorials of natural-number arguments (left side normalized by `ring_nf`). -/
macro "wigner_cast_ring" : tactic => `(tactic| (
  push_cast
  conv_lhs => ring_nf
  set_option linter.unusedSimpArgs false in simp only [one_add_natCast_eq,
  ofNat_add_natCast, natCast_mul_ofNat, ← Nat.cast_add, ratFactorial_natCast,
      ratInvFactorial_natCast,
  ratFactorial_zero, ratInvFactorial_zero, ratFactorial_one, ratInvFactorial_one,
      ratFactorial_ofNat,
  ratInvFactorial_ofNat, ratInvFactorial_neg_one_add, ratInvFactorial_neg_two_add,
  ratInvFactorial_neg_one, ratInvFactorial_neg_ofNat, mul_one,
  one_mul]))

/-- Peel numeral offsets off factorials, clear denominators and close by `ring`. -/
macro "wigner_fin_simp" : tactic => `(tactic| (
  (set_option linter.unusedSimpArgs false in
    simp only [Nat.add_assoc, natCast_factorial_one_add, natCast_factorial_two_add,
      natCast_factorial_three_add, natCast_factorial_four_add, Nat.factorial_two,
          Nat.factorial_one])
  push_cast
  field_simp (disch := first | positivity | (ring_nf; positivity))
  ring))

/-- Nonnegativity of products and quotients of factorials and reciprocal factorials. -/
macro "wigner_cast_nonneg" : tactic => `(tactic|
  repeat (first | apply mul_nonneg | apply div_nonneg | exact ratInvFactorial_nonneg _ |
    (positivity) | (unfold ratFactorial; positivity)))

end DLMF.WignerSymbols
