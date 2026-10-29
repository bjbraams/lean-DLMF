/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Binomial

/-!
# Falling-factorial expressions for generalized binomial coefficients

These adapters connect the polynomial evaluation API for Pochhammer symbols to
`Ring.choose`, including the coefficient relation used in Euler–Maclaurin expansions.
-/

@[expose] public noncomputable section

open Polynomial

namespace Ring

/-- Generalized binomial coefficients are falling-factorial polynomial evaluations
divided by the factorial. -/
theorem choose_eq_descPochhammer_div {K : Type*} [Field K] [CharZero K] (z : K) (n : ℕ) :
    choose z n = (descPochhammer K n).eval z / n.factorial := by
  rw [choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval, descPochhammer_eval_eq_ascPochhammer,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The odd-order shifted binomial coefficient in Euler–Maclaurin has the
opposite sign to the corresponding falling coefficient. -/
theorem choose_neg_add_even_sub_two {K : Type*} [Field K] [CharZero K]
    (z : K) {k : ℕ} (hk : 1 ≤ k) :
    choose (-z + 2 * k - 2) (2 * k - 1) = -choose z (2 * k - 1) := by
  have h := choose_neg (z - (2 * k - 1 : ℕ) + 1) (2 * k - 1)
  have hp : Odd ((2 * k - 1 : ℕ) : ℤ) := by
    exact ⟨(k : ℤ) - 1, by rw [Nat.cast_sub (by omega)]; push_cast; ring⟩
  rw [Int.negOnePow_odd _ hp, Units.neg_smul, one_smul] at h
  rw [show z - (2 * k - 1 : ℕ) + 1 + (2 * k - 1 : ℕ) - 1 = z by ring] at h
  have he : -(z - (2 * k - 1 : ℕ) + 1) = -z + 2 * k - 2 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  simpa only [he] using h

/-- Consecutive generalized binomial coefficients satisfy the falling-factorial
recursion, with no restriction on the upper argument. -/
theorem natCast_mul_choose_succ {K : Type*} [Field K] [CharZero K] (z : K) (n : ℕ) :
    (n + 1 : K) * choose z (n + 1) = z * choose (z - 1) n := by
  have h := choose_smul_choose z (n := n + 1) (k := 1) (by omega)
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, nsmul_eq_mul,
    choose_one_right, Nat.add_sub_cancel] using h

end Ring
