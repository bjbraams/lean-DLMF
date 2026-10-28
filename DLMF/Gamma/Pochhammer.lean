/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic
public import DLMF.Hypergeometric.Series

/-!
# Pochhammer identities (DLMF §5.2)

The symbol `(a)_n` is the project's `poch`. `(a)_0 = 1` and the rising product
are `poch_zero` and `poch_succ` in `Hypergeometric.Basic`. The Gamma quotient
`(a)_n = Γ(a+n)/Γ(a)` is Mathlib's `Gamma_add_nat_div_Gamma_eq`.
-/

@[expose] public section

open Complex
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Gamma

/-- `(a)_{n+1} = a (a + 1)_n`. -/
theorem poch_succ_left (a : ℂ) (n : ℕ) : poch a (n + 1) = a * poch (a + 1) n :=
  DLMF.Hypergeometric.poch_succ_left a n

/-- DLMF 5.2.6: `(-a)_n = (-1)^n (a - n + 1)_n`. -/
@[dlmf 5.2.E6]
theorem poch_neg_eq (a : ℂ) (n : ℕ) :
    poch (-a) n = (-1 : ℂ) ^ n * poch (a - n + 1) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have harg : a - (n + 1 : ℕ) + 1 = a - n := by
      rw [Nat.cast_succ]
      ring
    rw [poch_succ, ih, pow_succ, harg, poch_succ_left]
    ring

/-- DLMF 5.2.7: `(-m)_n = (-1)^n m!/(m - n)!` for `n ≤ m`, and `(-m)_n = 0` for `n > m`. -/
@[dlmf 5.2.E7]
theorem poch_neg_nat_eq (m n : ℕ) :
    poch (-(m : ℂ)) n =
      if n ≤ m then (-1 : ℂ) ^ n * m.factorial / (m - n).factorial else 0 := by
  split_ifs with h
  · have hdiv : (m - n).factorial ∣ m.factorial :=
      Nat.factorial_dvd_factorial (Nat.sub_le _ _)
    have hne : ((m - n).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [poch_neg_coe_nat, Nat.descFactorial_eq_div h, Nat.cast_div hdiv hne, mul_div_assoc]
  · exact poch_neg_nat_eq_zero (Nat.lt_of_not_ge h)

end DLMF.Gamma
