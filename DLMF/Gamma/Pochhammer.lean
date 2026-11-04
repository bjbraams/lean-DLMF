/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.SpecialValues
public import DLMF.Hypergeometric.Basic.RealPochhammer

/-!
# Pochhammer identities (DLMF §5.2)

The symbol `(a)_n` is the project's `pochhammer`. `(a)_0 = 1` and the rising product are
`pochhammer_zero` and `pochhammer_succ` in `DLMF.Hypergeometric.Basic.Pochhammer`. The Gamma
quotient `(a)_n = Γ(a+n)/Γ(a)` is Mathlib's `Gamma_add_nat_div_Gamma_eq`.

## Main results

* `pochhammer_neg_eq`: `(-a)_n = (-1)^n (a - n + 1)_n`, DLMF 5.2.6.
* `pochhammer_neg_nat_eq`: `(-m)_n = (-1)^n m!/(m - n)!` for `n ≤ m` and `0` otherwise, DLMF 5.2.7.
-/

@[expose] public section

open Complex
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Gamma

/-- DLMF 5.2.6: `(-a)_n = (-1)^n (a - n + 1)_n`. -/
@[dlmf 5.2.E6]
theorem pochhammer_neg_eq (a : ℂ) (n : ℕ) :
    pochhammer (-a) n = (-1 : ℂ) ^ n * pochhammer (a - n + 1) n := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    have harg : a - (n + 1 : ℕ) + 1 = a - n := by
      rw [Nat.cast_succ]
      ring
    rw [pochhammer_succ, ih, pow_succ, harg, pochhammer_succ_left]
    ring

/-- DLMF 5.2.7: `(-m)_n = (-1)^n m!/(m - n)!` for `n ≤ m`, and `(-m)_n = 0` for `n > m`. -/
@[dlmf 5.2.E7]
theorem pochhammer_neg_nat_eq (m n : ℕ) :
    pochhammer (-(m : ℂ)) n =
      if n ≤ m then (-1 : ℂ) ^ n * m.factorial / (m - n).factorial else 0 := by
  split_ifs with h
  · have hdiv : (m - n).factorial ∣ m.factorial :=
      Nat.factorial_dvd_factorial (Nat.sub_le _ _)
    have hne : ((m - n).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [pochhammer_neg_coe_nat, Nat.descFactorial_eq_div h, Nat.cast_div hdiv hne, mul_div_assoc]
  · exact pochhammer_neg_nat_eq_zero (Nat.lt_of_not_ge h)

end DLMF.Gamma
