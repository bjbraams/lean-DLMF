/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Series
public import DLMF.QSeries.Basic.CalculusProperties
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Basic properties of integer-index shifted factorials and the triangular exponent

This file proves the unfolding lemmas of the integer-index `q`-shifted factorial and the basic
identities for the triangular exponent `tri n = n (n - 1) / 2` used throughout the `q`-series
area.

## Main results

* `qPochhammerInt_natCast`, `qPochhammerInt_negSucc`: the integer-index shifted factorial
  (AAR (10.5.2)).
* `TripleProduct.tri_mul_two`, `TripleProduct.cpow_tri`, `TripleProduct.tri_sub_cast`:
  the triangular exponent.
* `TripleProduct.qPochhammer_shift_down`: reversal of a finite `q`-shifted factorial.

## Implementation notes

The Jacobi triple product and Ramanujan's `₁ψ₁` summation are in `DLMF.QSeries.Identities`.
-/

@[expose] public section

open Complex

noncomputable section

namespace DLMF.QSeries

/-- At a natural index `qPochhammerInt` is the ordinary `q`-shifted factorial. -/
@[simp] theorem qPochhammerInt_natCast (a q : ℂ) (n : ℕ) :
    qPochhammerInt a q n = qPochhammer a q n := rfl

/-- At the index `-(n+1)`, `(a;q)_{-(n+1)} = 1/(a q^{-(n+1)};q)_{n+1}` (AAR (10.5.2)). -/
@[simp] theorem qPochhammerInt_negSucc (a q : ℂ) (n : ℕ) :
    qPochhammerInt a q (Int.negSucc n) =
      (qPochhammer (a * q ^ (-(n + 1 : ℤ))) q (n + 1))⁻¹ := rfl

namespace TripleProduct

/-- `2 tri n = n (n - 1)`: the integer division in `tri` is exact. -/
theorem tri_mul_two (n : ℤ) : tri n * 2 = n * (n - 1) :=
  Int.ediv_mul_cancel (even_iff_two_dvd.mp (Int.even_mul_pred_self n))

/-- `q^{n(n-1)/2}` as a complex power equals the integer power `q^{tri n}`. -/
theorem cpow_tri (q : ℂ) (n : ℤ) :
    q ^ ((n : ℂ) * ((n : ℂ) - 1) / 2) = q ^ tri n := by
  have h : ((tri n : ℤ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast tri_mul_two n
  rw [← h, cpow_intCast]

/-- `(z q^{-m};q)_m q^{C(m+1,2)} = (-z)^m (q/z;q)_m`: reversing a finite `q`-shifted
factorial. -/
theorem qPochhammer_shift_down {q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    qPochhammer (z / q ^ m) q m * q ^ (m + 1).choose 2 = (-z) ^ m * qPochhammer (q / z) q m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : (m + 2).choose 2 = (m + 1).choose 2 + (m + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have hx : z / q ^ (m + 1) * q = z / q ^ m := by field_simp; ring
    rw [qPochhammer_succ', hx, hc, qPochhammer_succ, pow_add]
    have hqm : q ^ (m + 1) ≠ 0 := pow_ne_zero _ hq
    linear_combination (norm := (field_simp; ring)) ((1 - z / q ^ (m + 1)) * q ^ (m + 1)) * ih

/-- `C(k,2) + C(m+1,2) - m k = tri (k - m)`. -/
theorem tri_sub_cast (k m : ℕ) :
    ((k.choose 2 : ℕ) : ℤ) + ((m + 1).choose 2 : ℕ) - (m : ℤ) * k = tri ((k : ℤ) - m) := by
  apply Int.cast_injective (α := ℚ)
  have h := tri_mul_two ((k : ℤ) - m)
  have h' : ((tri ((k : ℤ) - m) : ℤ) : ℚ) = ((k : ℚ) - m) * ((k : ℚ) - m - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast h
  push_cast
  rw [h', Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

end TripleProduct

end DLMF.QSeries
