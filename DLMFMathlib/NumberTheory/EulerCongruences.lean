/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.EulerPolynomials
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.RingTheory.Polynomial.Pochhammer
import DLMFMathlib.NumberTheory.PadicNorm
import Mathlib.Tactic

/-!
# Two-adic continuity of the Euler numbers

The normalized coefficients `2ⁿ Eₙ(0) / n!` are two-adic integers: their convolution
recurrence has coefficients `2ᵏ / (k + 1)!`. Expanding the Euler numbers in falling
factorials of their index then shows that congruent indices give congruent Euler numbers.

* `Polynomial.padicNorm_two_pow_mul_euler_eval_zero_div_factorial`: integral coefficients.
* `eulerNumber_eq_sum_descPochhammer`: the falling-factorial expansion in the index.
* `padicNorm_eulerNumber_sub_le_of_modEq`: a two-adic Lipschitz bound.

The proof uses Mathlib's strict factorial valuation bound and polynomial difference
divisibility, together with the Euler polynomial addition API.
-/

public noncomputable section

open Finset Polynomial
open scoped Nat

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

namespace Polynomial

/-- The coefficients `2ⁿ Eₙ(0) / n!` of `2 / (exp (2t) + 1)` are two-adic integers. -/
lemma padicNorm_two_pow_mul_euler_eval_zero_div_factorial (n : ℕ) :
    padicNorm 2 ((2 : ℚ) ^ n * (euler n).eval 0 / (n ! : ℚ)) ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · norm_num [euler_zero]
    have h := euler_eval_add (n + 1) 0 1
    simp only [zero_add, one_pow, mul_one] at h
    rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at h
    have hrec := euler_eval_one_add_eval_zero (n + 1)
    rw [h] at hrec
    simp only [zero_pow (by omega : n + 1 ≠ 0), mul_zero] at hrec
    have he : (2 : ℚ) ^ (n + 1) * (euler (n + 1)).eval 0 / ((n + 1) ! : ℚ) =
        - ∑ k ∈ range (n + 1),
          ((2 : ℚ) ^ k * (euler k).eval 0 / (k ! : ℚ)) *
            (2 ^ (n - k) / ((n + 1 - k) ! : ℚ)) := by
      have hfac (k : ℕ) (hk : k ∈ range (n + 1)) :
          ((2 : ℚ) ^ k * (euler k).eval 0 / (k ! : ℚ)) *
            (2 ^ (n - k) / ((n + 1 - k) ! : ℚ)) =
          (2 : ℚ) ^ n / ((n + 1) ! : ℚ) * ((n + 1).choose k : ℚ) * (euler k).eval 0 := by
        have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
        rw [Nat.cast_choose ℚ (by omega : k ≤ n + 1)]
        have hp : (2 : ℚ) ^ k * 2 ^ (n - k) = 2 ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' hkn]
        have hf₁ : (k ! : ℚ) ≠ 0 := by positivity
        have hf₂ : ((n + 1 - k) ! : ℚ) ≠ 0 := by positivity
        have hf₃ : ((n + 1) ! : ℚ) ≠ 0 := by positivity
        field_simp
        linear_combination hp * (euler k).eval 0
      rw [sum_congr rfl hfac]
      simp only [mul_assoc, ← mul_sum]
      rw [pow_succ]
      linear_combination (2 ^ n / ((n + 1) ! : ℚ)) * hrec
    rw [he, padicNorm.neg]
    apply padicNorm.sum_le' _ (by norm_num)
    intro k hk
    rw [padicNorm.mul]
    have h₁ := ih k (by simpa using mem_range.mp hk)
    have h₂ := padicNorm.pow_div_factorial_le_one (p := 2) (n - k)
    norm_num only [Nat.cast_ofNat] at h₂
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    rw [show n + 1 - k = n - k + 1 by omega]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left h₂ (padicNorm.nonneg _)).trans (by simpa only [mul_one] using h₁)

end Polynomial

/-- Euler numbers are a finite sum of falling factorials of their index; any upper
limit at least the index gives the same sum. -/
lemma eulerNumber_eq_sum_descPochhammer (m K : ℕ) (hmK : m ≤ K) :
    eulerNumber m = ∑ k ∈ range (K + 1),
      (((descPochhammer ℤ k).eval (m : ℤ) : ℤ) : ℚ) *
        ((2 : ℚ) ^ k * (euler k).eval 0 / (k ! : ℚ)) := by
  have hbase : eulerNumber m = ∑ k ∈ range (m + 1),
      (((descPochhammer ℤ k).eval (m : ℤ) : ℤ) : ℚ) *
        ((2 : ℚ) ^ k * (euler k).eval 0 / (k ! : ℚ)) := by
    have h := euler_eval_add m 0 (1 / 2)
    simp only [zero_add] at h
    rw [eulerNumber, h, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have hpow : (2 : ℚ) ^ m = 2 ^ k * 2 ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hkm]
    have hkfac : (k ! : ℚ) ≠ 0 := by positivity
    rw [hpow, div_pow, one_pow]
    field_simp
  rw [hbase]
  apply sum_subset (range_subset_range.mpr (show m + 1 ≤ K + 1 by omega))
  intro k hk hk'
  have hmk : m < k := by simp only [mem_range] at hk hk'; omega
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_zero_iff_lt.mpr hmk]
  simp

/-- Euler numbers at indices congruent modulo `2^ℓ` differ by a rational with
two-adic norm at most `2⁻ℓ`. -/
lemma padicNorm_eulerNumber_sub_le_of_modEq (m n ℓ : ℕ) (hmn : m ≡ n [MOD 2 ^ ℓ]) :
    padicNorm 2 (eulerNumber m - eulerNumber n) ≤ (2 : ℚ) ^ (-(ℓ : ℤ)) := by
  rw [eulerNumber_eq_sum_descPochhammer m (m + n) (by omega),
    eulerNumber_eq_sum_descPochhammer n (m + n) (by omega), ← sum_sub_distrib]
  apply padicNorm.sum_le' _ (by positivity)
  intro k _
  rw [← sub_mul, padicNorm.mul]
  have hcong : (2 : ℤ) ^ ℓ ∣ (descPochhammer ℤ k).eval (m : ℤ) -
      (descPochhammer ℤ k).eval (n : ℤ) := by
    apply dvd_trans _ (Polynomial.sub_dvd_eval_sub (m : ℤ) (n : ℤ) _)
    exact (Int.modEq_iff_dvd).mp (by exact_mod_cast hmn.symm)
  have hd : padicNorm 2 ((((descPochhammer ℤ k).eval (m : ℤ) -
      (descPochhammer ℤ k).eval (n : ℤ) : ℤ) : ℚ)) ≤ (2 : ℚ) ^ (-(ℓ : ℤ)) := by
    apply padicNorm.dvd_iff_norm_le.mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcong
  rw [Int.cast_sub] at hd
  calc
    _ ≤ padicNorm 2 ((((descPochhammer ℤ k).eval (m : ℤ) : ℤ) : ℚ) -
        (((descPochhammer ℤ k).eval (n : ℤ) : ℤ) : ℚ)) * 1 :=
      mul_le_mul_of_nonneg_left
        (Polynomial.padicNorm_two_pow_mul_euler_eval_zero_div_factorial k) (padicNorm.nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hd
