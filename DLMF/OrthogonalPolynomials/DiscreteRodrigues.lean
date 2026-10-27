/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Hahn
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Discrete Rodrigues formulas for Charlier, Meixner, and Krawtchouk polynomials

The Charlier weight `w(x) = a^x/x!` on nonnegative integers is extended by zero to
negative integers. Its iterated backward difference is `w(x) C_n(x;a)`
(Beals–Wong §§6.2–6.3). The zero extension retains the endpoint terms, including `n > x`.
Meixner and Krawtchouk use shifted weights expressed by Pochhammer symbols,
with both finite-support endpoints retained in the Krawtchouk case.
We use Mathlib's `fwdDiff (-1)`, the negative of the backward difference.
-/

@[expose] public noncomputable section

open Complex
open DLMF.Hypergeometric
open scoped Nat

namespace DLMF.OrthogonalPolynomials

/-- The Charlier weight on the integers, with zero extension below its support. -/
def charlierWeightInt (a : ℂ) (x : ℤ) : ℂ :=
  if 0 ≤ x then a ^ x.toNat / x.toNat.factorial else 0

/-- The adjacent Charlier weights, including the boundary at zero. -/
theorem charlierWeightInt_sub_one {a : ℂ} (ha : a ≠ 0) (x : ℤ) (hx : 0 ≤ x) :
    charlierWeightInt a (x - 1) = (x : ℂ) / a * charlierWeightInt a x := by
  lift x to ℕ using hx
  cases x with
  | zero => norm_num [charlierWeightInt]
  | succ x =>
    have he : ((x + 1 : ℕ) : ℤ) - 1 = (x : ℤ) := by omega
    rw [he]
    simp only [charlierWeightInt, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    field_simp [ha, Nat.cast_ne_zero.mpr x.factorial_ne_zero,
      show (x : ℂ) + 1 ≠ 0 by exact_mod_cast x.succ_ne_zero]

/-- Charlier's discrete Rodrigues formula for every integer argument. For `x ≥ 0`,
this states `∇^n(a^x/x!) = (a^x/x!) C_n(x;a)`. -/
theorem charlier_rodrigues {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℤ) :
    (fwdDiff (-1 : ℤ))^[n] (charlierWeightInt a) x =
      (-1 : ℂ) ^ n * charlierWeightInt a x * charlier a n (x : ℂ) := by
  induction n generalizing x with
  | zero => simp [DiscreteOrtho.charlier_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((fwdDiff (-1 : ℤ))^[n] (charlierWeightInt a)) (x - 1) -
      ((fwdDiff (-1 : ℤ))^[n] (charlierWeightInt a)) x = _
    rw [ih, ih, pow_succ]
    by_cases hx : 0 ≤ x
    · rw [charlierWeightInt_sub_one ha x hx]
      have h := charlier_first_difference a n (x : ℂ)
      push_cast
      linear_combination ((-1 : ℂ) ^ n * charlierWeightInt a x) * h
    · have hx' : ¬0 ≤ x - 1 := by omega
      have hw0 : charlierWeightInt a x = 0 := by rw [charlierWeightInt, ite_eq_right hx]
      have hw1 : charlierWeightInt a (x - 1) = 0 := by rw [charlierWeightInt, ite_eq_right hx']
      rw [hw0, hw1]
      ring

/-- The shifted Meixner weight, extended by zero below its support. At `n = 0`
this is `(β)_x c^x/x!`; at general `n` its multiplier is `(β+x)_n`. -/
def meixnerRodriguesWeight (β c : ℂ) (n : ℕ) (x : ℤ) : ℂ :=
  if 0 ≤ x then poch β (x.toNat + n) * c ^ x.toNat / x.toNat.factorial else 0

/-- The shifted Meixner weight is its original weight times `(β+x)_n`, also at
negative integer arguments because of the zero extension. -/
theorem meixnerRodriguesWeight_eq (β c : ℂ) (n : ℕ) (x : ℤ) :
    meixnerRodriguesWeight β c n x = meixnerRodriguesWeight β c 0 x * poch (β + x) n := by
  by_cases hx : 0 ≤ x
  · lift x to ℕ using hx
    simp only [meixnerRodriguesWeight, Int.natCast_nonneg, ite_true, Int.toNat_natCast,
      Nat.add_zero, Int.cast_natCast, poch_add]
    ring
  · simp [meixnerRodriguesWeight, hx]

/-- A shifted weight term in the binomial expansion of the Meixner Rodrigues formula.
The identity includes the zero terms when the shift crosses the support boundary. -/
private lemma meixnerRodriguesWeight_shift {c : ℂ} (hc : c ≠ 0) (β : ℂ)
    (n x k : ℕ) (hk : k ≤ n) :
    meixnerRodriguesWeight β c n ((x : ℤ) - k) =
      (-1 : ℂ) ^ k * meixnerRodriguesWeight β c 0 x * poch (-(x : ℂ)) k *
        poch (β + x) (n - k) * c⁻¹ ^ k := by
  by_cases hkx : k ≤ x
  · have hz : (0 : ℤ) ≤ (x : ℤ) - k := by omega
    have hnat : ((x : ℤ) - k).toNat = x - k := by omega
    simp only [meixnerRodriguesWeight, hz, ite_true, hnat, Int.natCast_nonneg,
      Int.toNat_natCast, Nat.add_zero]
    have hp : poch β (x - k + n) = poch β x * poch (β + x) (n - k) := by
      rw [← poch_add]
      congr 1
      omega
    have hfac : ((x - k).factorial : ℂ) * (x.descFactorial k : ℂ) = (x.factorial : ℂ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hkx
    have hpow : c ^ (x - k) = c ^ x * c⁻¹ ^ k := by
      rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hc), ← pow_add,
        Nat.sub_add_cancel hkx]
    have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    rw [hp, hpow, poch_neg_coe_nat]
    rw [← hfac]
    field_simp [Nat.cast_ne_zero.mpr (x - k).factorial_ne_zero,
      Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hkx).ne']
    linear_combination -(poch β x * poch (β + x) (n - k)) * hsign
  · have hz : ¬(0 : ℤ) ≤ (x : ℤ) - k := by omega
    rw [meixnerRodriguesWeight, ite_eq_right hz, poch_neg_nat_eq_zero (by omega)]
    ring

/-- Meixner's discrete Rodrigues formula. The finite nonvanishing hypothesis permits
negative integral `β`, needed for the finite Krawtchouk specialization. -/
theorem meixner_rodrigues_of_ne_zero {β c : ℂ} (hc : c ≠ 0) (n : ℕ)
    (hβ : ∀ k ≤ n, poch β k ≠ 0) (x : ℤ) :
    (fwdDiff (-1 : ℤ))^[n] (meixnerRodriguesWeight β c n) x =
      (-1 : ℂ) ^ n * meixnerRodriguesWeight β c 0 x * poch β n *
        meixner β c n (x : ℂ) := by
  rw [fwdDiff_iter_eq_sum_shift]
  by_cases hx : 0 ≤ x
  · lift x to ℕ using hx
    rw [mul_assoc ((-1 : ℂ) ^ n * meixnerRodriguesWeight β c 0 x),
      poch_mul_meixner_eq_sum_of_ne_zero n hβ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, nsmul_eq_mul, mul_neg_one, ← sub_eq_add_neg]
    rw [meixnerRodriguesWeight_shift hc β n x k hkn, add_comm (x : ℂ) β]
    have hsign : (-1 : ℂ) ^ (n - k) * (-1 : ℂ) ^ k = (-1 : ℂ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    linear_combination (n.choose k * meixnerRodriguesWeight β c 0 x * poch (-(x : ℂ)) k *
      poch (β + x) (n - k) * c⁻¹ ^ k) * hsign
  · have hw : meixnerRodriguesWeight β c 0 x = 0 := by
      rw [meixnerRodriguesWeight, ite_eq_right hx]
    rw [hw]
    simp only [mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro k _
    have hz : ¬0 ≤ x + k • (-1 : ℤ) := by simp only [nsmul_eq_mul, mul_neg_one]; omega
    rw [meixnerRodriguesWeight, ite_eq_right hz, smul_zero]

/-- Meixner's Rodrigues formula in the ordinary parameter range, with all integer arguments
and zero extension below the support. -/
theorem meixner_rodrigues {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℤ) :
    (fwdDiff (-1 : ℤ))^[n] (meixnerRodriguesWeight β c n) x =
      (-1 : ℂ) ^ n * meixnerRodriguesWeight β c 0 x * poch β n *
        meixner β c n (x : ℂ) :=
  meixner_rodrigues_of_ne_zero hc n (fun k _ => poch_ne_zero_of_re_pos hβ k) x

/-- The shifted finite Krawtchouk weight. At order zero this is the binomial
weight; at order `n` it is multiplied by `(x-N)_n`. The Pochhammer definition
extends it by zero outside its finite support. -/
def krawtchoukRodriguesWeight (p : ℂ) (N n : ℕ) (x : ℤ) : ℂ :=
  (1 - p) ^ N * meixnerRodriguesWeight (-(N : ℂ)) (1 - p⁻¹)⁻¹ n x

/-- The shifted Krawtchouk weight is its binomial weight times `(x-N)_n`. -/
theorem krawtchoukRodriguesWeight_eq (p : ℂ) (N n : ℕ) (x : ℤ) :
    krawtchoukRodriguesWeight p N n x =
      krawtchoukRodriguesWeight p N 0 x * poch ((x : ℂ) - N) n := by
  rw [krawtchoukRodriguesWeight, meixnerRodriguesWeight_eq]
  rw [show -(N : ℂ) + x = (x : ℂ) - N by ring]
  rw [krawtchoukRodriguesWeight]
  ring

/-- The order-zero Krawtchouk Rodrigues weight is precisely the binomial weight
on its natural support. -/
theorem krawtchoukRodriguesWeight_zero {p : ℂ} (hp : p ≠ 0) (hp1 : p ≠ 1)
    (N x : ℕ) (hx : x ≤ N) :
    krawtchoukRodriguesWeight p N 0 x =
      (N.choose x : ℂ) * p ^ x * (1 - p) ^ (N - x) := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  have hc : (1 - p⁻¹)⁻¹ = -p / (1 - p) := by field_simp; ring
  simp only [krawtchoukRodriguesWeight, meixnerRodriguesWeight, Int.natCast_nonneg,
    ite_true, Int.toNat_natCast, Nat.add_zero, poch_neg_coe_nat,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [hc, div_pow, neg_pow]
  have hf : (x.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr x.factorial_ne_zero
  have hsign : (-1 : ℂ) ^ x * (-1 : ℂ) ^ x = 1 := by rw [← mul_pow]; norm_num
  have hpow : (1 - p) ^ N = (1 - p) ^ x * (1 - p) ^ (N - x) := by
    rw [← pow_add, Nat.add_sub_cancel' hx]
  rw [hpow]
  field_simp
  linear_combination ((N.choose x : ℂ) * p ^ x) * hsign

/-- A shifted Krawtchouk weight vanishes beyond its finite support. -/
theorem krawtchoukRodriguesWeight_eq_zero {p : ℂ} {N n : ℕ} {x : ℤ}
    (hx : N < x.toNat + n) : krawtchoukRodriguesWeight p N n x = 0 := by
  unfold krawtchoukRodriguesWeight meixnerRodriguesWeight
  split_ifs <;> simp [poch_neg_nat_eq_zero hx]

/-- Krawtchouk's discrete Rodrigues formula on every integer argument, including
both ends of the finite support. The parameter exclusions keep the binomial
weight and the existing hypergeometric normalization nondegenerate. -/
theorem krawtchouk_rodrigues {p : ℂ} (_hp : p ≠ 0) (hp1 : p ≠ 1)
    {N n : ℕ} (hn : n ≤ N) (x : ℤ) :
    (fwdDiff (-1 : ℤ))^[n] (krawtchoukRodriguesWeight p N n) x =
      (-1 : ℂ) ^ n * krawtchoukRodriguesWeight p N 0 x * poch (-(N : ℂ)) n *
        krawtchouk p N n (x : ℂ) := by
  have hc : (1 - p⁻¹)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    intro h
    have hpinv : p⁻¹ = 1 := by linear_combination -h
    exact hp1 (inv_eq_one.mp hpinv)
  have hb : ∀ k ≤ n, poch (-(N : ℂ)) k ≠ 0 := by
    intro k hk
    rw [poch_neg_coe_nat]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (hk.trans hn)).ne')
  change (fwdDiff (-1 : ℤ))^[n]
    ((1 - p) ^ N • meixnerRodriguesWeight (-(N : ℂ)) (1 - p⁻¹)⁻¹ n) x = _
  rw [fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul,
    meixner_rodrigues_of_ne_zero hc n hb]
  simp only [meixner, krawtchouk, inv_inv, sub_sub_cancel, krawtchoukRodriguesWeight]
  ring

end DLMF.OrthogonalPolynomials
