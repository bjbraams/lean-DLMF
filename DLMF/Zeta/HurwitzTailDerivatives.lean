/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.Hurwitz
public import DLMF.Hypergeometric.Basic.PochhammerDerivatives

/-!
# Order derivatives of the Hurwitz Euler–Maclaurin tail

At the orders `-1` and `-2`, every correction term beyond the first has a vanishing
Pochhammer factor. Its order derivative is given by the surviving simple-root factor.
These finite identities provide the explicit terms in DLMF 25.11.44 and 25.11.45.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.Hypergeometric

namespace DLMF.Zeta.EulerMaclaurinTailDerivatives

/-- At a zero of its Pochhammer factor, a correction term differentiates without a logarithm. -/
lemma hasDerivAt_correction_neg_nat {a : ℂ} (ha : a ≠ 0) {n k : ℕ}
    (hn : n < 2 * k + 1) :
    HasDerivAt (fun s : ℂ => eulerMaclaurinCoeff s k * a ^ (-s - (2 * k + 1 : ℕ)))
      ((bernoulli (2 * k + 2) : ℂ) / (2 * k + 2).factorial *
        ((-1 : ℂ) ^ n * n.factorial * (2 * k - n).factorial) *
          a ^ ((n : ℂ) - (2 * k + 1 : ℕ))) (-(n : ℂ)) := by
  have hp := (hasDerivAt_pochhammer_neg_nat_of_lt hn).const_mul
    ((bernoulli (2 * k + 2) : ℂ) / (2 * k + 2).factorial)
  have hpow := ((hasDerivAt_id (-(n : ℂ))).neg.sub_const ((2 * k + 1 : ℕ) : ℂ)).const_cpow
    (c := a) (Or.inl ha)
  have h := hp.mul hpow
  refine h.congr_deriv ?_
  simp only [pochhammer_neg_nat_eq_zero hn, mul_zero, zero_mul, add_zero,
    Pi.neg_apply, id_eq, neg_neg]
  rw [show 2 * k + 1 - n - 1 = 2 * k - n by omega]

/-- The higher correction terms at order `-1`. -/
lemma hasDerivAt_correction_neg_one {a : ℂ} (ha : a ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    HasDerivAt (fun s : ℂ => eulerMaclaurinCoeff s k * a ^ (-s - (2 * k + 1 : ℕ)))
      (-((bernoulli (2 * k + 2) : ℂ) /
        ((2 * k + 2) * (2 * k + 1) * (2 * k))) * a ^ (-(2 * k : ℤ))) (-1) := by
  have h := hasDerivAt_correction_neg_nat ha (n := 1) (k := k) (by omega)
  norm_num only [Nat.cast_one] at h
  have hfac : ((2 * k + 2).factorial : ℂ) =
      (2 * k + 2) * (2 * k + 1) * (2 * k) * ((2 * k - 1).factorial : ℂ) := by
    have h0 : 2 * k + 2 = (2 * k - 1) + 1 + 1 + 1 := by omega
    rw [h0, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  have hf0 : ((2 * k - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  convert h using 1
  rw [hfac]
  have hpow : a ^ ((1 : ℂ) - (2 * k + 1 : ℕ)) = a ^ (-(2 * k : ℤ)) := by
    calc _ = a ^ (((-(2 * k : ℤ)) : ℂ)) := by congr 1; push_cast; ring
         _ = _ := by simpa only [Int.cast_neg] using cpow_intCast a (-(2 * k : ℤ))
  rw [hpow]
  field_simp

/-- The higher correction terms at order `-2`. -/
lemma hasDerivAt_correction_neg_two {a : ℂ} (ha : a ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    HasDerivAt (fun s : ℂ => eulerMaclaurinCoeff s k * a ^ (-s - (2 * k + 1 : ℕ)))
      ((2 * (bernoulli (2 * k + 2) : ℂ) /
        ((2 * k + 2) * (2 * k + 1) * (2 * k) * (2 * k - 1))) *
          a ^ (-(2 * k - 1 : ℤ))) (-2) := by
  have h := hasDerivAt_correction_neg_nat ha (n := 2) (k := k) (by omega)
  norm_num only [Nat.cast_ofNat] at h
  have hfac : ((2 * k + 2).factorial : ℂ) =
      (2 * k + 2) * (2 * k + 1) * (2 * k) * (2 * k - 1) *
        ((2 * k - 2).factorial : ℂ) := by
    have h0 : 2 * k + 2 = (2 * k - 2) + 1 + 1 + 1 + 1 := by omega
    rw [h0, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast [Nat.cast_sub (by omega : 2 ≤ 2 * k)]
    ring
  have hf0 : ((2 * k - 2).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  convert h using 1
  rw [hfac]
  have hpow : a ^ ((2 : ℂ) - (2 * k + 1 : ℕ)) = a ^ (-(2 * k - 1 : ℤ)) := by
    calc _ = a ^ (((-(2 * k - 1 : ℤ)) : ℂ)) := by congr 1; push_cast; ring
         _ = _ := by simpa only [Int.cast_neg] using cpow_intCast a (-(2 * k - 1 : ℤ))
  rw [hpow]
  field_simp

/-- The first-correction tail differentiated at order `-1`. -/
lemma hasDerivAt_tail_one_neg_one {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun s : ℂ => eulerMaclaurinTail 1 s a)
      (1 / 12 - a ^ 2 / 4 + (1 / 12 - a / 2 + a ^ 2 / 2) * log a) (-1) := by
  have hA := ((hasDerivAt_const (-1 : ℂ) 1).sub (hasDerivAt_id (-1 : ℂ))).const_cpow
    (c := a) (Or.inl ha)
  have hB := (hasDerivAt_id (-1 : ℂ)).neg.const_cpow (c := a) (Or.inl ha)
  have hC := ((hasDerivAt_id (-1 : ℂ)).neg.sub_const 1).const_cpow (c := a) (Or.inl ha)
  have h := ((hA.div ((hasDerivAt_id (-1 : ℂ)).sub_const 1) (by norm_num)).add
    (hB.div_const 2)).add (((hasDerivAt_id (-1 : ℂ)).div_const 12).mul hC)
  have hcoeff (s : ℂ) : eulerMaclaurinCoeff s 0 = s / 12 := by
    norm_num [eulerMaclaurinCoeff, pochhammer, bernoulli_two]
    ring
  convert h using 1
  · funext s
    simp only [eulerMaclaurinTail, Finset.sum_range_one, hcoeff, Nat.cast_zero, mul_zero,
      zero_add, Pi.add_apply, Pi.div_apply, Pi.mul_apply, Pi.sub_apply,
      Pi.neg_apply, id_eq]

  · norm_num
    ring

/-- The first-correction tail differentiated at order `-2`. -/
lemma hasDerivAt_tail_one_neg_two {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun s : ℂ => eulerMaclaurinTail 1 s a)
      (a / 12 - a ^ 3 / 9 + (a / 6 - a ^ 2 / 2 + a ^ 3 / 3) * log a) (-2) := by
  have hA := ((hasDerivAt_const (-2 : ℂ) 1).sub (hasDerivAt_id (-2 : ℂ))).const_cpow
    (c := a) (Or.inl ha)
  have hB := (hasDerivAt_id (-2 : ℂ)).neg.const_cpow (c := a) (Or.inl ha)
  have hC := ((hasDerivAt_id (-2 : ℂ)).neg.sub_const 1).const_cpow (c := a) (Or.inl ha)
  have h := ((hA.div ((hasDerivAt_id (-2 : ℂ)).sub_const 1) (by norm_num)).add
    (hB.div_const 2)).add (((hasDerivAt_id (-2 : ℂ)).div_const 12).mul hC)
  have hcoeff (s : ℂ) : eulerMaclaurinCoeff s 0 = s / 12 := by
    norm_num [eulerMaclaurinCoeff, pochhammer, bernoulli_two]
    ring
  convert h using 1
  · funext s
    simp only [eulerMaclaurinTail, Finset.sum_range_one, hcoeff, Nat.cast_zero, mul_zero,
      zero_add, Pi.add_apply, Pi.div_apply, Pi.mul_apply, Pi.sub_apply,
      Pi.neg_apply, id_eq]

  · norm_num
    ring

/-- Split off the first correction term in an Euler–Maclaurin tail. -/
lemma tail_eq_one_add_sum (M : ℕ) (hM : 1 ≤ M) (a s : ℂ) :
    eulerMaclaurinTail M s a = eulerMaclaurinTail 1 s a +
      ∑ k ∈ Ico 1 M, eulerMaclaurinCoeff s k * a ^ (-s - (2 * k + 1 : ℕ)) := by
  simp only [eulerMaclaurinTail, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [Finset.sum_Ico_eq_sub _ hM]
  ring

/-- The finite Euler–Maclaurin tail differentiated at order `-1`. -/
theorem hasDerivAt_tail_neg_one (M : ℕ) (hM : 1 ≤ M) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun s : ℂ => eulerMaclaurinTail M s a)
      (1 / 12 - a ^ 2 / 4 + (1 / 12 - a / 2 + a ^ 2 / 2) * log a -
        ∑ k ∈ Ico 1 M, (bernoulli (2 * k + 2) : ℂ) /
          ((2 * k + 2) * (2 * k + 1) * (2 * k)) * a ^ (-(2 * k : ℤ))) (-1) := by
  have hD := (hasDerivAt_tail_one_neg_one ha).add
    (HasDerivAt.fun_sum (u := Ico 1 M) (fun k hk =>
      hasDerivAt_correction_neg_one ha (mem_Ico.mp hk).1))
  have hfun : (fun s : ℂ => eulerMaclaurinTail M s a) = fun s =>
      eulerMaclaurinTail 1 s a +
        ∑ k ∈ Ico 1 M, eulerMaclaurinCoeff s k * a ^ (-s - (2 * k + 1 : ℕ)) :=
    funext (tail_eq_one_add_sum M hM a)
  rw [hfun]
  refine hD.congr_deriv ?_
  simp only [neg_mul, sum_neg_distrib]
  ring

/-- The finite Euler–Maclaurin tail differentiated at order `-2`. -/
theorem hasDerivAt_tail_neg_two (M : ℕ) (hM : 1 ≤ M) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun s : ℂ => eulerMaclaurinTail M s a)
      (a / 12 - a ^ 3 / 9 + (a / 6 - a ^ 2 / 2 + a ^ 3 / 3) * log a +
        ∑ k ∈ Ico 1 M, 2 * (bernoulli (2 * k + 2) : ℂ) /
          ((2 * k + 2) * (2 * k + 1) * (2 * k) * (2 * k - 1)) *
            a ^ (-(2 * k - 1 : ℤ))) (-2) := by
  have hD := (hasDerivAt_tail_one_neg_two ha).add
    (HasDerivAt.fun_sum (u := Ico 1 M) (fun k hk =>
      hasDerivAt_correction_neg_two ha (mem_Ico.mp hk).1))
  have hfun : (fun s : ℂ => eulerMaclaurinTail M s a) = fun s =>
      eulerMaclaurinTail 1 s a +
        ∑ k ∈ Ico 1 M, eulerMaclaurinCoeff s k * a ^ (-s - (2 * k + 1 : ℕ)) :=
    funext (tail_eq_one_add_sum M hM a)
  rw [hfun]
  exact hD

/-- The explicit order derivative of the finite Euler–Maclaurin tail at `-1`. -/
theorem deriv_neg_one (M : ℕ) (hM : 1 ≤ M) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun s : ℂ => eulerMaclaurinTail M s a) (-1) =
      1 / 12 - a ^ 2 / 4 + (1 / 12 - a / 2 + a ^ 2 / 2) * log a -
        ∑ k ∈ Ico 1 M, (bernoulli (2 * k + 2) : ℂ) /
          ((2 * k + 2) * (2 * k + 1) * (2 * k)) * a ^ (-(2 * k : ℤ)) :=
  (hasDerivAt_tail_neg_one M hM ha).deriv

/-- The explicit order derivative of the finite Euler–Maclaurin tail at `-2`. -/
theorem deriv_neg_two (M : ℕ) (hM : 1 ≤ M) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun s : ℂ => eulerMaclaurinTail M s a) (-2) =
      a / 12 - a ^ 3 / 9 + (a / 6 - a ^ 2 / 2 + a ^ 3 / 3) * log a +
        ∑ k ∈ Ico 1 M, 2 * (bernoulli (2 * k + 2) : ℂ) /
          ((2 * k + 2) * (2 * k + 1) * (2 * k) * (2 * k - 1)) *
            a ^ (-(2 * k - 1 : ℤ)) :=
  (hasDerivAt_tail_neg_two M hM ha).deriv

end DLMF.Zeta.EulerMaclaurinTailDerivatives
