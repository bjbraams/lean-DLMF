/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Saalschutz

/-!
# Finite hypergeometric convolutions

Chu–Vandermonde and finite binomial moments give a terminating `3F2`
transformation without restrictions on its upper parameters. The analytic
Cauchy-product helper uses the Mathlib contributors’ absolutely summable
series API. These identities identify the Hahn generating-function coefficients.
-/

@[expose] public section

open Complex
open scoped Nat
noncomputable section
namespace DLMF.Hypergeometric

/-- Cauchy product of scalar series, written as a coefficient convolution. -/
theorem hasSum_coefficient_convolution {c d : ℕ → ℂ} {z u v : ℂ}
    (hc : HasSum (fun n => c n * z ^ n) u)
    (hd : HasSum (fun n => d n * z ^ n) v) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), c k * d (n - k)) * z ^ n) (u * v) := by
  exact Complex.hasSum_powerSeries_convolution hc hd

/-- Chu–Vandermonde with a regular denominator, in binomial form. -/
theorem poch_ratio_vandermonde (Q R : ℂ) (hR : ∀ k : ℕ, poch R k ≠ 0) (n : ℕ) :
    poch (R - Q) n / poch R n =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k * poch Q k / poch R k := by
  apply (div_eq_iff (hR n)).2
  rw [Finset.sum_mul, ← chu_vandermonde_sum n Q R]
  symm
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  have hp : poch R n = poch R k * poch (R + k) (n - k) := by
    rw [← poch_add, Nat.add_sub_cancel' hk']
  rw [hp]
  field_simp [hR k]

/-- A binomial moment of rising factorials. -/
theorem poch_binomial_moment (P X : ℂ) {n k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * j.choose k * poch P j * poch X (n - j) =
      n.choose k * poch P k * poch (P + X + k) (n - k) := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k ≤ n + 1)]
  have h0 : ∑ j ∈ Finset.range k,
      (n.choose j : ℂ) * j.choose k * poch P j * poch X (n - j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj)]
    ring
  rw [h0, zero_add, Finset.sum_Ico_eq_sum_range, show n + 1 - k = n - k + 1 by omega,
    show P + X + k = P + k + X by ring, poch_add_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hc := Nat.choose_mul (n := n) (k := k + i) (s := k) (by omega)
  rw [show k + i - k = i by omega] at hc
  have hc' : (n.choose (k + i) : ℂ) * (k + i).choose k = n.choose k * (n - k).choose i := by
    exact_mod_cast hc
  rw [poch_add, show n - (k + i) = n - k - i by omega]
  linear_combination (poch P k * poch (P + k) i * poch X (n - k - i)) * hc'

/-- A terminating `3F2` transformation as a finite binomial convolution. -/
theorem terminating_3F2_convolution (P Q R D : ℂ) (hR : ∀ k : ℕ, poch R k ≠ 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k * poch P k * poch Q k /
      poch R k * poch (D + k) (n - k)) =
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * poch P j * poch (R - Q) j /
      poch R j * poch (D - P) (n - j) := by
  have he (j : ℕ) : (n.choose j : ℂ) * poch P j * poch (R - Q) j /
      poch R j * poch (D - P) (n - j) =
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ k * poch Q k / poch R k) *
        ((n.choose j : ℂ) * j.choose k * poch P j * poch (D - P) (n - j)) := by
    rw [show (n.choose j : ℂ) * poch P j * poch (R - Q) j / poch R j * poch (D - P) (n - j) =
      (n.choose j * poch P j * poch (D - P) (n - j)) * (poch (R - Q) j / poch R j) by ring,
      poch_ratio_vandermonde Q R hR, Finset.mul_sum]
    by_cases hj : j ≤ n
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ n + 1)]
      have hz : ∑ k ∈ Finset.Ico (j + 1) (n + 1),
          ((-1 : ℂ) ^ k * poch Q k / poch R k) *
          ((n.choose j : ℂ) * j.choose k * poch P j * poch (D - P) (n - j)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega : j < k)]
        ring
      rw [hz, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp [Nat.choose_eq_zero_of_lt (by omega : n < j)]
  rw [Finset.sum_congr rfl (fun j _ => he j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  rw [← Finset.mul_sum, poch_binomial_moment P (D - P) hk',
    show P + (D - P) + k = D + k by ring]
  ring

/-- Euler's transformation as a finite binomial convolution. -/
theorem saalschutz_binomial_convolution (a b c : ℂ) (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * poch a k * poch b k / poch c k *
      poch (c - a - b) (n-k) = poch (c-a) n * poch (c-b) n / poch c n := by
  have h := regularized_saalschutz_convolution a b c n
  have hG (k : ℕ) : Gamma (c+k) = poch c k * Gamma c := by
    rw [poch, ← Gamma_add_nat_div_Gamma_eq c hc]
    field_simp [Gamma_ne_zero hc]
  have hg := Gamma_ne_zero hc
  have hp := poch_ne_zero_of_not_neg_nat hc
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [hG n, eq_div_iff (mul_ne_zero hn (mul_ne_zero (hp n) hg)), Finset.sum_mul] at h
  apply (eq_div_iff (hp n)).2
  rw [Finset.sum_mul, ← h]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  have hf : (n.choose k : ℂ) * k ! * (n-k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk : ((n-k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n-k).factorial_ne_zero
  rw [hG k]
  field_simp [hp k, hg, hkf, hnk]
  linear_combination (poch a k * poch b k * poch (c-a-b) (n-k) * poch c n) * hf

/-- Pfaff–Saalschütz in the inner sum of the Wilson coefficient transformation. -/
theorem wilson_inner_sum {P Q E F : ℂ}
    (hE : 0 < E.re) (hF : 0 < F.re) (n j : ℕ) (hj : j ≤ n)
    (hbal : Q = E + F - P + n - 1) :
    ∑ l ∈ Finset.range (n-j+1), poch (-((n-j : ℕ) : ℂ)) l * poch (P+j) l * poch Q l /
      (poch (E+j) l * poch (F+j) l * l !) =
    poch (E-P) (n-j) * poch (P-F-n+1+j) (n-j) /
      (poch (E+j) (n-j) * poch (1-F-n) (n-j)) := by
  have he : ∀ k : ℕ, E+j ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) j])
  have hf : ∀ k : ℕ, F+j ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) j])
  have hh : 1 + (P+j) + Q - (E+j) - (n-j : ℕ) = F+j := by
    rw [hbal]; push_cast [Nat.cast_sub hj]; ring
  have hs := pfaff_saalschutz (n-j) (a := P+j) (b := Q) (c := E+j) he
    (by rw [hh]; exact poch_ne_zero_of_not_neg_nat hf _)
  rw [hh, show E+j-(P+j) = E-P by ring,
    show E+j-Q = P-F-n+1+j by rw [hbal]; ring,
    show E-P-Q = 1-F-n by rw [hbal]; ring] at hs
  exact hs

/-- Reflection of a finite rising factorial. -/
theorem poch_one_sub_nat (Z : ℂ) (m : ℕ) :
    poch (1-Z-m) m = (-1 : ℂ) ^ m * poch Z m := by
  rw [show 1-Z-m = -(Z+m-1) by ring, DLMF.Gamma.poch_neg_eq,
    show Z+m-1-m+1 = Z by ring]

/-- The balanced inner Pfaff–Saalschütz sum with no singular numerator divisions. -/
theorem balanced_inner_sum {P Q E F : ℂ}
    (hE : 0 < E.re) (hF : 0 < F.re) (n j : ℕ) (hj : j ≤ n)
    (hbal : Q = E + F - P + n - 1) :
    ∑ l ∈ Finset.range (n-j+1), poch (-((n-j : ℕ) : ℂ)) l * poch (P+j) l * poch Q l /
      (poch (E+j) l * poch (F+j) l * l !) =
    poch (E-P) (n-j) * poch (F-P) (n-j) /
      (poch (E+j) (n-j) * poch (F+j) (n-j)) := by
  rw [wilson_inner_sum hE hF n j hj hbal,
    show P-F-n+1+j = 1-(F-P)-(n-j : ℕ) by push_cast [Nat.cast_sub hj]; ring,
    show 1-F-n = 1-(F+j)-(n-j : ℕ) by push_cast [Nat.cast_sub hj]; ring,
    poch_one_sub_nat, poch_one_sub_nat]
  have hs : (-1 : ℂ) ^ (n-j) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Reindexing the double convolution arising from Euler's transformation. -/
theorem balanced_4F3_double_sum (P Q N E F R : ℂ)
    (hE : 0 < E.re) (hF : 0 < F.re) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), poch (-(n : ℂ)) k * poch P k /
      (poch E k * poch F k * k !) *
      (∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) * poch (R-Q) j * poch (R-N) j /
        poch R j * poch (Q+N-R) (k-j))) =
    ∑ j ∈ Finset.range (n+1),
      (poch (-(n : ℂ)) j * poch P j * poch (R-Q) j * poch (R-N) j /
        (poch R j * poch E j * poch F j * j !)) *
      (∑ l ∈ Finset.range (n-j+1), poch (-((n-j : ℕ) : ℂ)) l * poch (P+j) l *
        poch (Q+N-R) l / (poch (E+j) l * poch (F+j) l * l !)) := by
  simp_rw [Finset.mul_sum]
  have htri := (Finset.sum_range_diag_flip (n+1) (fun j l =>
    poch (-(n : ℂ)) (j+l) * poch P (j+l) / (poch E (j+l) * poch F (j+l) * (j+l)!) *
      ((j+l).choose j * poch (R-Q) j * poch (R-N) j / poch R j * poch (Q+N-R) l))).symm
  have he : (∑ k ∈ Finset.range (n+1), ∑ j ∈ Finset.range (k+1),
      poch (-(n : ℂ)) k * poch P k / (poch E k * poch F k * k !) *
        ((k.choose j : ℂ) * poch (R-Q) j * poch (R-N) j / poch R j * poch (Q+N-R) (k-j))) =
      ∑ j ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1-j),
        poch (-(n : ℂ)) (j+l) * poch P (j+l) / (poch E (j+l) * poch F (j+l) * (j+l)!) *
          ((j+l).choose j * poch (R-Q) j * poch (R-N) j / poch R j * poch (Q+N-R) l) := by
    rw [htri]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.add_sub_cancel' (show j ≤ k by simpa using hj)]
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by simpa using hj
  rw [show n+1-j = n-j+1 by omega]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l ≤ n-j := by simpa using hl
  have hch : ((j+l).choose j : ℂ) * j ! * l ! = (j+l)! := by
    exact_mod_cast (by simpa using Nat.choose_mul_factorial_mul_factorial (show j ≤ j+l by omega))
  rw [poch_add, poch_add, show -(n : ℂ)+j = -((n-j : ℕ) : ℂ) by push_cast [Nat.cast_sub hj']; ring,
    poch_add E, poch_add F]
  have hp (Z : ℂ) (hZ : 0 < Z.re) (k : ℕ) : poch Z k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hZ) k
  have he : 0 < (E+j).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hf : 0 < (F+j).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hjf : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hlf : (l ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
  have ht : ((j+l)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (j+l).factorial_ne_zero
  field_simp [hp E hE j, hp F hF j, hp (E+j) he l, hp (F+j) hf l, hjf, hlf, ht]
  linear_combination (poch (-(n : ℂ)) j * poch (-((n-j : ℕ) : ℂ)) l * poch P j *
    poch (P+j) l * poch (R-Q) j * poch (R-N) j * poch (Q+N-R) l * (poch R j)⁻¹) * hch

/-- Whipple's balanced terminating coefficient transformation in convolution form. -/
theorem balanced_4F3_convolution (P Q N E F R : ℂ)
    (hE : 0 < E.re) (hF : 0 < F.re) (hR : 0 < R.re) (n : ℕ)
    (hbal : Q+N-R = E+F-P+n-1) :
    (∑ k ∈ Finset.range (n+1), poch (-(n : ℂ)) k * poch P k * poch Q k * poch N k /
      (poch R k * poch E k * poch F k * k !)) =
    ∑ j ∈ Finset.range (n+1),
      (poch (-(n : ℂ)) j * poch P j * poch (R-Q) j * poch (R-N) j /
        (poch R j * poch E j * poch F j * j !)) *
      (poch (E-P) (n-j) * poch (F-P) (n-j) /
        (poch (E+j) (n-j) * poch (F+j) (n-j))) := by
  have hr := not_neg_nat_of_re_pos hR
  have he (k : ℕ) : poch Q k * poch N k / poch R k =
      ∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) * poch (R-Q) j * poch (R-N) j /
        poch R j * poch (Q+N-R) (k-j) := by
    have ht := saalschutz_binomial_convolution (R-Q) (R-N) R hr k
    simpa only [show R-(R-Q) = Q by ring, show R-(R-N) = N by ring,
      show R-(R-Q)-(R-N) = Q+N-R by ring,
      show Q-(R-N) = Q+N-R by ring] using ht.symm
  have hf : (∑ k ∈ Finset.range (n+1), poch (-(n : ℂ)) k * poch P k * poch Q k * poch N k /
      (poch R k * poch E k * poch F k * k !)) =
      ∑ k ∈ Finset.range (n+1), poch (-(n : ℂ)) k * poch P k / (poch E k * poch F k * k !) *
        (∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) * poch (R-Q) j * poch (R-N) j /
          poch R j * poch (Q+N-R) (k-j)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← he]
    ring
  rw [hf, balanced_4F3_double_sum P Q N E F R hE hF]
  apply Finset.sum_congr rfl
  intro j hj
  rw [balanced_inner_sum hE hF n j (by simpa using hj) hbal]

end DLMF.Hypergeometric
