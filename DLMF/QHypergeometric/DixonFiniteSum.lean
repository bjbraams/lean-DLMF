/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.DixonPolynomial
public import DLMF.QHypergeometric.Calculus.QBinomial

/-!
# Finite-series normalization of the q-Dixon polynomial identity

Index reversal converts the finite lower-parameter regularity hypotheses into nonvanishing
of the paired factorials. The denominator-free identity therefore gives the cancelled
terminating q-Dixon quotient at every regular terminating parameter, including removable
zeros of its uncancelled product form.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries DLMF.QSeries.TripleProduct

namespace DLMF.QHypergeometric.DixonFiniteSum

/-- Lower-parameter regularity after index reversal implies nonvanishing of the original
shifted factorial. -/
theorem pochhammer_ne_zero_of_reverse {b q : ℂ} (hb : b ≠ 0) (hq0 : q ≠ 0) (N : ℕ)
    (hd : qPochhammer (q ^ (1 - (N : ℤ)) / b) q N ≠ 0) : qPochhammer b q N ≠ 0 := by
  have h := qPochhammer_sub_index hb hq0 (k := N) (n := N) le_rfl hd
  simp only [Nat.sub_self, qPochhammer_zero] at h
  intro he
  rw [he, zero_div, zero_mul, zero_mul] at h
  exact one_ne_zero h

/-- The powers in the reversed two-parameter summand give the q-Dixon argument. -/
theorem power_balance {b c q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hq0 : q ≠ 0) (n k : ℕ) :
    (-1 : ℂ) ^ k * q ^ (((2 * n : ℕ) : ℤ) * k - (k.choose 2 : ℤ)) *
      DixonPolynomial.weight q n k * (-q / b) ^ k * (-q / c) ^ k *
      (q ^ ((k.choose 2 : ℤ) - ((2 * n : ℕ) : ℤ) * k)) ^ 2 =
        (q ^ (2 - (n : ℤ)) / (b * c)) ^ k := by
  have hs : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hfour : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k * (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    calc
      _ = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) := by ring
      _ = 1 := by rw [hs]; norm_num
  have ht : (k.choose 2 : ℤ) = tri k := by simpa using tri_sub_cast k 0
  have hbpow : (-q / b) ^ k = (-1 : ℂ) ^ k * q ^ k / b ^ k := by
    rw [neg_div, neg_pow, div_pow]
    ring
  have hcpow : (-q / c) ^ k = (-1 : ℂ) ^ k * q ^ k / c ^ k := by
    rw [neg_div, neg_pow, div_pow]
    ring
  have he : q ^ (((2 * n : ℕ) : ℤ) * k - (k.choose 2 : ℤ)) *
      q ^ DixonPolynomial.exponent n k * q ^ k * q ^ k *
      (q ^ ((k.choose 2 : ℤ) - ((2 * n : ℕ) : ℤ) * k)) ^ 2 =
        (q ^ (2 - (n : ℤ))) ^ k := by
    rw [sq]
    simp only [← zpow_natCast q k, ← zpow_add₀ hq0]
    rw [← zpow_natCast (q ^ (2 - (n : ℤ))) k, ← zpow_mul]
    congr 1
    simp only [DixonPolynomial.exponent, ht, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hbpow, hcpow, DixonPolynomial.weight, div_pow, mul_pow]
  field_simp
  linear_combination
    ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k * (-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * he +
      ((q ^ (2 - (n : ℤ))) ^ k) * hfour

/-- Each regular terminating q-Dixon term agrees with its cleared polynomial summand. -/
theorem term_mul_pochhammer {b c q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n k : ℕ) (hk : k ≤ 2 * n)
    (hB : qPochhammer (q ^ (1 - ((2 * n : ℕ) : ℤ)) / b) q k ≠ 0)
    (hC : qPochhammer (q ^ (1 - ((2 * n : ℕ) : ℤ)) / c) q k ≠ 0) :
    qPhiTerm [q ^ (-((2 * n : ℕ) : ℤ)), b, c]
        [q ^ (1 - ((2 * n : ℕ) : ℤ)) / b, q ^ (1 - ((2 * n : ℕ) : ℤ)) / c] q
        (q ^ (2 - (n : ℤ)) / (b * c)) k *
      (qPochhammer b q (2 * n) * qPochhammer c q (2 * n)) =
        qBinom q (2 * n) k * DixonPolynomial.weight q n k *
          DixonPolynomial.pair b q (2 * n) k * DixonPolynomial.pair c q (2 * n) k := by
  have hQ := qPochhammer_self_ne_zero hq k
  have hbsub := qPochhammer_sub_index hb hq0 hk hB
  have hcsub := qPochhammer_sub_index hc hq0 hk hC
  have hp := power_balance hb hc hq0 n k
  have he : qPhiExponent [q ^ (-((2 * n : ℕ) : ℤ)), b, c]
      [q ^ (1 - ((2 * n : ℕ) : ℤ)) / b, q ^ (1 - ((2 * n : ℕ) : ℤ)) / c] = 0 := by
    simp [qPhiExponent]
  simp only [qPhiTerm, he, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, zpow_zero]
  rw [qBinom_terminating_ratio hq0 hq hk]
  dsimp [DixonPolynomial.pair]
  rw [hbsub, hcsub]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hB hC hbsub hcsub hp ⊢
  field_simp at hp ⊢
  linear_combination
    -(qPochhammer (q ^ (-(2 * (n : ℤ)))) q k * qPochhammer b q k *
      qPochhammer c q k * qPochhammer b q (2 * n) * qPochhammer c q (2 * n)) * hp

/-- Finite lower-parameter regularity gives both nonvanishing shifted factorials. -/
theorem pochhammer_ne_zero_of_regular {b c q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hq0 : q ≠ 0) (n : ℕ)
    (hd : QDenominatorRegularThrough [q ^ (1 - ((2 * n : ℕ) : ℤ)) / b,
      q ^ (1 - ((2 * n : ℕ) : ℤ)) / c] q (2 * n)) :
    qPochhammer b q (2 * n) ≠ 0 ∧ qPochhammer c q (2 * n) ≠ 0 := by
  have hd' : qPochhammer (q ^ (1 - ((2 * n : ℕ) : ℤ)) / b) q (2 * n) *
      qPochhammer (q ^ (1 - ((2 * n : ℕ) : ℤ)) / c) q (2 * n) ≠ 0 := by
    simpa [QDenominatorRegularThrough, qPochhammerList] using hd
  exact ⟨pochhammer_ne_zero_of_reverse hb hq0 _ (left_ne_zero_of_mul hd'),
    pochhammer_ne_zero_of_reverse hc hq0 _ (right_ne_zero_of_mul hd')⟩

/-- The terminating basic hypergeometric series equals the normalized polynomial sum. -/
theorem qPhi_eq_cleared_quotient {b c q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n : ℕ)
    (hd : QDenominatorRegularThrough [q ^ (1 - ((2 * n : ℕ) : ℤ)) / b,
      q ^ (1 - ((2 * n : ℕ) : ℤ)) / c] q (2 * n)) :
    qPhi [q ^ (-((2 * n : ℕ) : ℤ)), b, c]
        [q ^ (1 - ((2 * n : ℕ) : ℤ)) / b, q ^ (1 - ((2 * n : ℕ) : ℤ)) / c] q
        (q ^ (2 - (n : ℤ)) / (b * c)) =
      DixonPolynomial.clearedValue b c q n /
        (qPochhammer b q (2 * n) * qPochhammer c q (2 * n)) := by
  obtain ⟨hPb, hPc⟩ := pochhammer_ne_zero_of_regular hb hc hq0 n hd
  have hd' : qPochhammer (q ^ (1 - ((2 * n : ℕ) : ℤ)) / b) q (2 * n) *
      qPochhammer (q ^ (1 - ((2 * n : ℕ) : ℤ)) / c) q (2 * n) ≠ 0 := by
    simpa [QDenominatorRegularThrough, qPochhammerList] using hd
  have hB := left_ne_zero_of_mul hd'
  have hC := right_ne_zero_of_mul hd'
  apply (eq_div_iff (mul_ne_zero hPb hPc)).mpr
  rw [qPhi_terminates hq0 (2 * n), qPhiPartial, sum_mul]
  rw [sum_congr rfl (fun k hk => term_mul_pochhammer hb hc hq0 hq n k
    (by simp at hk; omega)
    (qPochhammer_ne_zero_of_le hB (by simp at hk; omega))
    (qPochhammer_ne_zero_of_le hC (by simp at hk; omega)))]
  exact DixonPolynomial.clearedSum_eq_value hb hq0 hq c n

/-- The cancelled product form of the terminating q-Dixon sum. -/
theorem qPhi_eq_cancelled_quotient {b c q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n : ℕ)
    (hd : QDenominatorRegularThrough [q ^ (1 - (2 * n : ℤ)) / b,
      q ^ (1 - (2 * n : ℤ)) / c] q (2 * n)) :
    qPhi [q ^ (-(2 * n : ℤ)), b, c]
        [q ^ (1 - (2 * n : ℤ)) / b, q ^ (1 - (2 * n : ℤ)) / c] q
        (q ^ (2 - (n : ℤ)) / (b * c)) =
      qPochhammerList [q ^ (n + 1), b * c * q ^ n] q n /
        qPochhammerList [b * q ^ n, c * q ^ n] q n := by
  have hd' : QDenominatorRegularThrough [q ^ (1 - ((2 * n : ℕ) : ℤ)) / b,
      q ^ (1 - ((2 * n : ℕ) : ℤ)) / c] q (2 * n) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd
  obtain ⟨hPb, hPc⟩ := pochhammer_ne_zero_of_regular hb hc hq0 n hd'
  have hb0 := qPochhammer_ne_zero_of_le hPb (by omega : n ≤ 2 * n)
  have hc0 := qPochhammer_ne_zero_of_le hPc (by omega : n ≤ 2 * n)
  have hsplit (a : ℂ) : qPochhammer a q (2 * n) =
      qPochhammer a q n * qPochhammer (a * q ^ n) q n := by
    rw [two_mul, qPochhammer_add]
  have hb1 : qPochhammer (b * q ^ n) q n ≠ 0 := by
    rw [hsplit] at hPb
    exact right_ne_zero_of_mul hPb
  have hc1 : qPochhammer (c * q ^ n) q n ≠ 0 := by
    rw [hsplit] at hPc
    exact right_ne_zero_of_mul hPc
  have h := qPhi_eq_cleared_quotient hb hc hq0 hq n hd'
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [h]
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, DixonPolynomial.clearedValue]
  rw [hsplit b, hsplit c]
  field_simp

end DLMF.QHypergeometric.DixonFiniteSum
