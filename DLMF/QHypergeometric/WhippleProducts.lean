/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations.Heine

/-!
# Product recurrence for the terminating q-Whipple sum

The paired base-square products in DLMF 17.7.11 satisfy the same two-step recurrence
as the finite q-Whipple sum. Their finite-product normalization gives the initial values.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.WhippleProducts

/-- The pair of base-square products associated with one lower parameter. -/
def shiftedProduct (z q : ℂ) (n : ℕ) : ℂ :=
  qPochhammerInf (z * q ^ (-(n : ℤ))) (q ^ 2) *
    qPochhammerInf (z * q ^ (n + 1)) (q ^ 2)

/-- The q-Whipple product value, including all removable zeros of its upper products. -/
def productValue (e x q : ℂ) (n : ℕ) : ℂ :=
  q ^ ((n + 1).choose 2) * shiftedProduct e q n * shiftedProduct (x * q / e) q n /
    (qPochhammerInf e q * qPochhammerInf (x * q / e) q)

/-- The paired products shift by two in the truncation parameter. -/
lemma shiftedProduct_contiguous {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (z : ℂ) (n : ℕ) :
    (1 - z * q ^ (n + 1)) * shiftedProduct z q (n + 2) =
      (1 - z * q ^ (-((n + 2 : ℕ) : ℤ))) * shiftedProduct z q n := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hback := qPochhammerInf_shift (a := z * q ^ (-((n + 2 : ℕ) : ℤ))) hQ
  have hforw := qPochhammerInf_shift (a := z * q ^ (n + 1)) hQ
  have harg : z * q ^ (-((n + 2 : ℕ) : ℤ)) * q ^ 2 = z * q ^ (-(n : ℤ)) := by
    rw [mul_assoc, ← zpow_natCast q 2, ← zpow_add₀ hq0]
    congr 2
    omega
  have harg' : z * q ^ (n + 1) * q ^ 2 = z * q ^ (n + 2 + 1) := by
    rw [mul_assoc, ← pow_add]
  rw [harg] at hback
  rw [harg'] at hforw
  unfold shiftedProduct
  rw [hback, hforw]
  ring

/-- The power of the base cancels the two negative shifts in the product recurrence. -/
lemma power_balance {e q : ℂ} (he : e ≠ 0) (hq0 : q ≠ 0) (x : ℂ) (n : ℕ) :
    q ^ ((n + 2 + 1).choose 2) * e *
        (1 - e * q ^ (-((n + 2 : ℕ) : ℤ))) *
        (1 - (x * q / e) * q ^ (-((n + 2 : ℕ) : ℤ))) =
      q ^ ((n + 1).choose 2) * (e - q ^ (n + 2)) * (x - e * q ^ (n + 1)) := by
  have hchoose : (n + 2 + 1).choose 2 = (n + 1).choose 2 + (2 * n + 3) := by
    have hc (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
      simpa [Nat.add_comm] using Nat.choose_succ_succ' j 1
    have h1 := hc (n + 2)
    have h2 : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using hc (n + 1)
    omega
  rw [hchoose, pow_add]
  simp only [zpow_neg, zpow_natCast, pow_succ]
  field_simp
  ring

/-- The infinite product value has the q-Whipple two-step recurrence. -/
theorem productValue_contiguous {e q : ℂ} (he : e ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (x : ℂ) (n : ℕ) :
    ((1 - e * q ^ (n + 1)) * (e - x * q ^ (n + 2))) * productValue e x q (n + 2) =
      ((e - q ^ (n + 2)) * (x - e * q ^ (n + 1))) * productValue e x q n := by
  have hA : (1 - e * q ^ (n + 1)) * (e - x * q ^ (n + 2)) =
      e * (1 - e * q ^ (n + 1)) * (1 - (x * q / e) * q ^ (n + 1)) := by
    rw [pow_succ q (n + 1)]
    field_simp
  unfold productValue
  rw [hA]
  calc
    _ = q ^ ((n + 2 + 1).choose 2) * e *
        ((1 - e * q ^ (n + 1)) * shiftedProduct e q (n + 2)) *
        ((1 - (x * q / e) * q ^ (n + 1)) * shiftedProduct (x * q / e) q (n + 2)) /
          (qPochhammerInf e q * qPochhammerInf (x * q / e) q) := by ring
    _ = _ := by
      rw [shiftedProduct_contiguous hq0 hq, shiftedProduct_contiguous hq0 hq]
      have h := power_balance he hq0 x n
      linear_combination
        (shiftedProduct e q n * shiftedProduct (x * q / e) q n /
          (qPochhammerInf e q * qPochhammerInf (x * q / e) q)) * h

/-- Splitting the first `n` factors relates the paired products to a finite shifted factorial. -/
lemma shiftedProduct_eq_finite_mul {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (z : ℂ) (n : ℕ) :
    shiftedProduct z q n = qPochhammer (z * q ^ (-(n : ℤ))) (q ^ 2) n *
      qPochhammerInf (z * q ^ n) q := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have harg : z * q ^ (-(n : ℤ)) * (q ^ 2) ^ n = z * q ^ n := by
    rw [← pow_mul, mul_assoc, ← zpow_natCast q (2 * n), ← zpow_add₀ hq0, ← zpow_natCast q n]
    congr 2
    push_cast
    ring
  have harg' : z * q ^ n * q = z * q ^ (n + 1) := by rw [pow_succ]; ring
  unfold shiftedProduct
  rw [qPochhammerInf_mul_qPochhammer hQ n, harg, mul_assoc,
    ← harg', ← qPochhammerInf_split_sq hq]

/-- The paired infinite products normalize to the finite q-Whipple quotient. -/
lemma productValue_eq_finite {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (e x : ℂ) (n : ℕ)
    (hE : qPochhammerInf e q ≠ 0) (hX : qPochhammerInf (x * q / e) q ≠ 0) :
    productValue e x q n = q ^ ((n + 1).choose 2) *
      qPochhammer (e * q ^ (-(n : ℤ))) (q ^ 2) n *
      qPochhammer ((x * q / e) * q ^ (-(n : ℤ))) (q ^ 2) n /
        (qPochhammer e q n * qPochhammer (x * q / e) q n) := by
  have hEp := qPochhammerInf_mul_qPochhammer (a := e) hq n
  have hXp := qPochhammerInf_mul_qPochhammer (a := x * q / e) hq n
  have hEt : qPochhammerInf (e * q ^ n) q ≠ 0 := by
    rw [hEp] at hE
    exact right_ne_zero_of_mul hE
  have hXt : qPochhammerInf ((x * q / e) * q ^ n) q ≠ 0 := by
    rw [hXp] at hX
    exact right_ne_zero_of_mul hX
  have hEn : qPochhammer e q n ≠ 0 := by rw [hEp] at hE; exact left_ne_zero_of_mul hE
  have hXn : qPochhammer (x * q / e) q n ≠ 0 := by rw [hXp] at hX; exact left_ne_zero_of_mul hX
  have hXt' : qPochhammerInf (q * q ^ n * x / e) q ≠ 0 := by
    simpa only [show q * q ^ n * x / e = x * q / e * q ^ n by ring] using hXt
  have hXn' : qPochhammer (q * x / e) q n ≠ 0 := by
    simpa only [mul_comm q x] using hXn
  unfold productValue
  rw [shiftedProduct_eq_finite_mul hq0 hq, shiftedProduct_eq_finite_mul hq0 hq, hEp, hXp]
  field_simp

/-- The product value at truncation zero. -/
lemma productValue_zero {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (e x : ℂ)
    (hE : qPochhammerInf e q ≠ 0) (hX : qPochhammerInf (x * q / e) q ≠ 0) :
    productValue e x q 0 = 1 := by
  rw [productValue_eq_finite hq0 hq e x 0 hE hX]
  simp

/-- The product value at truncation one. -/
lemma productValue_one {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (e x : ℂ)
    (hE : qPochhammerInf e q ≠ 0) (hX : qPochhammerInf (x * q / e) q ≠ 0) :
    productValue e x q 1 =
      q * (1 - e / q) * (1 - x / e) / ((1 - e) * (1 - x * q / e)) := by
  rw [productValue_eq_finite hq0 hq e x 1 hE hX]
  norm_num only [Nat.reduceAdd, Nat.choose_self, pow_one, qPochhammer_one, zpow_neg_one]
  rw [show x * q / e * q⁻¹ = x / e by field_simp]
  rfl

end DLMF.QHypergeometric.WhippleProducts
