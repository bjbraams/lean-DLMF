/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.WhippleRecurrence
public import DLMF.QHypergeometric.WhippleProducts
public import DLMF.QHypergeometric.PfaffSaalschutz

/-!
# The terminating q-Whipple sum

A finite telescoping recurrence and its two initial values prove the balanced terminating
sum of DLMF 17.7.11. Its paired upper parameters are combined before taking quotients,
so the result includes zero upper parameters and vanishing product values.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.WhippleSummation

/-- The recurrence and its initial values identify the finite sum with the product value. -/
theorem finiteSum_eq_productValue {e x q : ℂ} (he : e ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hEf : ∀ j : ℕ, 1 - e * q ^ j ≠ 0)
    (hXf : ∀ j : ℕ, 1 - (x * q / e) * q ^ j ≠ 0) (n : ℕ) :
    WhippleRecurrence.finiteSum e x q n = WhippleProducts.productValue e x q n := by
  have hE := qPochhammer_ne_zero_of_factors hq hEf
  have hX := qPochhammer_ne_zero_of_factors hq hXf
  have hEi := qPochhammerInf_ne_zero hq hEf
  have hXi := qPochhammerInf_ne_zero hq hXf
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [WhippleRecurrence.finiteSum_zero, WhippleProducts.productValue_zero hq0 hq _ _ hEi hXi]
  | one => rw [WhippleRecurrence.finiteSum_one he hq0 hq hE hX,
      WhippleProducts.productValue_one hq0 hq _ _ hEi hXi]
  | more n ih _ =>
    have hS := WhippleRecurrence.finiteSum_contiguous he hq0 hq hE hX n
    have hV := WhippleProducts.productValue_contiguous he hq0 hq x n
    have hA : WhippleRecurrence.nextFactor e x q (q ^ n) =
        (1 - e * q ^ (n + 1)) * (e - x * q ^ (n + 2)) := by
      simp only [WhippleRecurrence.nextFactor, pow_succ]
      ring
    have hB : WhippleRecurrence.currentFactor e x q (q ^ n) =
        (e - q ^ (n + 2)) * (x - e * q ^ (n + 1)) := by
      simp only [WhippleRecurrence.currentFactor, pow_succ]
      ring
    rw [hA, hB, ih] at hS
    have hz : e - x * q ^ (n + 2) ≠ 0 := by
      intro hn
      apply hXf (n + 1)
      rw [pow_succ q (n + 1)] at hn
      field_simp
      linear_combination hn
    exact mul_left_cancel₀ (mul_ne_zero (hEf (n + 1)) hz) (hS.trans hV.symm)

/-- Pairing opposite upper parameters and the two self-denominator factors gives the kernel. -/
lemma qPhiTerm_eq_kernel (c e q : ℂ) (n k : ℕ) :
    qPhiTerm [q ^ (-(n : ℤ)), q ^ (n + 1), c, -c]
        [e, c ^ 2 * q / e, -q] q q k =
      WhippleRecurrence.kernel e (c ^ 2) q (q ^ n) k := by
  have hc := qPochhammer_squared c q k
  have hq := qPochhammer_squared q q k
  have hexp : qPhiExponent [q ^ (-(n : ℤ)), q ^ (n + 1), c, -c]
      [e, c ^ 2 * q / e, -q] = 0 := by simp [qPhiExponent]
  unfold qPhiTerm
  rw [hexp]
  simp only [zpow_zero, mul_one, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, WhippleRecurrence.kernel, zpow_neg,
    zpow_natCast, hc, hq, pow_succ q n]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The terminating q-Whipple identity at all globally regular lower parameters. -/
theorem four_phi_three_infinite_product {c e q : ℂ} (he : e ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n : ℕ) (hd : QDenominatorRegular [e, c ^ 2 * q / e, -q] q) :
    qPhi [q ^ (-(n : ℤ)), q ^ (n + 1), c, -c] [e, c ^ 2 * q / e, -q] q q =
      q ^ ((n + 1).choose 2) * qPochhammerListInf
        [e * q ^ (-(n : ℤ)), e * q ^ (n + 1), c ^ 2 * q ^ (1 - (n : ℤ)) / e,
          c ^ 2 * q ^ (n + 2) / e] (q ^ 2) / qPochhammerListInf [e, c ^ 2 * q / e] q := by
  have hEf (j : ℕ) : 1 - e * q ^ j ≠ 0 := sub_ne_zero.mpr (hd e (by simp) j).symm
  have hXf (j : ℕ) : 1 - (c ^ 2 * q / e) * q ^ j ≠ 0 :=
    sub_ne_zero.mpr (hd (c ^ 2 * q / e) (by simp) j).symm
  rw [PfaffSaalschutz.qPhi_eq_sum_of_mem hq0 n (by simp)]
  simp_rw [qPhiTerm_eq_kernel]
  change WhippleRecurrence.finiteSum e (c ^ 2) q n = _
  rw [finiteSum_eq_productValue he hq0 hq hEf hXf]
  have hb : c ^ 2 * q / e * q ^ (-(n : ℤ)) = c ^ 2 * q ^ (1 - (n : ℤ)) / e := by
    simp only [zpow_sub₀ hq0, zpow_one, zpow_neg, zpow_natCast]
    ring
  have hf : c ^ 2 * q / e * q ^ (n + 1) = c ^ 2 * q ^ (n + 2) / e := by
    rw [pow_succ q (n + 1)]
    ring
  unfold WhippleProducts.productValue WhippleProducts.shiftedProduct
  rw [hb, hf]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  ring

end DLMF.QHypergeometric.WhippleSummation
