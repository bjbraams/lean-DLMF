/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ClausenSecondRecurrence

/-!
# Initial values for the q-Clausen recurrences

The first three truncations identify the square of the four-phi-three sum with the
five-phi-four sum. Fixed lower-parameter regularity supplies the needed cancellations.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.ClausenRecurrence

/-- The first finite sum has constant value one at truncation zero. -/
@[simp] lemma firstSum_zero (S β q : ℂ) : firstSum S β q 0 = 1 := by
  simp [firstSum, firstKernel, weightedKernel, firstWeight, quadraticPochhammer]

/-- The second finite sum has constant value one at truncation zero. -/
@[simp] lemma secondSum_zero (S β q : ℂ) : secondSum S β q 0 = 1 := by
  simp [secondSum, secondKernel, weightedKernel, secondWeight, quadraticPochhammer]

/-- The first finite sum at truncation one. -/
lemma firstSum_one {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) : firstSum S β q 1 = S / (1 + β) := by
  have hq1 : 1 - q ≠ 0 := by
    simpa only [pow_zero, mul_one] using one_sub_mul_pow_ne_zero_of_norm hq hq 0
  have hB1 : 1 - β ^ 2 * q ≠ 0 := by
    simpa only [pow_one] using (sub_ne_zero.mpr (hB 1).symm)
  have hplus : 1 + β ≠ 0 := by
    intro he
    apply hB 0
    simp only [pow_zero, mul_one]
    linear_combination (β - 1) * he
  norm_num only [firstSum, firstKernel, weightedKernel, firstWeight, quadraticPochhammer,
    sum_range_succ, sum_range_zero, Nat.reduceAdd, qPochhammer_succ, qPochhammer_zero,
    pow_zero, pow_one, mul_one, one_mul, one_div_one, add_zero, zero_add, neg_mul, sub_neg_eq_add]
  field_simp
  ring_nf
  field_simp [hB1]
  ring

/-- The second finite sum at truncation one. -/
lemma secondSum_one {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) : secondSum S β q 1 = (S / (1 + β)) ^ 2 := by
  have hq1 : 1 - q ≠ 0 := by
    simpa only [pow_zero, mul_one] using one_sub_mul_pow_ne_zero_of_norm hq hq 0
  have hB0 : 1 - β ^ 2 ≠ 0 := by
    simpa only [pow_zero, mul_one] using (sub_ne_zero.mpr (hB 0).symm)
  have hB1 : 1 - β ^ 2 * q ≠ 0 := by
    simpa only [pow_one] using (sub_ne_zero.mpr (hB 1).symm)
  have hplus : 1 + β ≠ 0 := by
    intro he
    apply hB 0
    simp only [pow_zero, mul_one]
    linear_combination (β - 1) * he
  norm_num only [secondSum, secondKernel, weightedKernel, secondWeight, quadraticPochhammer,
    sum_range_succ, sum_range_zero, Nat.reduceAdd, qPochhammer_succ, qPochhammer_zero,
    pow_zero, pow_one, mul_one, one_mul, one_div_one, add_zero, zero_add, neg_mul, sub_neg_eq_add]
  field_simp
  ring_nf
  field_simp [hB1]
  ring

/-- The first finite sum at truncation two, from its three-term recurrence. -/
lemma firstSum_two {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) :
    firstSum S β q 2 = (S ^ 2 * (1 - β * q) - β * (1 - q) * (1 + β)) /
      ((1 + β) * (1 - β ^ 2 * q)) := by
  have hB1 : 1 - β ^ 2 * q ≠ 0 := by
    simpa only [pow_one] using (sub_ne_zero.mpr (hB 1).symm)
  have hplus : 1 + β ≠ 0 := by
    intro he
    apply hB 0
    simp only [pow_zero, mul_one]
    linear_combination (β - 1) * he
  have h := firstSum_contiguous hq0 hq hB S 0
  rw [firstSum_zero, firstSum_one hq0 hq hB] at h
  norm_num only [Nat.reduceAdd, pow_one, mul_one] at h
  apply (eq_div_iff (mul_ne_zero hplus hB1)).mpr
  field_simp at h
  linear_combination h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The second finite sum at truncation two. -/
lemma secondSum_two {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) :
    secondSum S β q 2 = ((S ^ 2 * (1 - β * q) - β * (1 - q) * (1 + β)) /
      ((1 + β) * (1 - β ^ 2 * q))) ^ 2 := by
  have hq1 : 1 - q ≠ 0 := by
    simpa only [pow_zero, mul_one] using one_sub_mul_pow_ne_zero_of_norm hq hq 0
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa only [qPochhammer_one] using qPochhammer_self_ne_zero
      (show ‖q ^ 2‖ < 1 by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)) 1
  have hB0 : 1 - β ^ 2 ≠ 0 := by
    simpa only [pow_zero, mul_one] using (sub_ne_zero.mpr (hB 0).symm)
  have hB1 : 1 - β ^ 2 * q ≠ 0 := by
    simpa only [pow_one] using (sub_ne_zero.mpr (hB 1).symm)
  have hB2 : 1 - β ^ 2 * q ^ 2 ≠ 0 := sub_ne_zero.mpr (hB 2).symm
  have hB3 : 1 - β ^ 2 * q ^ 3 ≠ 0 := sub_ne_zero.mpr (hB 3).symm
  have hplus : 1 + β ≠ 0 := by
    intro he
    apply hB 0
    simp only [pow_zero, mul_one]
    linear_combination (β - 1) * he
  have hplusq : 1 + β * q ≠ 0 := by
    intro he
    apply hB 2
    linear_combination (β * q - 1) * he
  have hzero : secondKernel S β q (q ^ 2) 0 = 1 := by
    simp [secondKernel, weightedKernel, secondWeight, quadraticPochhammer]
  have hone : secondKernel S β q (q ^ 2) 1 =
      -(1 + q) * (1 - β ^ 2 * q ^ 2) * ((1 + β) ^ 2 - S ^ 2) /
        (q * (1 - β ^ 2 * q) * (1 + β) ^ 2) := by
    rw [show 1 = 0 + 1 by rfl, secondKernel_succ, hzero]
    simp only [pow_zero, mul_one, one_mul]
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring_nf at hB0 hB1 hB2 hB3 hq1 hq2 hplus hplusq ⊢
    field_simp
    ring
  have htwo : secondKernel S β q (q ^ 2) 2 =
      (((1 + β) ^ 2 - S ^ 2) * (1 - (S ^ 2 - 2 * β) * q + β ^ 2 * q ^ 2) *
        (1 - β * q) ^ 2) / (q * (1 - β ^ 2 * q) ^ 2 * (1 + β) ^ 2) := by
    rw [show 2 = 1 + 1 by rfl, secondKernel_succ, hone]
    simp only [pow_one, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring_nf at hB0 hB1 hB2 hB3 hq1 hq2 hplus hplusq ⊢
    field_simp
    ring
  simp only [secondSum, sum_range_succ, sum_range_zero, Nat.reduceAdd, zero_add,
    hzero, hone, htwo]
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring_nf at hB0 hB1 hB2 hB3 hq1 hq2 hplus hplusq ⊢
  field_simp
  ring


end DLMF.QHypergeometric.ClausenRecurrence
