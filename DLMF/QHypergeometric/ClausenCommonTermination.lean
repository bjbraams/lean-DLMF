/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ClausenInitialValues
public import DLMF.QHypergeometric.PfaffSaalschutz

/-!
# The q-Clausen identity with a common terminating upper parameter

The first three values and the matching four-term recurrences identify the two finite
sums in DLMF 17.9.18 when both contain the same truncating upper parameter.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.ClausenRecurrence

/-- The leading coefficient in the square recurrence does not vanish at regular parameters. -/
lemma squareLeadingCoefficient_ne_zero {β q : ℂ}
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (n : ℕ) :
    squareLeadingCoefficient β q (q ^ n) ≠ 0 := by
  have hf (j : ℕ) : 1 - β ^ 2 * q ^ j ≠ 0 := sub_ne_zero.mpr (hB j).symm
  have hm (j : ℕ) : 1 - β * q ^ j ≠ 0 := by
    intro he
    apply hB (2 * j)
    rw [Nat.mul_comm 2 j, pow_mul, ← mul_pow, ← sub_eq_zero.mp he, one_pow]
  simpa only [squareLeadingCoefficient, leadingFactor, middleFactor, pow_succ, mul_assoc]
    using mul_ne_zero (mul_ne_zero (hf (n + 1)) (hm (n + 1))) (pow_ne_zero 2 (hf (n + 2)))

/-- The common terminating four-phi-three sum squares to the five-phi-four sum. -/
theorem firstSum_sq_eq_secondSum {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) (n : ℕ) :
    (firstSum S β q n) ^ 2 = secondSum S β q n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => rw [firstSum_one hq0 hq hB, secondSum_one hq0 hq hB]
      | succ n =>
        cases n with
        | zero => rw [firstSum_two hq0 hq hB, secondSum_two hq0 hq hB]
        | succ n =>
          have hF := firstSum_sq_contiguous hq0 hq hB S n
          have hG := secondSum_contiguous hq0 hq hB S n
          rw [ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)] at hF
          exact mul_left_cancel₀ (squareLeadingCoefficient_ne_zero hB n) (hF.trans hG.symm)

/-- Combining the two lower half-base parameters preserves the principal square root. -/
lemma pochhammer_half_base_pair (β q : ℂ) (k : ℕ) :
    qPochhammer (β * q ^ (1 / 2 : ℂ)) q k * qPochhammer (-(β * q ^ (1 / 2 : ℂ))) q k =
      qPochhammer (β ^ 2 * q) (q ^ 2) k := by
  have hroot : (q ^ (1 / 2 : ℂ)) ^ 2 = q := by
    simpa only [one_div, Nat.cast_ofNat] using cpow_nat_inv_pow q (n := 2) (by decide)
  rw [← qPochhammer_squared, mul_pow, hroot]

/-- The four-phi-three summand equals the symmetric first kernel. -/
lemma qPhiTerm_first_eq (a b q : ℂ) (n k : ℕ) :
    qPhiTerm [a, b, (a * b) ^ 2 * q ^ n, q ^ (-(n : ℤ))]
        [a * b * q ^ (1 / 2 : ℂ), -a * b * q ^ (1 / 2 : ℂ), -a * b] q q k =
      firstKernel (a + b) (a * b) q (q ^ n) k := by
  have he : qPhiExponent [a, b, (a * b) ^ 2 * q ^ n, q ^ (-(n : ℤ))]
      [a * b * q ^ (1 / 2 : ℂ), -a * b * q ^ (1 / 2 : ℂ), -a * b] = 0 := by
    simp [qPhiExponent]
  unfold qPhiTerm
  rw [he]
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    zpow_zero, mul_one, firstKernel, weightedKernel, firstWeight,
    quadraticPochhammer_eq_mul, zpow_neg, zpow_natCast]
  rw [← pochhammer_half_base_pair (a * b) q k,
    show -a * b * q ^ (1 / 2 : ℂ) = -(a * b * q ^ (1 / 2 : ℂ)) by ring,
    show -a * b = -(a * b) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The five-phi-four summand equals the symmetric second kernel. -/
lemma qPhiTerm_second_eq (a b q : ℂ) (n k : ℕ) :
    qPhiTerm [a ^ 2, b ^ 2, a * b, (a * b) ^ 2 * q ^ n, q ^ (-(n : ℤ))]
        [a * b * q ^ (1 / 2 : ℂ), -a * b * q ^ (1 / 2 : ℂ), -a * b, (a * b) ^ 2] q q k =
      secondKernel (a + b) (a * b) q (q ^ n) k := by
  have he : qPhiExponent [a ^ 2, b ^ 2, a * b, (a * b) ^ 2 * q ^ n, q ^ (-(n : ℤ))]
      [a * b * q ^ (1 / 2 : ℂ), -a * b * q ^ (1 / 2 : ℂ), -a * b, (a * b) ^ 2] = 0 := by
    simp [qPhiExponent]
  have hquad : quadraticPochhammer ((a + b) ^ 2 - 2 * (a * b)) ((a * b) ^ 2) q k =
      qPochhammer (a ^ 2) q k * qPochhammer (b ^ 2) q k := by
    rw [show (a + b) ^ 2 - 2 * (a * b) = a ^ 2 + b ^ 2 by ring,
      show (a * b) ^ 2 = a ^ 2 * b ^ 2 by ring, quadraticPochhammer_eq_mul]
  unfold qPhiTerm
  rw [he]
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    zpow_zero, mul_one, secondKernel, weightedKernel, secondWeight, hquad,
    zpow_neg, zpow_natCast]
  rw [← pochhammer_half_base_pair (a * b) q k,
    show -a * b * q ^ (1 / 2 : ℂ) = -(a * b * q ^ (1 / 2 : ℂ)) by ring,
    show -a * b = -(a * b) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The q-Clausen identity when both series have the same specified terminating parameter. -/
theorem qPhi_square_common_termination {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, (a * b) ^ 2 * q ^ j ≠ 1) (n : ℕ) :
    qPhi [a, b, (a * b) ^ 2 * q ^ n, q ^ (-(n : ℤ))]
        [a * b * q ^ (1 / 2 : ℂ), -a * b * q ^ (1 / 2 : ℂ), -a * b] q q ^ 2 =
      qPhi [a ^ 2, b ^ 2, a * b, (a * b) ^ 2 * q ^ n, q ^ (-(n : ℤ))]
        [a * b * q ^ (1 / 2 : ℂ), -a * b * q ^ (1 / 2 : ℂ), -a * b, (a * b) ^ 2] q q := by
  rw [PfaffSaalschutz.qPhi_eq_sum_of_mem hq0 n (by simp),
    PfaffSaalschutz.qPhi_eq_sum_of_mem hq0 n (by simp)]
  simp_rw [qPhiTerm_first_eq, qPhiTerm_second_eq]
  exact firstSum_sq_eq_secondSum hq0 hq hB (a + b) n

end DLMF.QHypergeometric.ClausenRecurrence
