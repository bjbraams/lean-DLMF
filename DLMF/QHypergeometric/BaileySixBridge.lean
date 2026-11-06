/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileySixRootFactor

/-!
# The actual six-psi-six series and its cleared kernel

Original bilateral regularity makes every clearing product nonzero in the convergence
region. The root-pair cancellation then identifies the actual bilateral sum with the
analytic denominator-cleared kernel used in Bailey's summation.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- Removing the very-well-poised roots preserves the four ordinary regularity conditions. -/
lemma rootless_regular_of_regular {a b c d e q r : ℂ}
    (hreg : QBilateralRegular [q * r, -q * r, b, c, d, e]
      [r, -r, a * q / b, a * q / c, a * q / d, a * q / e] q) :
    QBilateralRegular [b, c, d, 1 / e⁻¹]
      [a * q / b, a * q / c, a * q / d, a * q * e⁻¹] q := by
  have H : QBilateralRegular [b, c, d, e]
      [a * q / b, a * q / c, a * q / d, a * q / e] q := by
    constructor
    · intro u hu j
      exact hreg.1 u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)) j
    · intro u hu j
      exact hreg.2 u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)) j
  simpa only [one_div, inv_inv, div_eq_mul_inv, one_mul] using H

/-- The root regularity excludes the singular central parameter one. -/
lemma ne_one_of_regular {a b c d e q : ℂ}
    (hreg : QBilateralRegular [q * sqrt a, -q * sqrt a, b, c, d, e]
      [sqrt a, -sqrt a, a * q / b, a * q / c, a * q / d, a * q / e] q) : a ≠ 1 := by
  have H := hreg.1 (sqrt a) (by simp) 0
  simp only [pow_zero, mul_one] at H
  intro h
  rw [h, sqrt_one] at H
  exact H rfl

/-- Every original clearing factor is nonzero in the six-psi-six convergence region. -/
lemma denominator_ne_zero_of_regular {a b c d e q : ℂ} (_hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (_ha : a ≠ 0) (hz : ‖q * a ^ 2‖ < ‖b * c * d * e‖)
    (hreg : QBilateralRegular [q * sqrt a, -q * sqrt a, b, c, d, e]
      [sqrt a, -sqrt a, a * q / b, a * q / c, a * q / d, a * q / e] q) :
    denominator a b c d q e⁻¹ ≠ 0 := by
  have hBpos : 0 < ‖b * c * d * e‖ := (norm_nonneg _).trans_lt hz
  have hB : b * c * d * e ≠ 0 := norm_pos_iff.mp hBpos
  have hbcd := left_ne_zero_of_mul hB
  have he := right_ne_zero_of_mul hB
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have hR := rootless_regular_of_regular hreg
  have hL := FiniteBilateral.qPochhammerListInf_ne_zero hq hR.1
  have hU0 : ∀ u ∈ [b, c, d, e], u ≠ 0 := by simp [hb, hc, hd, he]
  have hU : ∀ u ∈ [b, c, d, e], ∀ j : ℕ, u ≠ q ^ (j + 1) := by
    intro u hu j
    exact hreg.2 u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)) j
  have hRec : QDenominatorRegular [q / b, q / c, q / d, q / e] q := by
    simpa only [List.map_cons, List.map_nil] using
      FiniteBilateral.qDenominatorRegular_reciprocal hU0 hU
  have hI := FiniteBilateral.qPochhammerListInf_ne_zero hq hRec
  have hArg : scale a b c d q * e⁻¹ = q * a ^ 2 / (b * c * d * e) := by
    simp only [scale, div_eq_mul_inv, mul_inv_rev]
    ring
  have hArgNorm : ‖scale a b c d q * e⁻¹‖ < 1 := by
    rw [hArg, norm_div]
    exact (div_lt_one hBpos).mpr hz
  have hZ := qPochhammerInf_ne_zero_of_norm_lt_one hArgNorm hq
  have hD : denominator a b c d q e⁻¹ =
      qPochhammerListInf [a * q / b, a * q / c, a * q / d, a * q * e⁻¹] q *
      qPochhammerListInf [q / b, q / c, q / d, q / e] q *
      qPochhammerInf (scale a b c d q * e⁻¹) q := by
    simp only [denominator, qPochhammerListInf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, div_eq_mul_inv]
    ring
  rw [hD]
  exact mul_ne_zero (mul_ne_zero hL hI) hZ

/-- Clearing the actual bilateral series gives the analytic integer-index kernel exactly. -/
lemma denominator_mul_qPsi_eq_tsum_term {a b c d e q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hz : ‖q * a ^ 2‖ < ‖b * c * d * e‖)
    (hreg : QBilateralRegular [q * sqrt a, -q * sqrt a, b, c, d, e]
      [sqrt a, -sqrt a, a * q / b, a * q / c, a * q / d, a * q / e] q) :
    denominator a b c d q e⁻¹ *
        qPsi [q * sqrt a, -q * sqrt a, b, c, d, e]
          [sqrt a, -sqrt a, a * q / b, a * q / c, a * q / d, a * q / e] q
          (q * a ^ 2 / (b * c * d * e)) =
      ∑' n : ℤ, term a b c d q e⁻¹ n := by
  have hB : b * c * d * e ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have hbcd := left_ne_zero_of_mul hB
  have he := right_ne_zero_of_mul hB
  have ha1 := ne_one_of_regular hreg
  unfold qPsi
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hr : (Complex.sqrt a) ^ 2 = a := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]
    norm_num
  rw [qPsiTerm_eq_rootlessTerm hr hq0 ha1 hreg]
  exact (term_eq_denominator_mul_rootless hq0 hq ha ha1 hbcd (inv_ne_zero he)
    (rootless_regular_of_regular hreg) n).symm

end DLMF.QHypergeometric.BaileySixSummation
