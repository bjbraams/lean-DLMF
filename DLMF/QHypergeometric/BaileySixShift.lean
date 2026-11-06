/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileySixRootless

/-!
# Semi-finite index shifts for Bailey's six-psi-six sum

At `x = q^m/a`, the negative tail of the cleared bilateral kernel vanishes below `-m`.
Shifting the remaining indices gives a fully cleared Rogers six-phi-five series.
The root-free central factor supplies the unit Bailey numerator without division by
any shifted lower product.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- The argument of the shifted unilateral sum at the geometric parameter node. -/
def shiftArgument (a b c d q : ℂ) (m : ℕ) : ℂ := a * q ^ (m + 1) / (b * c * d)

/-- The constant left by shifting the bilateral series from `-m` to zero. -/
def shiftFactor (a b c d q : ℂ) (m : ℕ) : ℂ :=
  (1 - a / q ^ (2 * m)) * qPochhammerInf q q * qPochhammerInf (q / b) q *
    qPochhammerInf (q / c) q * qPochhammerInf (q / d) q *
    qPochhammerInf (q ^ (m + 1) / a) q * qPochhammerInf (shiftArgument a b c d q m) q /
      ((1 - a) * qPochhammer (b / q ^ m) q m * qPochhammer (c / q ^ m) q m *
        qPochhammer (d / q ^ m) q m * qPochhammer (a / q ^ (2 * m)) q m *
        shiftArgument a b c d q m ^ m)

/-- The geometric parameter node has the displayed unilateral argument. -/
lemma scale_mul_pow_div {a b c d q : ℂ} (ha : a ≠ 0) (hq0 : q ≠ 0) (m : ℕ) :
    scale a b c d q * (q ^ m / a) = shiftArgument a b c d q m := by
  unfold scale shiftArgument
  rw [pow_succ q m]
  field_simp

/-- The shifted unilateral argument agrees with the geometric-node argument. -/
lemma shifted_argument {a b c d q : ℂ} (hq0 : q ≠ 0) (hbcd : b * c * d ≠ 0) (m : ℕ) :
    (a / q ^ (2 * m)) * q / ((b / q ^ m) * (c / q ^ m) * (d / q ^ m)) =
      shiftArgument a b c d q m := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  unfold shiftArgument
  rw [two_mul, pow_add, pow_succ q m]
  field_simp

/-- The moving lower parameter at a geometric node is a positive power of the base. -/
lemma regular_pow_node {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha : a ≠ 0)
    (hL : QDenominatorRegular [a * q / b, a * q / c, a * q / d] q)
    (hU : ∀ u ∈ [b, c, d], ∀ j : ℕ, u ≠ q ^ (j + 1))
    (m : ℕ) (hm : ∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1)) :
    QBilateralRegular [b, c, d, 1 / (q ^ m / a)]
      [a * q / b, a * q / c, a * q / d, a * q * (q ^ m / a)] q := by
  have hqm := pow_ne_zero m hq0
  constructor
  · intro u hu j
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hL _ (by simp) j
    · exact hL _ (by simp) j
    · exact hL _ (by simp) j
    · rw [show a * q * (q ^ m / a) = q ^ (m + 1) by rw [pow_succ]; field_simp]
      intro he
      have H := norm_mul_pow_lt_one
        (show ‖q ^ (m + 1)‖ < 1 by
          rw [norm_pow]
          exact pow_lt_one₀ (norm_nonneg _) hq (by omega)) hq j
      rw [he, norm_one] at H
      exact lt_irrefl _ H
  · intro u hu j
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hU _ (by simp) j
    · exact hU _ (by simp) j
    · exact hU _ (by simp) j
    · rw [show 1 / (q ^ m / a) = a / q ^ m by field_simp]
      exact hm j

/-- The central factor and shifted upper parameter give the unit Bailey numerator. -/
lemma integerFactor_mul_pochhammer_shift {q : ℂ} (hq0 : q ≠ 0) (a : ℂ) (m k : ℕ) :
    integerFactor a q ((k : ℤ) - m) * qPochhammer (a / q ^ (2 * m)) q k =
      (1 - a / q ^ (2 * m)) / (1 - a) * DLMF.Bailey.unitD (a / q ^ (2 * m)) q k := by
  have he : a * q ^ (2 * ((k : ℤ) - m)) = a / q ^ (2 * m) * q ^ (2 * k) := by
    rw [show (2 : ℤ) * ((k : ℤ) - m) = ((2 * k : ℕ) : ℤ) - ((2 * m : ℕ) : ℤ) by
      push_cast; ring, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    ring
  have H := congrArg (fun z : ℂ => z / (1 - a))
    (DLMF.Bailey.qPochhammer_mul_one_sub_pow (a / q ^ (2 * m)) q k)
  unfold integerFactor
  rw [he]
  linear_combination (norm := (simp only [div_eq_mul_inv]; ring)) H

/-- At a geometric node the negative tail vanishes before the shifted endpoint. -/
lemma term_pow_eq_zero {a b c d q : ℂ} (hq0 : q ≠ 0) (ha : a ≠ 0)
    (m : ℕ) {n : ℤ} (hn : n < -(m : ℤ)) : term a b c d q (q ^ m / a) n = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = Int.negSucc j := by
    cases n with
    | ofNat n => rw [Int.ofNat_eq_natCast] at hn; omega
    | negSucc j => exact ⟨j, rfl⟩
  have hj : m < j + 1 := by omega
  have hqm := pow_ne_zero m hq0
  have hz : a * (q ^ m / a) = q ^ m := by field_simp
  simp only [term, positiveTerm, hz]
  rw [BaileyBilateral.reversedProduct_eq hqm]
  simp only [one_div, qPochhammer_recip_pow_eq_zero hq0 hj, mul_zero, zero_mul]

/-- The geometric-node index shift gives the fully cleared Rogers summand. -/
lemma term_pow_shift {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hbcd : b * c * d ≠ 0)
    (hL : QDenominatorRegular [a * q / b, a * q / c, a * q / d] q)
    (hU : ∀ u ∈ [b, c, d], ∀ j : ℕ, u ≠ q ^ (j + 1))
    (m : ℕ) (hm : ∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1)) (k : ℕ) :
    term a b c d q (q ^ m / a) ((k : ℤ) - m) = shiftFactor a b c d q m *
      SixPhiFiveCleared.term (b / q ^ m) (c / q ^ m) (d / q ^ m) q (a / q ^ (2 * m)) k := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have hqm := pow_ne_zero m hq0
  have hx := div_ne_zero hqm ha
  have he0 := div_ne_zero ha hqm
  have hB := BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq hb (hU b (by simp)) m
  have hC := BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq hc (hU c (by simp)) m
  have hD := BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq hd (hU d (by simp)) m
  have he : a / q ^ m / q ^ m = a / q ^ (2 * m) := by
    rw [two_mul, pow_add]
    field_simp
  have hA : qPochhammer (a / q ^ (2 * m)) q m ≠ 0 := by
    rw [← he]
    exact BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq he0 hm m
  have hz0 : shiftArgument a b c d q m ≠ 0 := div_ne_zero
    (mul_ne_zero ha (pow_ne_zero (m + 1) hq0)) hbcd
  have hQ := qPochhammer_self_ne_zero hq k
  have hInfQ : qPochhammerInf (q * q ^ k) q = qPochhammerInf q q / qPochhammer q q k := by
    apply (eq_div_iff hQ).mpr
    simpa only [mul_comm] using (qPochhammerInf_mul_qPochhammer hq k (a := q)).symm
  have hshift (u : ℂ) : a * q / u * q ^ ((k : ℤ) - m) =
      (a / q ^ (2 * m)) * q / (u / q ^ m) * q ^ k := by
    rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast, two_mul, pow_add]
    field_simp
  have hshiftX : a * q * (q ^ m / a) * q ^ ((k : ℤ) - m) = q * q ^ k := by
    rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp
  have harg := shifted_argument (a := a) hq0 hbcd m
  rw [term_eq_ramanujanTerm hq0 hq ha ha1 hbcd hx
    (regular_pow_node hq0 hq ha hL hU m hm)]
  unfold ramanujanTerm RamanujanPsi.term
  rw [show 1 / (q ^ m / a) = a / q ^ m by field_simp,
    RamanujanPsi.qPochhammerInt_natCast_sub hq0 m k hB,
    RamanujanPsi.qPochhammerInt_natCast_sub hq0 m k hC,
    RamanujanPsi.qPochhammerInt_natCast_sub hq0 m k hD,
    RamanujanPsi.qPochhammerInt_natCast_sub hq0 m k (by simpa only [he] using hA),
    he, hshift b, hshift c, hshift d, hshiftX,
    show q * (q ^ m / a) = q ^ (m + 1) / a by rw [pow_succ]; ring,
    scale_mul_pow_div ha hq0 m, zpow_sub₀ hz0, zpow_natCast, zpow_natCast, hInfQ]
  simp only [one_zpow, mul_one]
  unfold shiftFactor SixPhiFiveCleared.term SixPhiFiveCleared.coefficient
  rw [harg]
  have H := integerFactor_mul_pochhammer_shift hq0 a m k
  linear_combination (norm := (simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring))
    (qPochhammer (b / q ^ m) q k * qPochhammer (c / q ^ m) q k *
      qPochhammer (d / q ^ m) q k *
      qPochhammerInf ((a / q ^ (2 * m)) * q / (b / q ^ m) * q ^ k) q *
      qPochhammerInf ((a / q ^ (2 * m)) * q / (c / q ^ m) * q ^ k) q *
      qPochhammerInf ((a / q ^ (2 * m)) * q / (d / q ^ m) * q ^ k) q *
      qPochhammerInf q q * qPochhammerInf (q / b) q * qPochhammerInf (q / c) q *
      qPochhammerInf (q / d) q * qPochhammerInf (q ^ (m + 1) / a) q *
      qPochhammerInf (shiftArgument a b c d q m) q * shiftArgument a b c d q m ^ k /
      (qPochhammer (b / q ^ m) q m * qPochhammer (c / q ^ m) q m *
        qPochhammer (d / q ^ m) q m * qPochhammer (a / q ^ (2 * m)) q m *
        qPochhammer q q k * shiftArgument a b c d q m ^ m)) * H

end DLMF.QHypergeometric.BaileySixSummation
