/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileySixKernel
public import DLMF.QHypergeometric.FiniteBilateralTransformations

/-!
# Reflection and clearing of the root-free six-psi-six kernel

Cancelling the very-well-poised roots leaves four ordinary bilateral shifted-factorial
ratios and a single central factor. Reflection interchanges the two analytic halves;
clearing the lower products makes the integer-index expression suitable for index shifts.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- The root-free very-well-poised factor at an integer index. -/
def integerFactor (a q : ℂ) (n : ℤ) : ℂ := (1 - a * q ^ (2 * n)) / (1 - a)

/-- The root-free bilateral term, before clearing its four lower products. -/
def rootlessTerm (a b c d q x : ℂ) (n : ℤ) : ℂ :=
  integerFactor a q n * qPsiTerm [b, c, d, 1 / x]
    [a * q / b, a * q / c, a * q / d, a * q * x] q (scale a b c d q * x) n

/-- The integer and natural central factors agree at nonnegative indices. -/
lemma integerFactor_natCast (a q : ℂ) (n : ℕ) :
    integerFactor a q (n : ℤ) = naturalFactor a q n := by
  simp only [integerFactor, naturalFactor,
    show (2 : ℤ) * (n : ℤ) = ((2 * n : ℕ) : ℤ) by omega, zpow_natCast]

/-- Reflection inverts the central factor, with its compensating square power of the base. -/
lemma integerFactor_neg_mul {a q : ℂ} (ha : a ≠ 0) (ha1 : a ≠ 1) (hq0 : q ≠ 0) (n : ℕ) :
    integerFactor a q (-(n : ℤ)) * (q ^ 2) ^ n = integerFactor a⁻¹ q (n : ℤ) := by
  have h1a : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  have hai : 1 - a⁻¹ ≠ 0 := by
    intro h
    apply ha1
    have H := congrArg (fun z : ℂ => z * a) h
    rw [sub_mul, one_mul, inv_mul_cancel₀ ha, zero_mul] at H
    linear_combination H
  simp only [integerFactor,
    show (2 : ℤ) * -(n : ℤ) = -((2 * n : ℕ) : ℤ) by push_cast; ring,
    show (2 : ℤ) * (n : ℤ) = ((2 * n : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, ← pow_mul]
  field_simp
  ring

/-- The root-free negative term is the reflected positive term. -/
lemma rootlessTerm_neg_natCast {a b c d q x : ℂ} (ha : a ≠ 0) (ha1 : a ≠ 1)
    (hbcd : b * c * d ≠ 0) (hq0 : q ≠ 0) (hx : x ≠ 0) (n : ℕ) :
    rootlessTerm a b c d q x (-(n : ℤ)) =
      rootlessTerm a⁻¹ (b / a) (c / a) (d / a) q (a * x) (n : ℤ) := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have hU : ∀ u ∈ [b, c, d, 1 / x], u ≠ 0 := by simp [hb, hc, hd, hx]
  have hL : ∀ u ∈ [a * q / b, a * q / c, a * q / d, a * q * x], u ≠ 0 := by
    simp [ha, hq0, hb, hc, hd, hx]
  have H := FiniteBilateral.qPsiTerm_reflect
    (z := scale a b c d q * x) hq0 (by rfl) hU hL n
  have harg : [a * q / b, a * q / c, a * q / d, a * q * x].prod /
      ([b, c, d, 1 / x].prod * (scale a b c d q * x)) =
      (scale a⁻¹ (b / a) (c / a) (d / a) q * (a * x)) * q ^ 2 := by
    simp only [List.prod_cons, List.prod_nil, mul_one, scale]
    field_simp
  have hargs : [a * q / b, a * q / c, a * q / d, a * q * x].map (fun u => q / u) =
      [b / a, c / a, d / a, 1 / (a * x)] := by
    simp only [List.map_cons, List.map_nil]
    congr 1 <;> field_simp
  have hargs' : [b, c, d, 1 / x].map (fun u => q / u) =
      [a⁻¹ * q / (b / a), a⁻¹ * q / (c / a), a⁻¹ * q / (d / a), a⁻¹ * q * (a * x)] := by
    simp only [List.map_cons, List.map_nil]
    congr 1 <;> field_simp
  rw [harg, hargs, hargs'] at H
  have hF := integerFactor_neg_mul ha ha1 hq0 n
  unfold rootlessTerm
  rw [H]
  simp only [qPsiTerm, qPsiExponent, List.length_cons, List.length_nil, sub_self,
    zpow_zero, mul_one, zpow_natCast, mul_pow]
  linear_combination
    (qPochhammerListInt [b / a, c / a, d / a, 1 / (a * x)] q (n : ℤ) /
      qPochhammerListInt [a⁻¹ * q / (b / a), a⁻¹ * q / (c / a), a⁻¹ * q / (d / a),
        a⁻¹ * q * (a * x)] q (n : ℤ) *
      (scale a⁻¹ (b / a) (c / a) (d / a) q * (a * x)) ^ n) * hF

/-- The common clearing product is unchanged by parameter reflection. -/
lemma denominator_reflected {a b c d q x : ℂ} (ha : a ≠ 0) (hbcd : b * c * d ≠ 0) :
    denominator a⁻¹ (b / a) (c / a) (d / a) q (a * x) = denominator a b c d q x := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have he (u : ℂ) (hu : u ≠ 0) : a⁻¹ * q / (u / a) = q / u := by field_simp
  have he' (u : ℂ) (hu : u ≠ 0) : q / (u / a) = a * q / u := by field_simp
  unfold denominator
  rw [he b hb, he c hc, he d hd, he' b hb, he' c hc, he' d hd,
    show a⁻¹ * q * (a * x) = q * x by field_simp,
    show q * (a * x) = a * q * x by ring,
    show scale a⁻¹ (b / a) (c / a) (d / a) q * (a * x) = scale a b c d q * x by
      linear_combination x * scale_reflected_mul (q := q) ha hbcd]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  ring

/-- Multiplying a nonnegative root-free term by the clearing product gives the analytic kernel. -/
lemma positiveTerm_eq_denominator_mul {a b c d q x : ℂ} (hq : ‖q‖ < 1) (hx : x ≠ 0)
    (hL : QDenominatorRegular [a * q / b, a * q / c, a * q / d, a * q * x] q) (n : ℕ) :
    positiveTerm a b c d q x n = denominator a b c d q x *
      rootlessTerm a b c d q x (n : ℤ) := by
  have hB := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hL (by simp :
    a * q / b ∈ [a * q / b, a * q / c, a * q / d, a * q * x]) n
  have hC := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hL (by simp :
    a * q / c ∈ [a * q / b, a * q / c, a * q / d, a * q * x]) n
  have hD := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hL (by simp :
    a * q / d ∈ [a * q / b, a * q / c, a * q / d, a * q * x]) n
  have hX := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hL (by simp :
    a * q * x ∈ [a * q / b, a * q / c, a * q / d, a * q * x]) n
  have hcancel (B C D X U V W Z : ℂ) (hB : B ≠ 0) (hC : C ≠ 0)
      (hD : D ≠ 0) (hX : X ≠ 0) :
      ((B * U) * (C * V) * (D * W) * (X * Z)) / (B * C * D * X) =
        U * V * W * Z := by field_simp
  have hclear :
      (qPochhammerInf (a * q / b) q * qPochhammerInf (a * q / c) q *
        qPochhammerInf (a * q / d) q * qPochhammerInf (a * q * x) q) /
      (qPochhammer (a * q / b) q n * qPochhammer (a * q / c) q n *
        qPochhammer (a * q / d) q n * qPochhammer (a * q * x) q n) =
      qPochhammerInf (a * q / b * q ^ n) q * qPochhammerInf (a * q / c * q ^ n) q *
        qPochhammerInf (a * q / d * q ^ n) q * qPochhammerInf (a * q * x * q ^ n) q := by
    rw [qPochhammerInf_mul_qPochhammer hq n (a := a * q / b),
      qPochhammerInf_mul_qPochhammer hq n (a := a * q / c),
      qPochhammerInf_mul_qPochhammer hq n (a := a * q / d),
      qPochhammerInf_mul_qPochhammer hq n (a := a * q * x)]
    exact hcancel _ _ _ _ _ _ _ _ hB hC hD hX
  simp only [positiveTerm, coefficient, denominator, rootlessTerm, integerFactor_natCast,
    qPsiTerm, qPsiExponent, List.length_cons, List.length_nil, sub_self, zpow_zero,
    mul_one, qPochhammerListInt_natCast, zpow_natCast]
  rw [BaileyBilateral.reversedProduct_eq hx]
  simp only [one_div, qPochhammerList, qPochhammerListInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev] at hclear ⊢
  linear_combination -(naturalFactor a q n * qPochhammer b q n * qPochhammer c q n *
    qPochhammer d q n * qPochhammer x⁻¹ q n * qPochhammerInf (q * b⁻¹) q *
    qPochhammerInf (q * c⁻¹) q * qPochhammerInf (q * d⁻¹) q * qPochhammerInf (q * x) q *
    qPochhammerInf (scale a b c d q * x) q * x ^ n * scale a b c d q ^ n) * hclear


/-- Original upper regularity supplies all reflected lower products. -/
lemma reflected_lower_regular {a b c d q x : ℂ} (ha : a ≠ 0)
    (hbcd : b * c * d ≠ 0) (hx : x ≠ 0)
    (hU : ∀ u ∈ [b, c, d, 1 / x], ∀ j : ℕ, u ≠ q ^ (j + 1)) :
    QDenominatorRegular [a⁻¹ * q / (b / a), a⁻¹ * q / (c / a),
      a⁻¹ * q / (d / a), a⁻¹ * q * (a * x)] q := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have hrec (u : ℂ) (hu : u ∈ [b, c, d, 1 / x]) (hu0 : u ≠ 0) (j : ℕ) :
      q / u * q ^ j ≠ 1 := by
    intro he
    apply hU u hu j
    rw [pow_succ']
    field_simp at he
    linear_combination -he
  have he (u : ℂ) (hu : u ≠ 0) : a⁻¹ * q / (u / a) = q / u := by field_simp
  intro u hu j
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · rw [he b hb]
    exact hrec b (by simp) hb j
  · rw [he c hc]
    exact hrec c (by simp) hc j
  · rw [he d hd]
    exact hrec d (by simp) hd j
  · rw [show a⁻¹ * q * (a * x) = q * x by field_simp]
    simpa only [div_eq_mul_inv, inv_inv, one_mul] using
      hrec (1 / x) (by simp) (one_div_ne_zero hx) j

/-- Every analytic cleared term is its root-free bilateral term times the common product. -/
lemma term_eq_denominator_mul_rootless {a b c d q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hbcd : b * c * d ≠ 0) (hx : x ≠ 0)
    (hreg : QBilateralRegular [b, c, d, 1 / x]
      [a * q / b, a * q / c, a * q / d, a * q * x] q) (n : ℤ) :
    term a b c d q x n = denominator a b c d q x * rootlessTerm a b c d q x n := by
  cases n with
  | ofNat n => exact positiveTerm_eq_denominator_mul hq hx hreg.1 n
  | negSucc n =>
    change positiveTerm a⁻¹ (b / a) (c / a) (d / a) q (a * x) (n + 1) =
      denominator a b c d q x * rootlessTerm a b c d q x (Int.negSucc n)
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) by omega,
      rootlessTerm_neg_natCast ha ha1 hbcd hq0 hx,
      ← denominator_reflected ha hbcd]
    exact positiveTerm_eq_denominator_mul hq (mul_ne_zero ha hx)
      (reflected_lower_regular ha hbcd hx hreg.2) (n + 1)

/-- The integer-index kernel as a product of four denominator-cleared one-psi-one terms. -/
def ramanujanTerm (a b c d q x : ℂ) (n : ℤ) : ℂ :=
  integerFactor a q n * RamanujanPsi.term b q 1 (a * q / b) n *
    RamanujanPsi.term c q 1 (a * q / c) n * RamanujanPsi.term d q 1 (a * q / d) n *
    RamanujanPsi.term (1 / x) q (scale a b c d q * x) (a * q * x) n *
    qPochhammerInf (q / b) q * qPochhammerInf (q / c) q * qPochhammerInf (q / d) q *
    qPochhammerInf (q * x) q * qPochhammerInf (scale a b c d q * x) q

/-- The lower products clear the root-free integer term without losing shifted zeros. -/
lemma denominator_mul_rootlessTerm_eq_ramanujanTerm {a b c d q x : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hL : QDenominatorRegular [a * q / b, a * q / c, a * q / d, a * q * x] q) (n : ℤ) :
    denominator a b c d q x * rootlessTerm a b c d q x n = ramanujanTerm a b c d q x n := by
  have hinf (u : ℂ) (hu : u ∈ [a * q / b, a * q / c, a * q / d, a * q * x]) :
      qPochhammerInf u q / qPochhammerInt u q n = qPochhammerInf (u * q ^ n) q := by
    cases n with
    | ofNat n =>
      have hP := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hL hu n
      rw [Int.ofNat_eq_natCast, qPochhammerInt_natCast, zpow_natCast,
        qPochhammerInf_mul_qPochhammer hq n (a := u)]
      field_simp
    | negSucc n =>
      rw [qPochhammerInt_negSucc]
      simp only [div_eq_mul_inv, inv_inv]
      have he : u * q ^ (Int.negSucc n) * q ^ (n + 1) = u := by
        rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) by omega,
          zpow_neg, zpow_natCast]
        field_simp
      rw [qPochhammerInf_mul_qPochhammer hq (n + 1) (a := u * q ^ (Int.negSucc n)), he,
        show -((n : ℤ) + 1) = Int.negSucc n by omega]
      ring
  simp only [denominator, rootlessTerm, ramanujanTerm, RamanujanPsi.term, qPsiTerm,
    qPsiExponent, List.length_cons, List.length_nil, sub_self, zpow_zero, mul_one,
    one_zpow, qPochhammerListInt, qPochhammerListInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  rw [← hinf (a * q / b) (by simp), ← hinf (a * q / c) (by simp),
    ← hinf (a * q / d) (by simp), ← hinf (a * q * x) (by simp)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The analytic bilateral kernel agrees with the integer product used for index shifts. -/
lemma term_eq_ramanujanTerm {a b c d q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hbcd : b * c * d ≠ 0) (hx : x ≠ 0)
    (hreg : QBilateralRegular [b, c, d, 1 / x]
      [a * q / b, a * q / c, a * q / d, a * q * x] q) (n : ℤ) :
    term a b c d q x n = ramanujanTerm a b c d q x n :=
  (term_eq_denominator_mul_rootless hq0 hq ha ha1 hbcd hx hreg n).trans
    (denominator_mul_rootlessTerm_eq_ramanujanTerm hq0 hq hreg.1 n)

end DLMF.QHypergeometric.BaileySixSummation
