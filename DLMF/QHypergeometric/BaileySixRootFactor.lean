/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileySixRootless

/-!
# Paired-root cancellation in Bailey's six-psi-six series

For every integer index, the two very-well-poised root parameters give the root-free
factor `(1-aq^(2n))/(1-a)`. Negative indices use the shifted finite square-root identity;
only the shifted upper-root products need to be nonzero.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- The paired very-well-poised root quotient equals the central factor at every integer. -/
lemma paired_root_quotient {a q r : ℂ} (hr : r ^ 2 = a) (hq0 : q ≠ 0) (ha1 : a ≠ 1)
    (hreg : QBilateralRegular [q * r, -q * r] [r, -r] q) (n : ℤ) :
    qPochhammerInt (q * r) q n * qPochhammerInt (-q * r) q n /
      (qPochhammerInt r q n * qPochhammerInt (-r) q n) = integerFactor a q n := by
  have h1a : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  cases n with
  | ofNat k =>
    have hP (u : ℂ) (hu : u ∈ [r, -r]) : qPochhammer u q k ≠ 0 := by
      rw [qPochhammer_eq_prod]
      apply prod_ne_zero_iff.mpr
      intro j _
      exact sub_ne_zero.mpr (hreg.1 u hu j).symm
    have hR := hP r (by simp)
    have hS := hP (-r) (by simp)
    have H := DLMF.Bailey.qPochhammer_sqrt_factor (q := q) hr k
    simp only [Int.ofNat_eq_natCast, qPochhammerInt_natCast, integerFactor_natCast,
      naturalFactor]
    apply (div_eq_div_iff (mul_ne_zero hR hS) h1a).mpr
    simpa only [mul_comm] using H
  | negSucc j =>
    let m := j + 1
    have hqm : q ^ m ≠ 0 := pow_ne_zero m hq0
    have hR := FiniteBilateral.qPochhammer_div_pow_ne_zero hq0
      (hreg.2 (q * r) (by simp)) m
    have hS := FiniteBilateral.qPochhammer_div_pow_ne_zero hq0
      (hreg.2 (-q * r) (by simp)) m
    have hrs : (r / q ^ m) ^ 2 = a / (q ^ m) ^ 2 := by rw [div_pow, hr]
    have H := DLMF.Bailey.qPochhammer_sqrt_factor (q := q) hrs m
    have he : a / (q ^ m) ^ 2 * q ^ (2 * m) = a := by
      rw [mul_comm 2 m, pow_mul]
      field_simp
    rw [he] at H
    simp only [← mul_div_assoc, ← neg_div] at H
    have hn : Int.negSucc j = -((m : ℕ) : ℤ) := by dsimp [m]; omega
    simp only [zpow_neg, zpow_natCast,
      ← div_eq_mul_inv, hn, integerFactor,
      show (2 : ℤ) * -((m : ℕ) : ℤ) = -((2 * m : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
    change (qPochhammer (q * r / q ^ m) q m)⁻¹ *
        (qPochhammer (-q * r / q ^ m) q m)⁻¹ /
        ((qPochhammer (r / q ^ m) q m)⁻¹ *
          (qPochhammer (-r / q ^ m) q m)⁻¹) =
      (1 - a * (q ^ (2 * m))⁻¹) / (1 - a)
    rw [← mul_inv, ← mul_inv, inv_div_inv]
    have he' : (q ^ m) ^ 2 = q ^ (2 * m) := by rw [← pow_mul]; congr 1; omega
    rw [he'] at H
    apply (div_eq_div_iff (mul_ne_zero hR hS) h1a).mpr
    simpa only [div_eq_mul_inv, mul_comm] using H.symm

/-- Cancelling both root parameters gives the root-free bilateral term for either square root.
No nonvanishing assumption on the remaining four upper parameters is needed pointwise. -/
lemma qPsiTerm_eq_rootlessTerm {a b c d e q r : ℂ} (hr : r ^ 2 = a) (hq0 : q ≠ 0)
    (ha1 : a ≠ 1)
    (hreg : QBilateralRegular [q * r, -q * r, b, c, d, e]
      [r, -r, a * q / b, a * q / c, a * q / d, a * q / e] q) (n : ℤ) :
    qPsiTerm [q * r, -q * r, b, c, d, e]
      [r, -r, a * q / b, a * q / c, a * q / d, a * q / e] q
        (q * a ^ 2 / (b * c * d * e)) n = rootlessTerm a b c d q e⁻¹ n := by
  have hroots : QBilateralRegular [q * r, -q * r] [r, -r] q := by
    constructor
    · intro u hu
      apply hreg.1 u
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu ⊢
      tauto
    · intro u hu
      apply hreg.2 u
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu ⊢
      tauto
  have H := paired_root_quotient hr hq0 ha1 hroots n
  have harg : scale a b c d q * e⁻¹ = q * a ^ 2 / (b * c * d * e) := by
    unfold scale
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  unfold rootlessTerm
  rw [one_div, inv_inv, harg, ← div_eq_mul_inv]
  simp only [qPsiTerm, qPochhammerListInt, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, qPsiExponent, List.length_cons, List.length_nil, sub_self,
    zpow_zero]
  linear_combination (norm := (simp only [div_eq_mul_inv, mul_inv_rev]; ring))
    (qPochhammerInt b q n * qPochhammerInt c q n * qPochhammerInt d q n *
      qPochhammerInt e q n /
      (qPochhammerInt (a * q / b) q n * qPochhammerInt (a * q / c) q n *
        qPochhammerInt (a * q / d) q n * qPochhammerInt (a * q / e) q n) *
      (q * a ^ 2 / (b * c * d * e)) ^ n) * H

end DLMF.QHypergeometric.BaileySixSummation
