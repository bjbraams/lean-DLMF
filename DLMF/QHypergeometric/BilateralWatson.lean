/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.FiniteBilateralTransformations

/-!
# The terminating bilateral Watson transformation

Shifting a doubly terminating bilateral series gives Watson's terminating eight-phi-seven
transformation. Finite product reversal supplies the bilateral prefactor, and continuity
retains exceptional shifted lower parameters in DLMF 17.10.3.
-/

@[expose] public noncomputable section

open Complex Finset Filter
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralWatson

/-- A very-well-poised factor for either square root agrees with the unit Bailey numerator.
-/
lemma root_factor_eq_unitD {a q r : ℂ} (hr : r ^ 2 = a) (ha : a ≠ 1) (k : ℕ)
    (hroot : qPochhammer r q k * qPochhammer (-r) q k ≠ 0) :
    qPochhammer a q k * qPochhammer (q * r) q k * qPochhammer (-q * r) q k /
        (qPochhammer r q k * qPochhammer (-r) q k) = DLMF.Bailey.unitD a q k := by
  have h1 := DLMF.Bailey.qPochhammer_sqrt_factor (q := q) hr k
  have h2 := DLMF.Bailey.qPochhammer_mul_one_sub_pow a q k
  have hA : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  rw [div_eq_iff hroot]
  apply mul_left_cancel₀ hA
  linear_combination qPochhammer a q k * h1 +
    qPochhammer r q k * qPochhammer (-r) q k * h2

/-- The eight-phi-seven term is Watson's rational term for either square root. -/
lemma qPhiTerm_eq_watsonR8 {a q r : ℂ} (hr : r ^ 2 = a) (ha : a ≠ 1)
    (b c d e : ℂ) (n k : ℕ)
    (hroot : qPochhammer r q k * qPochhammer (-r) q k ≠ 0) :
    qPhiTerm [q⁻¹ ^ n, q * r, -q * r, b, c, d, e, a]
      [r, -r, a * q / b, a * q / c, a * q / d, a * q / e, a * q * q ^ n]
      q (a ^ 2 * q ^ 2 * q ^ n / (b * c * d * e)) k =
      DLMF.Bailey.watsonR8 a b c d e q n k := by
  have H := root_factor_eq_unitD hr ha k hroot
  simp only [qPhiTerm, qPhiExponent, List.length_cons, List.length_nil]
  norm_num only
  simp only [zpow_zero, mul_one, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, DLMF.Bailey.watsonR8]
  rw [← H]
  ring

/-- The shifted four-phi-three term is Watson's balanced rational term. -/
lemma qPhiTerm_eq_watsonR4 (a b c d e q : ℂ) (n k : ℕ) :
    qPhiTerm [q⁻¹ ^ n, d, e, a * q / (b * c)]
      [a * q / b, a * q / c, d * e * q⁻¹ ^ n / a] q q k =
      DLMF.Bailey.watsonR4 a b c d e q n k := by
  simp only [qPhiTerm, qPhiExponent, List.length_cons, List.length_nil]
  norm_num only
  simp only [zpow_zero, mul_one, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, DLMF.Bailey.watsonR4]
  ring

/-- The shifted root factors and Watson's upper prefactor cancel to one finite factorial. -/
lemma root_products_mul_prefactor {a r q : ℂ} (hr : r ^ 2 = a) (hq0 : q ≠ 0)
    (ha : a ≠ 1) (n : ℕ) :
    (qPochhammer (r / q ^ n) q n * qPochhammer (-r / q ^ n) q n) *
        qPochhammer (a * q / (q ^ n) ^ 2) q (2 * n) =
      (qPochhammer (q * r / q ^ n) q n * qPochhammer (-q * r / q ^ n) q n) *
        qPochhammer (a / (q ^ n) ^ 2) q n * qPochhammer (a / q ^ n) q n := by
  have ht : q ^ n ≠ 0 := pow_ne_zero n hq0
  have ht2 : (q ^ n) ^ 2 = q ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm n 2]
  have hr' : (r / q ^ n) ^ 2 = a / (q ^ n) ^ 2 := by rw [div_pow, hr]
  have hR := DLMF.Bailey.qPochhammer_sqrt_factor (q := q) hr' n
  have he : a / (q ^ n) ^ 2 * q ^ (2 * n) = a := by rw [← ht2]; field_simp
  simp only [show q * (r / q ^ n) = q * r / q ^ n by ring,
    show -q * (r / q ^ n) = -q * r / q ^ n by ring,
    show -(r / q ^ n) = -r / q ^ n by ring, he] at hR
  have hsplit := qPochhammer_add (a * q / (q ^ n) ^ 2) q n n
  rw [← two_mul, show a * q / (q ^ n) ^ 2 * q ^ n = a * q / q ^ n by field_simp]
    at hsplit
  have hA := qPochhammer_succ' (a / (q ^ n) ^ 2) q n
  rw [qPochhammer_succ, show a / (q ^ n) ^ 2 * q ^ n = a / q ^ n by field_simp,
    show a / (q ^ n) ^ 2 * q = a * q / (q ^ n) ^ 2 by ring] at hA
  have hB := qPochhammer_succ' (a / q ^ n) q n
  rw [qPochhammer_succ, div_mul_cancel₀ a ht,
    show a / q ^ n * q = a * q / q ^ n by ring] at hB
  rw [hsplit]
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm ha))
  linear_combination qPochhammer (a * q / (q ^ n) ^ 2) q n *
      qPochhammer (a * q / q ^ n) q n * (-hR) +
    qPochhammer (q * r / q ^ n) q n * qPochhammer (-q * r / q ^ n) q n *
      qPochhammer (a * q / q ^ n) q n * (-hA) +
    qPochhammer (q * r / q ^ n) q n * qPochhammer (-q * r / q ^ n) q n *
      qPochhammer (a / (q ^ n) ^ 2) q n * (-hB)

/-- Finite product reversal gives the scalar part of the bilateral Watson prefactor. -/
lemma reversed_products {a c d e f q : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hq0 : q ≠ 0) (n : ℕ) :
    qPochhammer (a / q ^ n) q n * qPochhammer (a * q * q ^ n / (e * f)) q n *
        qPochhammer (q / c) q n * qPochhammer (q / d) q n *
        (a ^ 2 * q ^ 2 * (q ^ n) ^ 2 / (c * d * e * f)) ^ (-(n : ℤ)) =
      qPochhammer (q / a) q n * qPochhammer (e * f / (a * (q ^ n) ^ 2)) q n *
        qPochhammer (c / q ^ n) q n * qPochhammer (d / q ^ n) q n * q ^ (-(n : ℤ)) := by
  have ht := pow_ne_zero n hq0
  have hA := qPochhammer_shift_negative ha hq0 n
  have hC := qPochhammer_shift_negative hc hq0 n
  have hD := qPochhammer_shift_negative hd hq0 n
  simp only [zpow_neg, zpow_natCast, ← div_eq_mul_inv] at hA hC hD
  have hE := qPochhammer_reverse
    (div_ne_zero (mul_ne_zero he hf) (mul_ne_zero ha (pow_ne_zero 2 ht))) hq0 n
  have harg : q ^ (1 - (n : ℤ)) / (e * f / (a * (q ^ n) ^ 2)) =
      a * q * q ^ n / (e * f) := by
    rw [zpow_sub₀ hq0, zpow_one, zpow_natCast]
    field_simp
  rw [harg] at hE
  have hpow : (-a / q) ^ n *
      (a ^ 2 * q ^ 2 * (q ^ n) ^ 2 / (c * d * e * f)) ^ (-(n : ℤ)) =
      (-e * f / (a * (q ^ n) ^ 2)) ^ n * (-c / q) ^ n * (-d / q) ^ n *
        q ^ (-(n : ℤ)) := by
    simp only [zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
    congr 1
    field_simp
  rw [hA, hC, hD, hE]
  simp only [neg_div]
  have hQ : q ^ (n.choose 2) * ((q ^ n.choose 2)⁻¹) ^ 2 = (q ^ n.choose 2)⁻¹ := by
    field_simp
  calc
    _ = (qPochhammer (q / a) q n * qPochhammer (a * q * q ^ n / (e * f)) q n *
        qPochhammer (q / c) q n * qPochhammer (q / d) q n) *
        (q ^ n.choose 2)⁻¹ * ((-a / q) ^ n *
          (a ^ 2 * q ^ 2 * (q ^ n) ^ 2 / (c * d * e * f)) ^ (-(n : ℤ))) := by ring
    _ = _ := by
      rw [hpow, ← hQ]
      ring

/-- The bilateral eight-psi-eight argument after writing `q^(2n)` as `(q^n)^2`. -/
def argument (a c d e f q : ℂ) (n : ℕ) : ℂ :=
  a ^ 2 * q ^ 2 * (q ^ n) ^ 2 / (c * d * e * f)

/-- The constant introduced by shifting the eight-psi-eight index by `n`. -/
def eightScale (a r c d e f q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer q q n *
    qPochhammerList [r / q ^ n, -r / q ^ n, a * q / (c * q ^ n), a * q / (d * q ^ n),
      a * q / (e * q ^ n), a * q / (f * q ^ n), a * q] q n /
    qPochhammerList [q * r / q ^ n, -q * r / q ^ n, c / q ^ n, d / q ^ n,
      e / q ^ n, f / q ^ n, a / (q ^ n) ^ 2, 1 / (q ^ n) ^ 2] q n *
    argument a c d e f q n ^ (-(n : ℤ))

/-- The constant introduced by shifting the four-psi-four index by `n`. -/
def fourScale (a c d e f q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer q q n *
    qPochhammerList [a * q / (c * q ^ n), a * q / (d * q ^ n),
      e * f / (a * (q ^ n) ^ 2)] q n /
    qPochhammerList [e / q ^ n, f / q ^ n, a * q / (c * d), 1 / (q ^ n) ^ 2] q n *
    q ^ (-(n : ℤ))

/-- Watson's finite prefactor after shifting its parameters. -/
def watsonPrefactor (a e f q : ℂ) (n : ℕ) : ℂ :=
  qProductRatio (2 * n) [a * q / (q ^ n) ^ 2, a * q / (e * f)]
    [a * q / (e * q ^ n), a * q / (f * q ^ n)] q

/-- Combining finite product splitting and reversal gives the bilateral prefactor. -/
lemma eightScale_mul_watsonPrefactor {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hq0 : q ≠ 0) (n : ℕ)
    (hup : ∀ x ∈ [q * r / q ^ n, -q * r / q ^ n, c / q ^ n, d / q ^ n,
      e / q ^ n, f / q ^ n, a / (q ^ n) ^ 2, 1 / (q ^ n) ^ 2, a * q / (c * d)],
        qPochhammer x q n ≠ 0)
    (hlo : ∀ x ∈ [a * q / (e * q ^ n), a * q / (f * q ^ n)],
      qPochhammer x q (2 * n) ≠ 0)
    (hden : ∀ x ∈ [q / c, q / d, a * q / e, a * q / f], qPochhammer x q n ≠ 0) :
    eightScale a r c d e f q n * watsonPrefactor a e f q n =
      qProductRatio n [a * q, q / a, a * q / (c * d), a * q / (e * f)]
        [q / c, q / d, a * q / e, a * q / f] q * fourScale a c d e f q n := by
  have ht := pow_ne_zero n hq0
  have hE := qPochhammer_add (a * q / (e * q ^ n)) q n n
  have hF := qPochhammer_add (a * q / (f * q ^ n)) q n n
  have hEF := qPochhammer_add (a * q / (e * f)) q n n
  rw [← two_mul, show a * q / (e * q ^ n) * q ^ n = a * q / e by field_simp] at hE
  rw [← two_mul, show a * q / (f * q ^ n) * q ^ n = a * q / f by field_simp] at hF
  rw [← two_mul, show a * q / (e * f) * q ^ n = a * q * q ^ n / (e * f) by ring] at hEF
  have hEn : qPochhammer (a * q / (e * q ^ n)) q n ≠ 0 :=
    qPochhammer_ne_zero_of_le (hlo _ (by simp)) (by omega)
  have hFn : qPochhammer (a * q / (f * q ^ n)) q n ≠ 0 :=
    qPochhammer_ne_zero_of_le (hlo _ (by simp)) (by omega)
  have hroot := root_products_mul_prefactor hr hq0 ha1 n
  have hrev := reversed_products ha0 hc0 hd0 he0 hf0 hq0 n
  simp only [eightScale, fourScale, watsonPrefactor, qProductRatio, qPochhammerList,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [hE, hF, hEF]
  have hU1 := hup (q * r / q ^ n) (by simp)
  have hU2 := hup (-q * r / q ^ n) (by simp)
  have hC := hup (c / q ^ n) (by simp)
  have hD := hup (d / q ^ n) (by simp)
  have hUE := hup (e / q ^ n) (by simp)
  have hUF := hup (f / q ^ n) (by simp)
  have hA := hup (a / (q ^ n) ^ 2) (by simp)
  have hQ := hup (1 / (q ^ n) ^ 2) (by simp)
  have hCD := hup (a * q / (c * d)) (by simp)
  have hqc := hden (q / c) (by simp)
  have hqd := hden (q / d) (by simp)
  have hae := hden (a * q / e) (by simp)
  have haf := hden (a * q / f) (by simp)
  change qPochhammer (a / q ^ n) q n * qPochhammer (a * q * q ^ n / (e * f)) q n *
    qPochhammer (q / c) q n * qPochhammer (q / d) q n *
      argument a c d e f q n ^ (-(n : ℤ)) = _ at hrev
  simp only [neg_mul, neg_div] at hroot hU2 ⊢
  generalize qPochhammer (r / q ^ n) q (n) = rootPositive at *
  generalize qPochhammer (-(r / q ^ n)) q (n) = rootNegative at *
  generalize qPochhammer (q * r / q ^ n) q (n) = upperPositive at *
  generalize qPochhammer (-(q * r / q ^ n)) q (n) = upperNegative at *
  generalize qPochhammer (a * q / (q ^ n) ^ 2) q (2 * n) = doubledUpper at *
  generalize qPochhammer (a / (q ^ n) ^ 2) q (n) = upperFactor at *
  generalize qPochhammer (a / q ^ n) q (n) = reversedUpper at *
  generalize qPochhammer (c / q ^ n) q (n) = upperC at *
  generalize qPochhammer (d / q ^ n) q (n) = upperD at *
  generalize qPochhammer (e / q ^ n) q (n) = upperE at *
  generalize qPochhammer (f / q ^ n) q (n) = upperF at *
  generalize qPochhammer (1 / (q ^ n) ^ 2) q (n) = forcedUpper at *
  generalize qPochhammer (a * q / (c * q ^ n)) q (n) = lowerC at *
  generalize qPochhammer (a * q / (d * q ^ n)) q (n) = lowerD at *
  generalize qPochhammer (a * q / (e * q ^ n)) q (n) = lowerE at *
  generalize qPochhammer (a * q / (f * q ^ n)) q (n) = lowerF at *
  generalize qPochhammer (a * q) q (n) = originalUpper at *
  generalize qPochhammer (a * q / (e * f)) q (n) = crossedPrefix at *
  generalize qPochhammer (a * q * q ^ n / (e * f)) q (n) = crossedTail at *
  generalize qPochhammer (e * f / (a * (q ^ n) ^ 2)) q (n) = reversedCrossed at *
  generalize qPochhammer (a * q / (c * d)) q (n) = otherCrossed at *
  generalize qPochhammer (q / a) q (n) = qOverA at *
  generalize qPochhammer (q / c) q (n) = qOverC at *
  generalize qPochhammer (q / d) q (n) = qOverD at *
  generalize qPochhammer (a * q / e) q (n) = originalE at *
  generalize qPochhammer (a * q / f) q (n) = originalF at *
  generalize qPochhammer (q) q (n) = qFactorial at *
  generalize argument a c d e f q n ^ (-(n : ℤ)) = shiftPower at *
  generalize q ^ (-(n : ℤ)) = qPower at *
  field_simp [hU1, hU2, hC, hD, hUE, hUF, hA, hQ, hCD, hqc, hqd, hae, haf, hEn, hFn]
  linear_combination
    (qFactorial * lowerC * lowerD * originalUpper * crossedPrefix *
      qOverC * qOverD * crossedTail * shiftPower) * hroot +
    (qFactorial * lowerC * lowerD * originalUpper * crossedPrefix *
      upperPositive * upperNegative * upperFactor) * hrev

/-- Normalizing the shifted eight-phi-seven parameters gives Watson's rational summand. -/
lemma shifted_qPhiTerm_eq_watsonR8 {a r q : ℂ} (hr : r ^ 2 = a) (hq0 : q ≠ 0)
    (c d e f : ℂ) (n k : ℕ) (ha : a / (q ^ n) ^ 2 ≠ 1)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hroot : qPochhammer (r / q ^ n) q k * qPochhammer (-r / q ^ n) q k ≠ 0) :
    qPhiTerm [1 / (q ^ n) ^ 2, q * r / q ^ n, -q * r / q ^ n,
        c / q ^ n, d / q ^ n, e / q ^ n, f / q ^ n, a / (q ^ n) ^ 2]
      [r / q ^ n, -r / q ^ n, a * q / (c * q ^ n), a * q / (d * q ^ n),
        a * q / (e * q ^ n), a * q / (f * q ^ n), a * q]
      q (argument a c d e f q n) k =
      DLMF.Bailey.watsonR8 (a / (q ^ n) ^ 2) (c / q ^ n) (d / q ^ n)
        (e / q ^ n) (f / q ^ n) q (2 * n) k := by
  have ht := pow_ne_zero n hq0
  have hr' : (r / q ^ n) ^ 2 = a / (q ^ n) ^ 2 := by rw [div_pow, hr]
  have hroot' : qPochhammer (r / q ^ n) q k * qPochhammer (-(r / q ^ n)) q k ≠ 0 := by
    simpa only [neg_div] using hroot
  have H := qPhiTerm_eq_watsonR8 hr' ha (c / q ^ n) (d / q ^ n)
    (e / q ^ n) (f / q ^ n) (2 * n) k hroot'
  have hp : q⁻¹ ^ (2 * n) = 1 / (q ^ n) ^ 2 := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm n 2, one_div]
  rw [hp, show q ^ (2 * n) = (q ^ n) ^ 2 by rw [← pow_mul, Nat.mul_comm n 2]] at H
  have hquotient (x : ℂ) (hx : x ≠ 0) :
      a / (q ^ n) ^ 2 * q / (x / q ^ n) = a * q / (x * q ^ n) := by field_simp
  rw [hquotient c hc0, hquotient d hd0, hquotient e he0, hquotient f hf0,
    show a / (q ^ n) ^ 2 * q * (q ^ n) ^ 2 = a * q by field_simp,
    show (a / (q ^ n) ^ 2) ^ 2 * q ^ 2 * (q ^ n) ^ 2 /
      (c / q ^ n * (d / q ^ n) * (e / q ^ n) * (f / q ^ n)) =
        argument a c d e f q n by dsimp [argument]; field_simp] at H
  simpa only [mul_div_assoc, neg_div] using H

/-- Normalizing the shifted four-phi-three parameters gives Watson's rational summand. -/
lemma shifted_qPhiTerm_eq_watsonR4 {a q : ℂ} (ha0 : a ≠ 0) (hq0 : q ≠ 0)
    (c d e f : ℂ) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (n k : ℕ) :
    qPhiTerm [1 / (q ^ n) ^ 2, e / q ^ n, f / q ^ n, a * q / (c * d)]
      [a * q / (c * q ^ n), a * q / (d * q ^ n), e * f / (a * (q ^ n) ^ 2)] q q k =
      DLMF.Bailey.watsonR4 (a / (q ^ n) ^ 2) (c / q ^ n) (d / q ^ n)
        (e / q ^ n) (f / q ^ n) q (2 * n) k := by
  have ht := pow_ne_zero n hq0
  have H := qPhiTerm_eq_watsonR4 (a / (q ^ n) ^ 2) (c / q ^ n) (d / q ^ n)
    (e / q ^ n) (f / q ^ n) q (2 * n) k
  have hp : q⁻¹ ^ (2 * n) = 1 / (q ^ n) ^ 2 := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm n 2, one_div]
  rw [hp] at H
  have hquotient (x : ℂ) (hx : x ≠ 0) :
      a / (q ^ n) ^ 2 * q / (x / q ^ n) = a * q / (x * q ^ n) := by field_simp
  rw [hquotient c hc0, hquotient d hd0,
    show a / (q ^ n) ^ 2 * q / (c / q ^ n * (d / q ^ n)) = a * q / (c * d) by field_simp,
    show e / q ^ n * (f / q ^ n) * (1 / (q ^ n) ^ 2) / (a / (q ^ n) ^ 2) =
      e * f / (a * (q ^ n) ^ 2) by field_simp] at H
  exact H

/-- Upper parameters have nonzero finite prefixes after shifting the bilateral index. -/
def ShiftedUpperRegular (a r c d e f q : ℂ) (n : ℕ) : Prop :=
  ∀ x ∈ [q * r / q ^ n, -q * r / q ^ n, c / q ^ n, d / q ^ n,
    e / q ^ n, f / q ^ n, a / (q ^ n) ^ 2, 1 / (q ^ n) ^ 2, a * q / (c * d)],
      qPochhammer x q n ≠ 0

/-- Shifted lower parameters are regular throughout the finite Watson transformation. -/
def ShiftedLowerRegular (a r c d e f q : ℂ) (n : ℕ) : Prop :=
  ∀ x ∈ [r / q ^ n, -r / q ^ n, a * q / (c * q ^ n), a * q / (d * q ^ n),
    a * q / (e * q ^ n), a * q / (f * q ^ n), a * q, e * f / (a * (q ^ n) ^ 2)],
      qPochhammer x q (2 * n) ≠ 0

/-- The finite bilateral eight-psi-eight with its terminating parameters placed first. -/
def eightSeries (a r c d e f q : ℂ) (n : ℕ) : ℂ :=
  qPsi [q ^ (-(n : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ n]
    [q ^ (n + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f, a * q * q ^ n]
    q (argument a c d e f q n)

/-- The finite bilateral four-psi-four with its terminating parameters placed first. -/
def fourSeries (a c d e f q : ℂ) (n : ℕ) : ℂ :=
  qPsi [q ^ (-(n : ℤ)), e, f, a * q * q ^ n / (c * d)]
    [q ^ (n + 1), a * q / c, a * q / d, e * f / (a * q ^ n)] q q

/-- The bilateral eight-psi-eight argument is nonzero for nonzero parameters. -/
lemma argument_ne_zero {a c d e f q : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hq : q ≠ 0) (n : ℕ) : argument a c d e f q n ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hq))
    (pow_ne_zero _ (pow_ne_zero _ hq))) (by simp [hc, hd, he, hf])

/-- Shifting the eight-psi-eight gives the finite rational eight-phi-seven sum. -/
lemma eightSeries_eq_sum {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) (ha : a / (q ^ n) ^ 2 ≠ 1)
    (hup : ShiftedUpperRegular a r c d e f q n)
    (hlo : ShiftedLowerRegular a r c d e f q n) :
    eightSeries a r c d e f q n = eightScale a r c d e f q n *
      ∑ k ∈ range (2 * n + 1), DLMF.Bailey.watsonR8 (a / (q ^ n) ^ 2)
        (c / q ^ n) (d / q ^ n) (e / q ^ n) (f / q ^ n) q (2 * n) k := by
  have ht := pow_ne_zero n hq0
  let upper := [q ^ (-(n : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ n]
  let lower := [r, -r, a * q / c, a * q / d, a * q / e, a * q / f, a * q * q ^ n]
  have hmapU : upper.map (fun x => x / q ^ n) =
      [1 / (q ^ n) ^ 2, q * r / q ^ n, -q * r / q ^ n, c / q ^ n,
        d / q ^ n, e / q ^ n, f / q ^ n, a / (q ^ n) ^ 2] := by
    dsimp [upper]
    simp only [List.map_cons, List.map_nil]
    rw [show q ^ (-(n : ℤ)) / q ^ n = 1 / (q ^ n) ^ 2 by
      simp [zpow_neg, zpow_natCast, div_eq_mul_inv, pow_two]]
    simp only [div_div, ← pow_two]
  have hmapL : lower.map (fun x => x / q ^ n) =
      [r / q ^ n, -r / q ^ n, a * q / (c * q ^ n), a * q / (d * q ^ n),
        a * q / (e * q ^ n), a * q / (f * q ^ n), a * q] := by
    dsimp [lower]
    simp only [List.map_cons, List.map_nil]
    rw [mul_div_cancel_right₀ (a * q) ht]
    simp only [div_div]
  have hupper : ∀ x ∈ upper, qPochhammer (x / q ^ n) q n ≠ 0 := by
    intro x hx
    have hx' : x / q ^ n ∈ upper.map (fun y => y / q ^ n) := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmapU] at hx'
    exact hup _ (by simp only [List.mem_cons] at hx' ⊢; tauto)
  have hlower : ∀ x ∈ lower, qPochhammer (x / q ^ n) q n ≠ 0 := by
    intro x hx
    have hx' : x / q ^ n ∈ lower.map (fun y => y / q ^ n) := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmapL] at hx'
    exact qPochhammer_ne_zero_of_le
      (hlo _ (by simp only [List.mem_cons] at hx' ⊢; tauto)) (by omega)
  have H := FiniteBilateral.qPsi_eq_qPhi_shift hq0 hq
    (argument_ne_zero ha0 hc0 hd0 he0 hf0 hq0 n)
    [q * r, -q * r, c, d, e, f, a / q ^ n] lower n n (by simp [lower]) hupper hlower
  change eightSeries a r c d e f q n =
    (qPochhammer q q n * qPochhammerList (lower.map fun x => x / q ^ n) q n /
      qPochhammerList (upper.map fun x => x / q ^ n) q n *
        argument a c d e f q n ^ (-(n : ℤ))) *
      qPhi (upper.map fun x => x / q ^ n) (lower.map fun x => x / q ^ n)
        q (argument a c d e f q n) at H
  rw [hmapU, hmapL] at H
  have hconstant : qPochhammer q q n *
      qPochhammerList [r / q ^ n, -r / q ^ n, a * q / (c * q ^ n), a * q / (d * q ^ n),
        a * q / (e * q ^ n), a * q / (f * q ^ n), a * q] q n /
      qPochhammerList [1 / (q ^ n) ^ 2, q * r / q ^ n, -q * r / q ^ n, c / q ^ n,
        d / q ^ n, e / q ^ n, f / q ^ n, a / (q ^ n) ^ 2] q n *
        argument a c d e f q n ^ (-(n : ℤ)) = eightScale a r c d e f q n := by
    simp only [eightScale, qPochhammerList, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    ring
  rw [hconstant] at H
  have hfirst : 1 / (q ^ n) ^ 2 = q ^ (-((2 * n : ℕ) : ℤ)) := by
    simp only [zpow_neg, zpow_natCast, ← pow_mul, Nat.mul_comm n 2, one_div]
  rw [hfirst, qPhi_terminates hq0 (2 * n), qPhiPartial] at H
  rw [H]
  apply congrArg (eightScale a r c d e f q n * ·)
  apply sum_congr rfl
  intro k hk
  rw [← hfirst]
  have hk' : k ≤ 2 * n := by have := Finset.mem_range.mp hk; omega
  have hroot : qPochhammer (r / q ^ n) q k * qPochhammer (-r / q ^ n) q k ≠ 0 :=
    mul_ne_zero (qPochhammer_ne_zero_of_le (hlo _ (by simp)) hk')
      (qPochhammer_ne_zero_of_le (hlo _ (by simp)) hk')
  exact shifted_qPhiTerm_eq_watsonR8 hr hq0 c d e f n k ha hc0 hd0 he0 hf0 hroot

/-- Shifting the four-psi-four gives Watson's finite balanced four-phi-three sum. -/
lemma fourSeries_eq_sum {a r c d e f q : ℂ} (ha0 : a ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ)
    (hup : ShiftedUpperRegular a r c d e f q n)
    (hlo : ShiftedLowerRegular a r c d e f q n) :
    fourSeries a c d e f q n = fourScale a c d e f q n *
      ∑ k ∈ range (2 * n + 1), DLMF.Bailey.watsonR4 (a / (q ^ n) ^ 2)
        (c / q ^ n) (d / q ^ n) (e / q ^ n) (f / q ^ n) q (2 * n) k := by
  have ht := pow_ne_zero n hq0
  let upper := [q ^ (-(n : ℤ)), e, f, a * q * q ^ n / (c * d)]
  let lower := [a * q / c, a * q / d, e * f / (a * q ^ n)]
  have hmapU : upper.map (fun x => x / q ^ n) =
      [1 / (q ^ n) ^ 2, e / q ^ n, f / q ^ n, a * q / (c * d)] := by
    dsimp [upper]
    simp only [List.map_cons, List.map_nil]
    rw [show q ^ (-(n : ℤ)) / q ^ n = 1 / (q ^ n) ^ 2 by
      simp [zpow_neg, zpow_natCast, div_eq_mul_inv, pow_two],
      show a * q * q ^ n / (c * d) / q ^ n = a * q / (c * d) by field_simp]
  have hmapL : lower.map (fun x => x / q ^ n) =
      [a * q / (c * q ^ n), a * q / (d * q ^ n), e * f / (a * (q ^ n) ^ 2)] := by
    dsimp [lower]
    simp only [List.map_cons, List.map_nil, div_div]
    rw [show a * q ^ n * q ^ n = a * (q ^ n) ^ 2 by ring]
  have hupper : ∀ x ∈ upper, qPochhammer (x / q ^ n) q n ≠ 0 := by
    intro x hx
    have hx' : x / q ^ n ∈ upper.map (fun y => y / q ^ n) := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmapU] at hx'
    exact hup _ (by simp only [List.mem_cons] at hx' ⊢; tauto)
  have hlower : ∀ x ∈ lower, qPochhammer (x / q ^ n) q n ≠ 0 := by
    intro x hx
    have hx' : x / q ^ n ∈ lower.map (fun y => y / q ^ n) := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmapL] at hx'
    exact qPochhammer_ne_zero_of_le (hlo _ (by simp only [List.mem_cons] at hx' ⊢; tauto))
      (by omega)
  have H := FiniteBilateral.qPsi_eq_qPhi_shift hq0 hq hq0
    [e, f, a * q * q ^ n / (c * d)] lower n n (by simp [lower]) hupper hlower
  change fourSeries a c d e f q n =
    (qPochhammer q q n * qPochhammerList (lower.map fun x => x / q ^ n) q n /
      qPochhammerList (upper.map fun x => x / q ^ n) q n * q ^ (-(n : ℤ))) *
        qPhi (upper.map fun x => x / q ^ n) (lower.map fun x => x / q ^ n) q q at H
  rw [hmapU, hmapL] at H
  have hconstant : qPochhammer q q n *
      qPochhammerList [a * q / (c * q ^ n), a * q / (d * q ^ n),
        e * f / (a * (q ^ n) ^ 2)] q n /
      qPochhammerList [1 / (q ^ n) ^ 2, e / q ^ n, f / q ^ n, a * q / (c * d)] q n *
      q ^ (-(n : ℤ)) = fourScale a c d e f q n := by
    simp only [fourScale, qPochhammerList, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    ring
  rw [hconstant] at H
  have hfirst : 1 / (q ^ n) ^ 2 = q ^ (-((2 * n : ℕ) : ℤ)) := by
    simp only [zpow_neg, zpow_natCast, ← pow_mul, Nat.mul_comm n 2, one_div]
  rw [hfirst, qPhi_terminates hq0 (2 * n), qPhiPartial] at H
  rw [H]
  apply congrArg (fourScale a c d e f q n * ·)
  apply sum_congr rfl
  intro k hk
  rw [← hfirst]
  exact shifted_qPhiTerm_eq_watsonR4 ha0 hq0 c d e f hc0 hd0 n k

/-- Watson's finite transformation in the shifted parameters used by the bilateral sum. -/
lemma shifted_watson_sum {a r c d e f q : ℂ} (ha0 : a ≠ 0)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ)
    (hlo : ShiftedLowerRegular a r c d e f q n) :
    (∑ k ∈ range (2 * n + 1), DLMF.Bailey.watsonR8 (a / (q ^ n) ^ 2)
      (c / q ^ n) (d / q ^ n) (e / q ^ n) (f / q ^ n) q (2 * n) k) =
      watsonPrefactor a e f q n *
        ∑ k ∈ range (2 * n + 1), DLMF.Bailey.watsonR4 (a / (q ^ n) ^ 2)
          (c / q ^ n) (d / q ^ n) (e / q ^ n) (f / q ^ n) q (2 * n) k := by
  have ht := pow_ne_zero n hq0
  have hquotient (x : ℂ) (hx : x ≠ 0) :
      a / (q ^ n) ^ 2 * q / (x / q ^ n) = a * q / (x * q ^ n) := by field_simp
  have hB : qPochhammer (a / (q ^ n) ^ 2 * q / (c / q ^ n)) q (2 * n) ≠ 0 := by
    rw [hquotient c hc0]
    exact hlo _ (by simp)
  have hC : qPochhammer (a / (q ^ n) ^ 2 * q / (d / q ^ n)) q (2 * n) ≠ 0 := by
    rw [hquotient d hd0]
    exact hlo _ (by simp)
  have hD : qPochhammer (a / (q ^ n) ^ 2 * q / (e / q ^ n)) q (2 * n) ≠ 0 := by
    rw [hquotient e he0]
    exact hlo _ (by simp)
  have hE : qPochhammer (a / (q ^ n) ^ 2 * q / (f / q ^ n)) q (2 * n) ≠ 0 := by
    rw [hquotient f hf0]
    exact hlo _ (by simp)
  have hY : e / q ^ n * (f / q ^ n) * q⁻¹ ^ (2 * n) / (a / (q ^ n) ^ 2) =
      e * f / (a * (q ^ n) ^ 2) := by
    rw [inv_pow, show q ^ (2 * n) = (q ^ n) ^ 2 by rw [← pow_mul, Nat.mul_comm n 2]]
    field_simp
  have hN : a / (q ^ n) ^ 2 * q * q ^ (2 * n) = a * q := by
    rw [show q ^ (2 * n) = (q ^ n) ^ 2 by rw [← pow_mul, Nat.mul_comm n 2]]
    field_simp
  have H := DLMF.Bailey.watson_transformation_rational (2 * n)
    (div_ne_zero ha0 (pow_ne_zero 2 ht)) (div_ne_zero hc0 ht) (div_ne_zero hd0 ht)
    (div_ne_zero he0 ht) (div_ne_zero hf0 ht) hq0
    (fun k _ => qPochhammer_self_ne_zero hq k) hB hC hD hE
    (by rw [hY]; exact hlo _ (by simp)) (by rw [hN]; exact hlo _ (by simp))
  rw [show a / (q ^ n) ^ 2 * q / (e / q ^ n * (f / q ^ n)) = a * q / (e * f)
      by field_simp, hquotient e he0, hquotient f hf0,
    show a / (q ^ n) ^ 2 * q = a * q / (q ^ n) ^ 2 by ring] at H
  simpa only [watsonPrefactor, qProductRatio, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one] using H

/-- The bilateral Watson transformation when every shifted finite product is regular. -/
lemma eightSeries_eq_fourSeries_of_shifted_regular {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (n : ℕ) (ha : a / (q ^ n) ^ 2 ≠ 1)
    (hup : ShiftedUpperRegular a r c d e f q n)
    (hlo : ShiftedLowerRegular a r c d e f q n)
    (hden : ∀ x ∈ [q / c, q / d, a * q / e, a * q / f], qPochhammer x q n ≠ 0) :
    eightSeries a r c d e f q n =
      qProductRatio n [a * q, q / a, a * q / (c * d), a * q / (e * f)]
        [q / c, q / d, a * q / e, a * q / f] q * fourSeries a c d e f q n := by
  rw [eightSeries_eq_sum hr ha0 hc0 hd0 he0 hf0 hq0 hq n ha hup hlo,
    shifted_watson_sum ha0 hc0 hd0 he0 hf0 hq0 hq n hlo, ← mul_assoc,
    eightScale_mul_watsonPrefactor hr ha0 ha1 hc0 hd0 he0 hf0 hq0 n hup
      (fun x hx => hlo x (by simp only [List.mem_cons] at hx ⊢; tauto)) hden,
    mul_assoc, ← fourSeries_eq_sum ha0 hc0 hd0 hq0 hq n hup hlo]

/-- All shifted products are regular off a finite set near any root parameter; fixed upper
parameters need only the negative-index regularity of the original bilateral series. -/
lemma eventually_shifted_regular {c d e f q : ℂ} (_hc0 : c ≠ 0) (_hd0 : d ≠ 0)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hq0 : q ≠ 0) (n : ℕ) (r₀ : ℂ)
    (hfixed : ∀ x ∈ [c, d, e, f, q ^ (-(n : ℤ))], qPochhammer (x / q ^ n) q n ≠ 0)
    (hden : ∀ x ∈ [q / c, q / d], qPochhammer x q n ≠ 0) :
    ∀ᶠ r in 𝓝[≠] r₀, r ≠ 0 ∧ r ^ 2 ≠ 1 ∧ r ^ 2 / (q ^ n) ^ 2 ≠ 1 ∧
      ShiftedUpperRegular (r ^ 2) r c d e f q n ∧
      ShiftedLowerRegular (r ^ 2) r c d e f q n ∧
      (∀ x ∈ [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f], qPochhammer x q n ≠ 0) := by
  classical
  let linear : Finset ℂ := {q / q ^ n, -q / q ^ n, 1 / q ^ n, -1 / q ^ n}
  let quadratic : Finset ℂ := {1, 1 / (q ^ n) ^ 2, q / (c * d), q / (c * q ^ n),
    q / (d * q ^ n), q / (e * q ^ n), q / (f * q ^ n), q, q / e, q / f}
  have hlinear : ∀ᶠ r in 𝓝[≠] r₀, ∀ u ∈ linear,
      qPochhammer (u * r) q (2 * n + 1) ≠ 0 := by
    rw [eventually_all_finset]
    intro u hu
    simpa only [pow_one] using
      FiniteBilateral.eventually_qPochhammer_mul_pow_ne_zero u q r₀ 1 (2 * n + 1) (by omega)
  have hquadratic : ∀ᶠ r in 𝓝[≠] r₀, ∀ u ∈ quadratic,
      qPochhammer (u * r ^ 2) q (2 * n + 1) ≠ 0 := by
    rw [eventually_all_finset]
    intro u hu
    exact FiniteBilateral.eventually_qPochhammer_mul_pow_ne_zero u q r₀ 2 (2 * n + 1)
      (by omega)
  have hinverse := FiniteBilateral.eventually_qPochhammer_div_pow_ne_zero
    (div_ne_zero (mul_ne_zero he0 hf0) (pow_ne_zero 2 (pow_ne_zero n hq0))) hq0 r₀ 2
      (2 * n + 1) (by omega)
  have hr0 : ∀ᶠ r in 𝓝[≠] r₀, r ≠ 0 :=
    le_cofinite_iff_eventually_ne.mp (nhdsNE_le_cofinite r₀) 0
  have hprefix (x : ℂ) (hx : x ∈ [c, d, e, f, q ^ (-(n : ℤ))]) :
      qPochhammer (x / q ^ n) q n ≠ 0 :=
    hfixed x hx
  have hforced : qPochhammer (1 / (q ^ n) ^ 2) q n ≠ 0 := by
    have H := hprefix (q ^ (-(n : ℤ))) (by simp)
    rw [show q ^ (-(n : ℤ)) / q ^ n = 1 / (q ^ n) ^ 2 by
      simp [zpow_neg, zpow_natCast, div_eq_mul_inv, pow_two]] at H
    exact H
  filter_upwards [hlinear, hquadratic, hinverse, hr0] with r hl hq hi hr
  have hL (u : ℂ) (hu : u ∈ linear) (N : ℕ) (hN : N ≤ 2 * n + 1) :
      qPochhammer (u * r) q N ≠ 0 := qPochhammer_ne_zero_of_le (hl u hu) hN
  have hQ (u : ℂ) (hu : u ∈ quadratic) (N : ℕ) (hN : N ≤ 2 * n + 1) :
      qPochhammer (u * r ^ 2) q N ≠ 0 := qPochhammer_ne_zero_of_le (hq u hu) hN
  have hne (u : ℂ) (hu : u ∈ quadratic) : u * r ^ 2 ≠ 1 := by
    intro he
    have H := hQ u hu 1 (by omega)
    rw [he] at H
    simp [qPochhammer_succ] at H
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul] using hne 1 (by simp [quadratic])
  · rw [show r ^ 2 / (q ^ n) ^ 2 = (1 / (q ^ n) ^ 2) * r ^ 2 by ring]
    exact hne (1 / (q ^ n) ^ 2) (by simp [quadratic])
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [div_mul_eq_mul_div] using hL (q / q ^ n) (by simp [linear]) n (by omega)
    · simpa only [div_mul_eq_mul_div] using hL (-q / q ^ n) (by simp [linear]) n (by omega)
    · exact hprefix c (by simp)
    · exact hprefix d (by simp)
    · exact hprefix e (by simp)
    · exact hprefix f (by simp)
    · rw [show r ^ 2 / (q ^ n) ^ 2 = (1 / (q ^ n) ^ 2) * r ^ 2 by ring]
      exact hQ (1 / (q ^ n) ^ 2) (by simp [quadratic]) n (by omega)
    · exact hforced
    · simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hQ (q / (c * d)) (by simp [quadratic]) n (by omega)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show r / q ^ n = (1 / q ^ n) * r by ring]
      exact hL (1 / q ^ n) (by simp [linear]) (2 * n) (by omega)
    · rw [show -r / q ^ n = (-1 / q ^ n) * r by ring]
      exact hL (-1 / q ^ n) (by simp [linear]) (2 * n) (by omega)
    · simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hQ (q / (c * q ^ n)) (by simp [quadratic]) (2 * n) (by omega)
    · simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hQ (q / (d * q ^ n)) (by simp [quadratic]) (2 * n) (by omega)
    · simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hQ (q / (e * q ^ n)) (by simp [quadratic]) (2 * n) (by omega)
    · simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hQ (q / (f * q ^ n)) (by simp [quadratic]) (2 * n) (by omega)
    · simpa only [mul_comm] using hQ q (by simp [quadratic]) (2 * n) (by omega)
    · simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
        qPochhammer_ne_zero_of_le hi (show 2 * n ≤ 2 * n + 1 by omega)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hden _ (by simp)
    · exact hden _ (by simp)
    · simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hQ (q / e) (by simp [quadratic]) n (by omega)
    · simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hQ (q / f) (by simp [quadratic]) n (by omega)

/-- The finite eight-psi-eight is continuous in a chosen square root on its original regular
parameter domain, independently of extra shifted product exclusions. -/
lemma continuousAt_eightSeries {r c d e f q : ℂ} (hr0 : r ≠ 0)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (_hq : ‖q‖ < 1) (n : ℕ)
    (hB : FiniteBilateral.RegularThrough [q ^ (-(n : ℤ)), q * r, -q * r, c, d, e, f, r ^ 2 / q ^ n]
      [q ^ (n + 1), r, -r, r ^ 2 * q / c, r ^ 2 * q / d, r ^ 2 * q / e,
        r ^ 2 * q / f, r ^ 2 * q * q ^ n] q n) :
    ContinuousAt (fun s => eightSeries (s ^ 2) s c d e f q n) r := by
  let upper : List (ℂ → ℂ) := [fun s => q * s, fun s => -q * s, fun _ => c,
    fun _ => d, fun _ => e, fun _ => f, fun s => s ^ 2 / q ^ n]
  let lower : List (ℂ → ℂ) := [fun s => s, fun s => -s, fun s => s ^ 2 * q / c,
    fun s => s ^ 2 * q / d, fun s => s ^ 2 * q / e, fun s => s ^ 2 * q / f,
    fun s => s ^ 2 * q * q ^ n]
  have hU : ∀ g ∈ upper, ContinuousAt g r := by
    intro g hg
    simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fun_prop
  have hL : ∀ g ∈ lower, ContinuousAt g r := by
    intro g hg
    simp only [lower, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fun_prop
  have hz : ContinuousAt (fun s => argument (s ^ 2) c d e f q n) r := by
    unfold argument
    fun_prop
  have H := FiniteBilateral.continuousAt_qPsi_finite_of_regularThrough hq0 hU hL hz
    (argument_ne_zero (pow_ne_zero 2 hr0) hc0 hd0 he0 hf0 hq0 n) n hB
  simpa only [eightSeries, upper, lower, List.map_cons, List.map_nil] using H

/-- The finite four-psi-four is continuous in the same root parameter on its original regular
parameter domain. -/
lemma continuousAt_fourSeries {r c d e f q : ℂ} (hr0 : r ≠ 0) (hq0 : q ≠ 0)
    (_hq : ‖q‖ < 1) (n : ℕ)
    (hB : FiniteBilateral.RegularThrough [q ^ (-(n : ℤ)), e, f, r ^ 2 * q * q ^ n / (c * d)]
      [q ^ (n + 1), r ^ 2 * q / c, r ^ 2 * q / d, e * f / (r ^ 2 * q ^ n)] q n) :
    ContinuousAt (fun s => fourSeries (s ^ 2) c d e f q n) r := by
  have hR : r ^ 2 * q ^ n ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr0) (pow_ne_zero n hq0)
  let upper : List (ℂ → ℂ) := [fun _ => e, fun _ => f,
    fun s => s ^ 2 * q * q ^ n / (c * d)]
  let lower : List (ℂ → ℂ) := [fun s => s ^ 2 * q / c, fun s => s ^ 2 * q / d,
    fun s => e * f / (s ^ 2 * q ^ n)]
  have hU : ∀ g ∈ upper, ContinuousAt g r := by
    intro g hg
    simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> fun_prop
  have hL : ∀ g ∈ lower, ContinuousAt g r := by
    intro g hg
    simp only [lower, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> fun_prop
  have H := FiniteBilateral.continuousAt_qPsi_finite_of_regularThrough
    hq0 hU hL continuousAt_const hq0 n hB
  simpa only [fourSeries, upper, lower, List.map_cons, List.map_nil] using H

/-- The finite product prefactor is continuous wherever its original denominator is regular.
-/
lemma continuousAt_prefactor {r c d e f q : ℂ} (hr0 : r ≠ 0) (n : ℕ)
    (hden : qPochhammerList [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f] q n ≠ 0) :
    ContinuousAt (fun s => qProductRatio n [s ^ 2 * q, q / s ^ 2,
      s ^ 2 * q / (c * d), s ^ 2 * q / (e * f)]
      [q / c, q / d, s ^ 2 * q / e, s ^ 2 * q / f] q) r := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  let upper : List (ℂ → ℂ) := [fun s => s ^ 2 * q, fun s => q / s ^ 2,
    fun s => s ^ 2 * q / (c * d), fun s => s ^ 2 * q / (e * f)]
  let lower : List (ℂ → ℂ) := [fun _ => q / c, fun _ => q / d,
    fun s => s ^ 2 * q / e, fun s => s ^ 2 * q / f]
  have hU : ∀ g ∈ upper, ContinuousAt g r := by
    intro g hg
    simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> fun_prop
  have hL : ∀ g ∈ lower, ContinuousAt g r := by
    intro g hg
    simp only [lower, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> fun_prop
  have H := (FiniteBilateral.continuousAt_qPochhammerList hU q n).div₀
    (FiniteBilateral.continuousAt_qPochhammerList hL q n) hden
  simpa only [qProductRatio, upper, lower, List.map_cons, List.map_nil] using H

/-- Continuity removes every shifted-product exclusion from the finite bilateral Watson
transformation, retaining precisely the original bilateral and prefactor regularity. -/
lemma eightSeries_eq_fourSeries {r c d e f q : ℂ} (hr0 : r ≠ 0)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ)
    (hden : QDenominatorRegular [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f] q)
    (hB : FiniteBilateral.RegularThrough [q ^ (-(n : ℤ)), q * r, -q * r, c, d, e, f, r ^ 2 / q ^ n]
      [q ^ (n + 1), r, -r, r ^ 2 * q / c, r ^ 2 * q / d, r ^ 2 * q / e,
        r ^ 2 * q / f, r ^ 2 * q * q ^ n] q n ∧
      FiniteBilateral.RegularThrough [q ^ (-(n : ℤ)), e, f, r ^ 2 * q * q ^ n / (c * d)]
        [q ^ (n + 1), r ^ 2 * q / c, r ^ 2 * q / d, e * f / (r ^ 2 * q ^ n)] q n) :
    eightSeries (r ^ 2) r c d e f q n =
      qProductRatio n [r ^ 2 * q, q / r ^ 2, r ^ 2 * q / (c * d), r ^ 2 * q / (e * f)]
        [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f] q * fourSeries (r ^ 2) c d e f q n := by
  have hfixed : ∀ x ∈ [c, d, e, f, q ^ (-(n : ℤ))],
      qPochhammer (x / q ^ n) q n ≠ 0 := by
    intro x hx
    exact hB.1.2 x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  have hfixedDen : ∀ x ∈ [q / c, q / d], qPochhammer x q n ≠ 0 := by
    intro x hx
    exact qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) n
  have hEq : ∀ᶠ s in 𝓝[≠] r, eightSeries (s ^ 2) s c d e f q n =
      qProductRatio n [s ^ 2 * q, q / s ^ 2, s ^ 2 * q / (c * d), s ^ 2 * q / (e * f)]
        [q / c, q / d, s ^ 2 * q / e, s ^ 2 * q / f] q * fourSeries (s ^ 2) c d e f q n := by
    filter_upwards [eventually_shifted_regular hc0 hd0 he0 hf0 hq0 n r hfixed hfixedDen]
      with s hs
    exact eightSeries_eq_fourSeries_of_shifted_regular rfl (pow_ne_zero 2 hs.1) hs.2.1
      hc0 hd0 he0 hf0 hq0 hq n hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2
  have hleft := continuousAt_eightSeries hr0 hc0 hd0 he0 hf0 hq0 hq n hB.1
  have hdp : qPochhammerList [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f] q n ≠ 0 := by
    have h1 := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden
      (by simp : q / c ∈ [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f]) n
    have h2 := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden
      (by simp : q / d ∈ [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f]) n
    have h3 := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden
      (by simp : r ^ 2 * q / e ∈ [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f]) n
    have h4 := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden
      (by simp : r ^ 2 * q / f ∈ [q / c, q / d, r ^ 2 * q / e, r ^ 2 * q / f]) n
    simpa only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using mul_ne_zero h1 (mul_ne_zero h2 (mul_ne_zero h3 h4))
  have hright := (continuousAt_prefactor hr0 n hdp).fun_mul
    (continuousAt_fourSeries hr0 hq0 hq n hB.2)
  exact tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' (hEq.mono fun _ h => h.symm))

end DLMF.QHypergeometric.BilateralWatson
