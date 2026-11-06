/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileySixShift

/-!
# Finite product cancellation in Bailey's six-psi-six sum

Reversing four finite shifted factorials evaluates the constant in the semi-finite
index shift. The cleared product identity retains vanishing numerator products, including
`(q/a;q)∞`, so it also covers the exceptional positive powers of the base.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- Reversing the four shifted products gives the geometric argument in the node shift. -/
lemma shifted_finite_products {a b c d q : ℂ} (hq0 : q ≠ 0) (ha : a ≠ 0)
    (hbcd : b * c * d ≠ 0) (m : ℕ) :
    qPochhammer (q / b) q m * qPochhammer (q / c) q m *
      qPochhammer (q / d) q m * qPochhammer (a / q ^ m) q m =
    qPochhammer (b / q ^ m) q m * qPochhammer (c / q ^ m) q m *
      qPochhammer (d / q ^ m) q m * shiftArgument a b c d q m ^ m *
        qPochhammer (q / a) q m := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have he : 2 * (m + 1).choose 2 = m * (m + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show m + 1 + 1 = m + 2 by omega, Nat.choose_succ_succ', Nat.choose_one_right]
      nlinarith
  have hpow : (q ^ (m + 1).choose 2) ^ 2 = (q ^ (m + 1)) ^ m := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    nlinarith
  have hf (u : ℂ) (hu : u ≠ 0) :
      qPochhammer (q / u) q m =
        qPochhammer (u / q ^ m) q m * q ^ (m + 1).choose 2 / (-u) ^ m := by
    apply (eq_div_iff (pow_ne_zero m (neg_ne_zero.mpr hu))).mpr
    simpa only [mul_comm] using (TripleProduct.qPochhammer_shift_down hq0 hu m).symm
  have hScalar : (q ^ (m + 1).choose 2) ^ 2 * (-a) ^ m /
      ((-b) ^ m * (-c) ^ m * (-d) ^ m) = shiftArgument a b c d q m ^ m := by
    calc
      _ = (q ^ (m + 1).choose 2) ^ 2 * ((-a) / ((-b) * (-c) * (-d))) ^ m := by
        rw [div_pow, mul_pow, mul_pow]
        ring
      _ = (q ^ (m + 1)) ^ m * (a / (b * c * d)) ^ m := by
        rw [hpow]
        congr 2
        ring
      _ = _ := by
        rw [← mul_pow]
        congr 1
        unfold shiftArgument
        ring
  rw [hf b hb, hf c hc, hf d hd]
  have hA := TripleProduct.qPochhammer_shift_down hq0 ha m
  have hA' := (eq_div_iff (pow_ne_zero ((m + 1).choose 2) hq0)).mpr hA
  rw [hA']
  calc
    _ = qPochhammer (b / q ^ m) q m * qPochhammer (c / q ^ m) q m *
        qPochhammer (d / q ^ m) q m * qPochhammer (q / a) q m *
          ((q ^ (m + 1).choose 2) ^ 2 * (-a) ^ m /
            ((-b) ^ m * (-c) ^ m * (-d) ^ m)) := by
      field_simp
    _ = _ := by rw [hScalar]; ring

/-- The central finite factor joins the two adjacent halves without division. -/
lemma central_shifted_finite_products {a q : ℂ} (hq0 : q ≠ 0) (m : ℕ) :
    (1 - a / q ^ (2 * m)) * qPochhammer (a / q ^ (2 * m) * q) q (2 * m) =
      (1 - a) * qPochhammer (a / q ^ (2 * m)) q m *
        qPochhammer (a / q ^ m) q m := by
  have hfull : a / q ^ (2 * m) * q ^ (2 * m) = a := by field_simp
  have hhalf : a / q ^ (2 * m) * q ^ m = a / q ^ m := by
    rw [two_mul, pow_add]
    field_simp
  calc
    _ = qPochhammer (a / q ^ (2 * m)) q (2 * m + 1) :=
      (qPochhammer_succ' _ _ _).symm
    _ = _ := by
      rw [qPochhammer_succ, hfull, show 2 * m = m + m by omega,
        qPochhammer_add, ← two_mul m, hhalf]
      ring

/-- The product value of the shifted Rogers sum is the cleared Bailey product at its node.
Only finite denominator factors are cancelled; infinite numerator products may vanish. -/
lemma shiftFactor_mul_productSide {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hbcd : b * c * d ≠ 0)
    (hU : ∀ u ∈ [b, c, d], ∀ j : ℕ, u ≠ q ^ (j + 1))
    (m : ℕ) (hm : ∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1))
    (hz : ‖shiftArgument a b c d q m‖ < 1) :
    shiftFactor a b c d q m *
      SixPhiFiveCleared.productSide (b / q ^ m) (c / q ^ m) (d / q ^ m) q
        (a / q ^ (2 * m)) = productSide a b c d q (q ^ m / a) := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have hqm := pow_ne_zero m hq0
  have hB := BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq hb (hU b (by simp)) m
  have hC := BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq hc (hU c (by simp)) m
  have hD := BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq hd (hU d (by simp)) m
  have he : a / q ^ m / q ^ m = a / q ^ (2 * m) := by
    rw [two_mul, pow_add]
    field_simp
  have hA : qPochhammer (a / q ^ (2 * m)) q m ≠ 0 := by
    rw [← he]
    exact BaileyBilateral.qPochhammer_div_pow_ne_zero hq0 hq (div_ne_zero ha hqm) hm m
  have hZ : shiftArgument a b c d q m ≠ 0 :=
    div_ne_zero (mul_ne_zero ha (pow_ne_zero (m + 1) hq0)) hbcd
  have hIZ : qPochhammerInf (shiftArgument a b c d q m) q ≠ 0 := by
    apply qPochhammerInf_ne_zero hq
    intro j hj
    have H := norm_mul_pow_lt_one hz hq j
    rw [← sub_eq_zero.mp hj, norm_one] at H
    exact lt_irrefl _ H
  have hpair (u v : ℂ) : a / q ^ (2 * m) * q / ((u / q ^ m) * (v / q ^ m)) =
      a * q / (u * v) := by
    rw [two_mul, pow_add]
    field_simp
  have hnode (u : ℂ) : a * q * (q ^ m / a) / u = q ^ (m + 1) / u := by
    rw [pow_succ]
    field_simp
  have hsplit (u : ℂ) : qPochhammerInf (q / u) q =
      qPochhammer (q / u) q m * qPochhammerInf (q ^ (m + 1) / u) q := by
    rw [qPochhammerInf_mul_qPochhammer hq m,
      show q / u * q ^ m = q ^ (m + 1) / u by rw [pow_succ]; ring]
  have hcentral : (1 - a / q ^ (2 * m)) * qPochhammerInf (a / q ^ (2 * m) * q) q =
      (1 - a) * qPochhammer (a / q ^ (2 * m)) q m *
        qPochhammer (a / q ^ m) q m * qPochhammerInf (a * q) q := by
    rw [qPochhammerInf_mul_qPochhammer hq (2 * m)]
    have he : a / q ^ (2 * m) * q * q ^ (2 * m) = a * q := by field_simp
    rw [he]
    linear_combination qPochhammerInf (a * q) q * central_shifted_finite_products hq0 m
  have hfinite := shifted_finite_products hq0 ha hbcd m
  simp only [div_mul_eq_mul_div] at hcentral
  field_simp [pow_ne_zero (2 * m) hq0] at hcentral
  unfold shiftFactor SixPhiFiveCleared.productSide productSide
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [shifted_argument hq0 hbcd m, hpair b c, hpair b d, hpair c d,
    hnode b, hnode c, hnode d]
  rw [hsplit b, hsplit c, hsplit d, hsplit a]
  field_simp [hIZ, hB, hC, hD, hA, pow_ne_zero m hZ, sub_ne_zero.mpr ha1.symm]
  linear_combination (norm := ring_nf)
    (qPochhammerInf q q * qPochhammer (q / b) q m * qPochhammer (q / c) q m *
      qPochhammer (q / d) q m * qPochhammerInf (q ^ (m + 1) / b) q *
      qPochhammerInf (q ^ (m + 1) / c) q * qPochhammerInf (q ^ (m + 1) / d) q *
      qPochhammerInf (q ^ (m + 1) / a) q * qPochhammerInf (a * q / (b * c)) q *
      qPochhammerInf (a * q / (b * d)) q * qPochhammerInf (a * q / (c * d)) q) * hcentral +
    (q ^ (2 * m) * (1 - a) * qPochhammer (a / q ^ (2 * m)) q m *
      qPochhammerInf (a * q) q *
      qPochhammerInf q q * qPochhammerInf (q ^ (m + 1) / b) q *
      qPochhammerInf (q ^ (m + 1) / c) q * qPochhammerInf (q ^ (m + 1) / d) q *
      qPochhammerInf (q ^ (m + 1) / a) q * qPochhammerInf (a * q / (b * c)) q *
      qPochhammerInf (a * q / (b * d)) q * qPochhammerInf (a * q / (c * d)) q) * hfinite

end DLMF.QHypergeometric.BaileySixSummation
