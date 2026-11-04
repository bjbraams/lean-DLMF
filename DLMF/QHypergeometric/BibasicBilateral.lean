/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic
public import DLMF.QSeries.Basic

/-!
# Telescoping steps for the bilateral bibasic sum (DLMF 17.7.22)

Gasper's bilateral bibasic sum 17.7.22 is a telescoping sum: with `C` the constant factor of its
right side, `F(n)` the product of shifted factorials at the upper end and `G(m)` the one at the
lower end, every summand `t_k` is `C (T(k) - T(k-1))`, where `T(k) = F(k)` for `k ≥ 0` and
`T(k) = G(-k-1)` for `k < 0`. This file proves these identities, term by term; the sum itself is
`bibasic_bilateral_finite` in `DLMF.QHypergeometric.HigherSummations`.

## Main definitions

* `BibasicBilateral.summand`, `BibasicBilateral.scale`, `BibasicBilateral.upperValue`,
  `BibasicBilateral.lowerValue`: the summand `t_k`, the constant `C` and the products `F`, `G`.

## Main results

* `BibasicBilateral.summand_zero`, `BibasicBilateral.summand_natCast_succ`: the terms `k ≥ 0`.
* `BibasicBilateral.summand_negSucc`, `BibasicBilateral.summand_negSucc_of_eq_zero`: the terms
  `k < 0`, for `a ≠ 0` and for `a = 0` (where the quotients of DLMF degenerate in Lean's
  convention `x / 0 = 0` and the identity still holds).
-/

@[expose] public noncomputable section

open Complex Finset DLMF.QSeries

namespace DLMF.QHypergeometric.BibasicBilateral

/-- The summand of the bilateral bibasic sum (DLMF 17.7.22). -/
def summand (a b c d p q : ℂ) (k : ℤ) : ℂ :=
  (1-a*d*p^k*q^k)*(1-b*p^k/(d*q^k))/((1-a*d)*(1-b/d))*
      qPochhammerListInt [a,b] p k*qPochhammerListInt [c,a*d^2/(b*c)] q k/
        (qPochhammerListInt [d*q,a*d*q/b] q k*qPochhammerListInt [a*d*p/c,b*c*p/d] p k)*q^k

/-- The constant factor on the right side of DLMF 17.7.22. -/
def scale (a b c d : ℂ) : ℂ :=
  (1-a)*(1-b)*(1-c)*(1-a*d^2/(b*c))/(d*(1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)))

/-- The upper partial product `F(n)` of the telescoping form of DLMF 17.7.22. -/
def upperValue (a b c d p q : ℂ) (n : ℕ) : ℂ :=
  qPochhammerList [a*p,b*p] p n*qPochhammerList [c*q,a*d^2*q/(b*c)] q n/
        (qPochhammerList [d*q,a*d*q/b] q n*qPochhammerList [a*d*p/c,b*c*p/d] p n)

/-- The lower partial product `G(m)` of the telescoping form of DLMF 17.7.22. -/
def lowerValue (a b c d p q : ℂ) (m : ℕ) : ℂ :=
  qPochhammerList [c/(a*d),d/(b*c)] p (m+1)*qPochhammerList [1/d,b/(a*d)] q (m+1)/
        (qPochhammerList [1/c,b*c/(a*d^2)] q (m+1)*qPochhammerList [1/a,1/b] p (m+1))

/-- `(x;r)_0 = 1` at the integer index `0`. -/
private lemma qPochhammerInt_zero (x r : ℂ) : qPochhammerInt x r 0 = 1 := rfl

/-- Positive telescoping step: `t_{k+1} = C (F(k+1) - F(k))`. -/
theorem summand_natCast_succ {a b c d p q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hq : q ≠ 0) (k : ℕ)
    (hP : (1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)) ≠ 0)
    (hF : qPochhammerList [d*q,a*d*q/b] q (k+1)*qPochhammerList [a*d*p/c,b*c*p/d] p (k+1) ≠ 0) :
    summand a b c d p q ((k+1 : ℕ) : ℤ) =
      scale a b c d * (upperValue a b c d p q (k+1) - upperValue a b c d p q k) := by
  simp only [summand, scale, upperValue, qPochhammerListInt, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, qPochhammerInt_natCast,
    zpow_natCast] at hF hP ⊢
  rw [qPochhammer_succ' a, qPochhammer_succ' b, qPochhammer_succ' c,
    qPochhammer_succ' (a*d^2/(b*c))]
  simp only [qPochhammer_succ _ _ k] at hF ⊢
  simp only [ne_eq, mul_eq_zero, not_or] at hF hP
  obtain ⟨⟨⟨X1, D1⟩, ⟨X2, D2⟩⟩, ⟨⟨X3, D3⟩, ⟨X4, D4⟩⟩⟩ := hF
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hP
  rw [show a*d^2/(b*c)*q = a*d^2*q/(b*c) by ring]
  generalize qPochhammer (a*p) p k = y1 at *
  generalize qPochhammer (b*p) p k = y2 at *
  generalize qPochhammer (c*q) q k = y3 at *
  generalize qPochhammer (a*d^2*q/(b*c)) q k = y4 at *
  generalize qPochhammer (d*q) q k = x1 at *
  generalize qPochhammer (a*d*q/b) q k = x2 at *
  generalize qPochhammer (a*d*p/c) p k = x3 at *
  generalize qPochhammer (b*c*p/d) p k = x4 at *
  rw [show p^(k+1) = p*p^k by ring, show q^(k+1) = q*q^k by ring]
  have hQ0 : q^k ≠ 0 := pow_ne_zero _ hq
  generalize p^k = P at *
  generalize q^k = Q at *
  have K1 : d - b ≠ 0 := fun h => h2 (by field_simp; linear_combination h)
  have K2 : d - c ≠ 0 := fun h => h3 (by field_simp; linear_combination h)
  have K3 : b*c - a*d ≠ 0 := fun h => h4 (by field_simp; linear_combination h)
  have F2 : b - a*d*q*Q ≠ 0 := fun h => D2 (by field_simp; linear_combination h)
  have F3 : c - a*d*p*P ≠ 0 := fun h => D3 (by field_simp; linear_combination h)
  have F4 : d - p*P*b*c ≠ 0 := fun h => D4 (by field_simp; linear_combination h)
  field_simp
  ring

/-- The term `k = 0`: `t_0 = C (F(0) - G(0))`. -/
theorem summand_zero {a b c d p q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hP : (1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)) ≠ 0)
    (hR : qPochhammerList [1/c,b*c/(a*d^2)] q 1*qPochhammerList [1/a,1/b] p 1 ≠ 0) :
    summand a b c d p q 0 =
      scale a b c d * (upperValue a b c d p q 0 - lowerValue a b c d p q 0) := by
  simp only [summand, scale, upperValue, lowerValue, qPochhammerListInt, qPochhammerList,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, zero_add,
    qPochhammer_one, zpow_zero, qPochhammerInt_zero, qPochhammer_zero] at hR hP ⊢
  simp only [ne_eq, mul_eq_zero, not_or] at hR hP
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hP
  obtain ⟨⟨E3, E4⟩, ⟨E1, E2⟩⟩ := hR
  have K1 : d - b ≠ 0 := fun h => h2 (by field_simp; linear_combination h)
  have K2 : d - c ≠ 0 := fun h => h3 (by field_simp; linear_combination h)
  have K3 : b*c - a*d ≠ 0 := fun h => h4 (by field_simp; linear_combination h)
  have F3 : c - 1 ≠ 0 := fun h => E3 (by field_simp; linear_combination h)
  have F2 : b - 1 ≠ 0 := fun h => E2 (by field_simp; linear_combination h)
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, zero_div, div_zero, sub_zero, mul_one, one_mul] at *
    field_simp
    ring
  · have F1 : a - 1 ≠ 0 := fun h => E1 (by field_simp; linear_combination h)
    have F4 : a*d^2 - b*c ≠ 0 := fun h => E4 (by field_simp; linear_combination h)
    field_simp
    ring

/-- `(x;r)_{-(j+1)}` through the negative shift DLMF 17.2.E11. -/
private lemma qPochhammerInt_negSucc_eq {x r : ℂ} (hx : x ≠ 0) (hr : r ≠ 0) (j : ℕ) :
    qPochhammerInt x r (Int.negSucc j) =
      (qPochhammer (r/x) r (j+1) * (-x/r)^(j+1) * r^(-((j+1).choose 2:ℤ)))⁻¹ := by
  rw [qPochhammerInt_negSucc, ← qPochhammer_shift_negative hx hr]
  push_cast; rfl

/-- Negative telescoping step `t_{-(j+1)} = C (G(j) - G(j+1))` for `a ≠ 0`. -/
theorem summand_negSucc {a b c d p q : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (j : ℕ)
    (hP : (1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)) ≠ 0)
    (hF : qPochhammerListInt [a,b] p (Int.negSucc j) * qPochhammerListInt [c,a*d^2/(b*c)] q
        (Int.negSucc j) * qPochhammerListInt [d*q,a*d*q/b] q (Int.negSucc j) *
        qPochhammerListInt [a*d*p/c,b*c*p/d] p (Int.negSucc j) ≠ 0)
    (hR : qPochhammerList [1/c,b*c/(a*d^2)] q (j+2)*qPochhammerList [1/a,1/b] p (j+2)≠0) :
    summand a b c d p q (Int.negSucc j) =
      scale a b c d * (lowerValue a b c d p q j - lowerValue a b c d p q (j+1)) := by
  simp only [summand, scale, lowerValue, qPochhammerListInt, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hF hR ⊢
  have e1 : a*d^2/(b*c) ≠ 0 := by simp [ha, hb, hc, hd]
  have e2 : d*q ≠ 0 := mul_ne_zero hd hq
  have e3 : a*d*q/b ≠ 0 := by simp [ha, hb, hq, hd]
  have e4 : a*d*p/c ≠ 0 := by simp [ha, hc, hp, hd]
  have e5 : b*c*p/d ≠ 0 := by simp [hb, hc, hp, hd]
  rw [qPochhammerInt_negSucc_eq ha hp, qPochhammerInt_negSucc_eq hb hp,
    qPochhammerInt_negSucc_eq hc hq, qPochhammerInt_negSucc_eq e1 hq,
    qPochhammerInt_negSucc_eq e2 hq, qPochhammerInt_negSucc_eq e3 hq,
    qPochhammerInt_negSucc_eq e4 hp, qPochhammerInt_negSucc_eq e5 hp] at hF ⊢
  rw [show q/(d*q) = 1/d by field_simp, show q/(a*d*q/b) = b/(a*d) by field_simp,
    show p/(a*d*p/c) = c/(a*d) by field_simp, show p/(b*c*p/d) = d/(b*c) by field_simp,
    show q/(a*d^2/(b*c)) = b*c/(a*d^2)*q by field_simp, show p/a = 1/a*p by ring,
    show p/b = 1/b*p by ring, show q/c = 1/c*q by ring] at hF ⊢
  simp only [show j+1+1 = j+2 by ring] at *
  have hR2 := hR
  rw [show j+2 = (j+1)+1 by ring] at hR2
  simp only [qPochhammer_succ' _ _ (j+1)] at hR2
  rw [show j+2 = (j+1)+1 by ring] at hR ⊢
  simp only [qPochhammer_succ _ _ (j+1), zpow_negSucc, zpow_neg, zpow_natCast] at hR ⊢
  simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or] at hF hR hR2
  obtain ⟨⟨⟨⟨⟨⟨Y1, -⟩, -⟩, ⟨⟨Y2, -⟩, -⟩⟩, ⟨⟨⟨Y3, -⟩, -⟩, ⟨⟨Y4, -⟩, -⟩⟩⟩,
    ⟨⟨⟨X1, -⟩, -⟩, ⟨⟨X2, -⟩, -⟩⟩⟩, ⟨⟨⟨X3, -⟩, -⟩, ⟨⟨X4, -⟩, -⟩⟩⟩ := hF
  obtain ⟨⟨⟨Z3, D3⟩, ⟨Z4, D4⟩⟩, ⟨⟨Z1, D1⟩, ⟨Z2, D2⟩⟩⟩ := hR
  obtain ⟨⟨⟨E3, -⟩, ⟨E4, -⟩⟩, ⟨⟨E1, -⟩, ⟨E2, -⟩⟩⟩ := hR2
  have s1 := qPochhammer_succ' (1/a) p (j+1)
  have s2 := qPochhammer_succ' (1/b) p (j+1)
  have s3 := qPochhammer_succ' (1/c) q (j+1)
  have s4 := qPochhammer_succ' (b*c/(a*d^2)) q (j+1)
  rw [qPochhammer_succ _ _ (j+1)] at s1 s2 s3 s4
  rw [eq_div_of_mul_eq E1 ((mul_comm _ _).trans s1.symm),
    eq_div_of_mul_eq E2 ((mul_comm _ _).trans s2.symm),
    eq_div_of_mul_eq E3 ((mul_comm _ _).trans s3.symm),
    eq_div_of_mul_eq E4 ((mul_comm _ _).trans s4.symm)]
  generalize qPochhammer (1/a) p (j+1) = z1 at *
  generalize qPochhammer (1/b) p (j+1) = z2 at *
  generalize qPochhammer (1/c) q (j+1) = z3 at *
  generalize qPochhammer (b*c/(a*d^2)) q (j+1) = z4 at *
  generalize qPochhammer (1/d) q (j+1) = x1 at *
  generalize qPochhammer (b/(a*d)) q (j+1) = x2 at *
  generalize qPochhammer (c/(a*d)) p (j+1) = x3 at *
  generalize qPochhammer (d/(b*c)) p (j+1) = x4 at *
  rw [show -(d*q)/q = -d by field_simp, show -(a*d*q/b)/q = -(a*d/b) by field_simp,
    show -(a*d*p/c)/p = -(a*d/c) by field_simp, show -(b*c*p/d)/p = -(b*c/d) by field_simp,
    div_pow (-a), div_pow (-b), div_pow (-c), div_pow (-(a*d^2/(b*c)))]
  have hCp : p^((j+1).choose 2) ≠ 0 := pow_ne_zero _ hp
  have hCq : q^((j+1).choose 2) ≠ 0 := pow_ne_zero _ hq
  have hP0 : p^(j+1) ≠ 0 := pow_ne_zero _ hp
  have hQ0 : q^(j+1) ≠ 0 := pow_ne_zero _ hq
  generalize p^(j+1) = P at *
  generalize q^(j+1) = Q at *
  generalize p^((j+1).choose 2) = Cp at *
  generalize q^((j+1).choose 2) = Cq at *
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (by simpa [not_or] using hP :
    ((1 - a*d ≠ 0 ∧ 1 - b/d ≠ 0) ∧ 1 - c/d ≠ 0) ∧ 1 - a*d/(b*c) ≠ 0)
  generalize j+1 = n at *
  have F1 : a - P ≠ 0 := fun h => D1 (by rw [show P = a by linear_combination -h]; field_simp; simp)
  have F2 : b - P ≠ 0 := fun h => D2 (by rw [show P = b by linear_combination -h]; field_simp; simp)
  have F3 : c - Q ≠ 0 := fun h => D3 (by rw [show Q = c by linear_combination -h]; field_simp; simp)
  have F4 : a*d^2 - Q*b*c ≠ 0 := fun h => D4 (by field_simp; linear_combination h)
  have hpow : (-d)^n*(-(a*d/b))^n*(-(a*d/c))^n*(-(b*c/d))^n =
      (-a)^n*(-b)^n*(-c)^n*(-(a*d^2/(b*c)))^n := by
    simp only [← mul_pow]; congr 1; field_simp
  have hA : (-a)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr ha)
  have hB : (-b)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hb)
  have hC : (-c)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hc)
  have G1 : (-d)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hd)
  have G2 : (-(a*d/b))^n ≠ 0 := pow_ne_zero _ (by simp [ha, hb, hd])
  have G3 : (-(a*d/c))^n ≠ 0 := pow_ne_zero _ (by simp [ha, hc, hd])
  have G4 : (-(b*c/d))^n ≠ 0 := pow_ne_zero _ (by simp [hb, hc, hd])
  have K1 : d - b ≠ 0 := fun h => h2 (by field_simp; linear_combination h)
  have K2 : d - c ≠ 0 := fun h => h3 (by field_simp; linear_combination h)
  have K3 : b*c - a*d ≠ 0 := fun h => h4 (by field_simp; linear_combination h)
  generalize (-a)^n = A at *
  generalize (-b)^n = B at *
  generalize (-c)^n = C at *
  generalize (-(a*d^2/(b*c)))^n = W at *
  generalize (-d)^n = W1 at *
  generalize (-(a*d/b))^n = W2 at *
  generalize (-(a*d/c))^n = W3 at *
  generalize (-(b*c/d))^n = W4 at *
  have hW : W = W1*W2*W3*W4/(A*B*C) := by field_simp; linear_combination -hpow
  subst hW
  field_simp
  ring

/-- Negative telescoping step `t_{-(j+1)} = C (G(j) - G(j+1))` at `a = 0`. -/
theorem summand_negSucc_of_eq_zero {b c d p q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (j : ℕ)
    (hP : (1-0*d)*(1-b/d)*(1-c/d)*(1-0*d/(b*c)) ≠ 0)
    (hF : qPochhammerListInt [0,b] p (Int.negSucc j) * qPochhammerListInt [c,0*d^2/(b*c)] q
        (Int.negSucc j) * qPochhammerListInt [d*q,0*d*q/b] q (Int.negSucc j) *
        qPochhammerListInt [0*d*p/c,b*c*p/d] p (Int.negSucc j) ≠ 0)
    (hR : qPochhammerList [1/c,b*c/(0*d^2)] q (j+2)*qPochhammerList [1/0,1/b] p (j+2)≠0) :
    summand 0 b c d p q (Int.negSucc j) =
      scale 0 b c d * (lowerValue 0 b c d p q j - lowerValue 0 b c d p q (j+1)) := by
  simp only [summand, scale, lowerValue, qPochhammerListInt, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, zero_mul, zero_div, div_zero,
    sub_zero, one_mul, qPochhammer_zero_param, qPochhammerInt_negSucc,
    inv_one] at hF hR hP ⊢
  have e2 : d*q ≠ 0 := mul_ne_zero hd hq
  have e5 : b*c*p/d ≠ 0 := by simp [hb, hc, hp, hd]
  rw [← qPochhammerInt_negSucc, ← qPochhammerInt_negSucc, ← qPochhammerInt_negSucc,
    ← qPochhammerInt_negSucc] at hF ⊢
  rw [qPochhammerInt_negSucc_eq hb hp,
    qPochhammerInt_negSucc_eq hc hq,
    qPochhammerInt_negSucc_eq e2 hq,
    qPochhammerInt_negSucc_eq e5 hp] at hF ⊢
  rw [show q/(d*q) = 1/d by field_simp,
    show p/(b*c*p/d) = d/(b*c) by field_simp,
    show p/b = 1/b*p by ring, show q/c = 1/c*q by ring] at hF ⊢
  have hR2 := hR
  rw [show j+2 = (j+1)+1 by ring] at hR2
  simp only [qPochhammer_succ' _ _ (j+1)] at hR2
  rw [show j+2 = (j+1)+1 by ring] at hR ⊢
  simp only [qPochhammer_succ _ _ (j+1), zpow_negSucc, zpow_neg, zpow_natCast] at hR ⊢
  simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or] at hF hR hR2
  obtain ⟨⟨⟨⟨⟨Y2, -⟩, -⟩, ⟨⟨Y3, -⟩, -⟩⟩, ⟨⟨X1, -⟩, -⟩⟩, ⟨⟨X4, -⟩, -⟩⟩ := hF
  obtain ⟨⟨Z3, D3⟩, ⟨Z2, D2⟩⟩ := hR
  obtain ⟨⟨E3, -⟩, ⟨E2, -⟩⟩ := hR2
  have s2 := qPochhammer_succ' (1/b) p (j+1)
  have s3 := qPochhammer_succ' (1/c) q (j+1)
  rw [qPochhammer_succ _ _ (j+1)] at s2 s3
  rw [eq_div_of_mul_eq E2 ((mul_comm _ _).trans s2.symm),
    eq_div_of_mul_eq E3 ((mul_comm _ _).trans s3.symm)]
  generalize qPochhammer (1/b) p (j+1) = z2 at *
  generalize qPochhammer (1/c) q (j+1) = z3 at *
  generalize qPochhammer (1/d) q (j+1) = x1 at *
  generalize qPochhammer (d/(b*c)) p (j+1) = x4 at *
  rw [show -(d*q)/q = -d by field_simp, show -(b*c*p/d)/p = -(b*c/d) by field_simp,
    div_pow (-b), div_pow (-c)]
  have hCp : p^((j+1).choose 2) ≠ 0 := pow_ne_zero _ hp
  have hCq : q^((j+1).choose 2) ≠ 0 := pow_ne_zero _ hq
  have hP0 : p^(j+1) ≠ 0 := pow_ne_zero _ hp
  have hQ0 : q^(j+1) ≠ 0 := pow_ne_zero _ hq
  generalize p^(j+1) = P at *
  generalize q^(j+1) = Q at *
  generalize p^((j+1).choose 2) = Cp at *
  generalize q^((j+1).choose 2) = Cq at *
  obtain ⟨h2, h3⟩ := (by simpa [not_or] using hP : 1 - b/d ≠ 0 ∧ 1 - c/d ≠ 0)
  generalize j+1 = n at *
  have F2 : b - P ≠ 0 := fun h => D2 (by rw [show P = b by linear_combination -h]; field_simp; simp)
  have F3 : c - Q ≠ 0 := fun h => D3 (by rw [show Q = c by linear_combination -h]; field_simp; simp)
  have hpow : (-d)^n*(-(b*c/d))^n = (-b)^n*(-c)^n := by
    simp only [← mul_pow]; congr 1; field_simp
  have hB : (-b)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hb)
  have hC : (-c)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hc)
  have G1 : (-d)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hd)
  have G4 : (-(b*c/d))^n ≠ 0 := pow_ne_zero _ (by simp [hb, hc, hd])
  have K1 : d - b ≠ 0 := fun h => h2 (by field_simp; linear_combination h)
  have K2 : d - c ≠ 0 := fun h => h3 (by field_simp; linear_combination h)
  generalize (-b)^n = B at *
  generalize (-c)^n = C at *
  generalize (-d)^n = W1 at *
  generalize (-(b*c/d))^n = W4 at *
  have hW : W4 = B*C/W1 := by field_simp; linear_combination hpow
  subst hW
  field_simp
  ring

end DLMF.QHypergeometric.BibasicBilateral
