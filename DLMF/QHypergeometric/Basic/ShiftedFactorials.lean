/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.Series
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Identities for `q`-shifted factorials (DLMF §17.2(i)–(iii))

This file proves the identities for `q`-shifted factorials of DLMF §17.2: the generalized and
negative-index factorials, base inversion, reversal, index shifts, multiple and root
products, and the parameter limits.

## Main results

* `qPochhammer_order_hasProd`, `qPochhammer_negative`: the generalized and negative-index
  shifted factorials (DLMF 17.2.2–17.2.3).
* `qPochhammer_invert_base`, `qPochhammer_reverse`, `qPochhammer_shift_negative`,
  `qPochhammer_sub_index`, `qPochhammer_shift_positive`: DLMF 17.2.7–17.2.18, with their ratio
  forms.
* `qPochhammer_even`, `qPochhammer_blocks`, `qPochhammer_squared`, `qPochhammer_vwp_ratio`,
  `qPochhammer_root_ratio`: DLMF 17.2.19–17.2.23.
* `qPochhammer_parameter_limit`, `qPochhammer_parameter_ratio_limit`,
  `qPochhammer_double_parameter_limit`: DLMF 17.2.24–17.2.26.

## Implementation notes

The identities state their nonvanishing hypotheses explicitly, since division is totalized.
The convergence and analyticity of the general series are in
`DLMF.QHypergeometric.Convergence`.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set
open scoped Real Topology
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- Integer shifted-factorial products agree with finite products at nonnegative indices. -/
theorem qPochhammerListInt_natCast (a : List ℂ) (q : ℂ) (n : ℕ) :
    qPochhammerListInt a q n=qPochhammerList a q n := by
  simp [qPochhammerListInt,qPochhammerList]

/-- The product formula for the generalized q-shifted factorial `(a;q)_ν` as the convergent infinite
product of `(1-a q^j)/(1-a q^(ν+j))` (DLMF 17.2.E3). -/
@[dlmf 17.2.E3]
theorem qPochhammer_order_hasProd {a q ν : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hd : ∀ j : ℕ, 1-a*q^(ν+j)≠0) :
    HasProd (fun j : ℕ => (1-a*q^j)/(1-a*q^(ν+j))) (qPochhammerOrder a q ν) := by
  have hp (w : ℂ) : HasProd (fun j : ℕ => 1-w*q^j) (qPochhammerInf w q) := by
    simpa only [qPochhammerInf] using (multipliable_one_sub_mul_pow (w := w) hq).hasProd
  have hd' : ∀ j : ℕ, 1-(a*q^ν)*q^j≠0 := by
    intro j
    simpa [cpow_add _ _ hq0,mul_assoc] using hd j
  have h := (hp a).div₀ (hp (a*q^ν)) (qPochhammerInf_ne_zero hq hd')
  convert h using 1
  · ext j
    simp [cpow_add _ _ hq0,mul_assoc]
  · rfl

/-- For natural `n`, the generalized q-shifted factorial `(a;q)_n` defined via infinite products
agrees with the finite q-Pochhammer symbol. -/
theorem qPochhammer_order_nat {a q : ℂ} (hq : ‖q‖<1) (n : ℕ)
    (hd : qPochhammerInf (a*q^n) q≠0) : qPochhammerOrder a q n=qPochhammer a q n := by
  unfold qPochhammerOrder
  rw [cpow_natCast]
  apply (div_eq_iff hd).2
  exact qPochhammerInf_mul_qPochhammer hq n

/-- Inverting the base: `(a;q⁻¹)_n = (a⁻¹;q)_n (-a)^n q^(-n(n-1)/2)` (DLMF 17.2.E7). -/
@[dlmf 17.2.E7]
theorem qPochhammer_invert_base {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) :
    qPochhammer a q⁻¹ n=qPochhammer a⁻¹ q n*(-a)^n*q^(-(n.choose 2:ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n+1).choose 2=n.choose 2+n := by
      simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
    rw [qPochhammer_succ,qPochhammer_succ,ih,hc]
    simp only [Nat.cast_add,neg_add,zpow_add₀ hq,zpow_neg,zpow_natCast,pow_succ,inv_pow]
    field_simp
    ring

/-- Ratio form of base inversion: `(a;q⁻¹)_n/(b;q⁻¹)_n = (a⁻¹;q)_n/(b⁻¹;q)_n (a/b)^n` (DLMF
17.2.E8). -/
@[dlmf 17.2.E8]
theorem qPochhammer_invert_base_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) :
    qPochhammer a q⁻¹ n/qPochhammer b q⁻¹ n=qPochhammer a⁻¹ q n/qPochhammer b⁻¹ q n*(a/b)^n := by
  rw [qPochhammer_invert_base ha hq,qPochhammer_invert_base hb hq]
  rw [mul_div_mul_right _ _ (zpow_ne_zero _ hq),mul_div_mul_comm]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- Reversal of a q-shifted factorial: `(a;q)_n = (q^(1-n)/a;q)_n (-a)^n q^(n(n-1)/2)` (DLMF
17.2.E9). -/
@[dlmf 17.2.E9]
theorem qPochhammer_reverse {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) :
    qPochhammer a q n=qPochhammer (q^(1-(n:ℤ))/a) q n*(-a)^n*q^(n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n+1).choose 2=n.choose 2+n := by
      simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
    have harg : (q^(1-((n+1:ℕ):ℤ))/a)*q=q^(1-(n:ℤ))/a := by
      rw [show 1-((n+1:ℕ):ℤ)= -(n:ℤ) by omega]
      simp only [zpow_neg,zpow_natCast,zpow_sub₀ hq,zpow_one]
      field_simp
    rw [qPochhammer_succ,ih,qPochhammer_succ',harg,hc,pow_add,pow_succ]
    rw [show 1-((n+1:ℕ):ℤ)= -(n:ℤ) by omega]
    simp only [zpow_neg,zpow_natCast]
    field_simp
    ring

/-- Ratio form of reversal: `(a;q)_n/(b;q)_n = (q^(1-n)/a;q)_n/(q^(1-n)/b;q)_n (a/b)^n` (DLMF
17.2.E10). -/
@[dlmf 17.2.E10]
theorem qPochhammer_reverse_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) :
    qPochhammer a q n/qPochhammer b q n=qPochhammer (q^(1-(n:ℤ))/a) q n/qPochhammer (q^(1-(n:ℤ))/b)
      q n*(a/b)^n := by
  rw [qPochhammer_reverse ha hq,qPochhammer_reverse hb hq]
  rw [mul_div_mul_right _ _ (pow_ne_zero _ hq),mul_div_mul_comm]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- Negative shift: `(a q^(-n);q)_n = (q/a;q)_n (-a/q)^n q^(-n(n-1)/2)` (DLMF 17.2.E11). -/
@[dlmf 17.2.E11]
theorem qPochhammer_shift_negative {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) :
    qPochhammer (a*q^(-(n:ℤ))) q n=qPochhammer (q/a) q n*(-a/q)^n*q^(-(n.choose 2:ℤ)) := by
  have h := DLMF.QSeries.TripleProduct.qPochhammer_shift_down hq ha n
  have hc : (n+1).choose 2=n.choose 2+n := by
    simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
  rw [hc,pow_add] at h
  simp only [zpow_neg,zpow_natCast,← div_eq_mul_inv,div_pow]
  field_simp
  linear_combination h

/-- The q-shifted factorial of negative index `-n`, as the inverse of `(a q^(-n);q)_n` and in the
closed form `(-q/a)^n q^(n(n-1)/2)/(q/a;q)_n` (DLMF 17.2.E2). -/
@[dlmf 17.2.E2]
theorem qPochhammer_negative {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ)
    (hd : qPochhammer (q/a) q n≠0) :
    qPochhammerInt a q (-(n:ℤ))=(qPochhammer (a*q^(-(n:ℤ))) q n)⁻¹ ∧
    qPochhammerInt a q (-(n:ℤ))=(-q/a)^n*q^(n.choose 2)/qPochhammer (q/a) q n := by
  have h0 : qPochhammerInt a q (-(n:ℤ))=
      (qPochhammer (a*q^(-(n:ℤ))) q n)⁻¹ := by
    cases n with
    | zero => simp [qPochhammerInt]
    | succ n => rfl
  refine ⟨h0,?_⟩
  rw [h0,qPochhammer_shift_negative ha hq]
  simp only [zpow_neg,zpow_natCast,div_pow]
  field_simp
  ring_nf
  simp [-inv_pow]
  rw [mul_assoc,← mul_pow,mul_inv_cancel₀ ha,one_pow,mul_one]

/-- Ratio form of the negative shift: `(a q^(-n);q)_n/(b q^(-n);q)_n = (q/a;q)_n/(q/b;q)_n (a/b)^n`
(DLMF 17.2.E12). -/
@[dlmf 17.2.E12]
theorem qPochhammer_shift_negative_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) :
    qPochhammer (a*q^(-(n:ℤ))) q n/qPochhammer (b*q^(-(n:ℤ))) q n=qPochhammer (q/a) q n/qPochhammer
      (q/b) q n*(a/b)^n := by
  rw [qPochhammer_shift_negative ha hq,qPochhammer_shift_negative hb hq]
  rw [mul_div_mul_right _ _ (zpow_ne_zero _ hq),mul_div_mul_comm]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- The reversal of a shifted block, used for 17.2.E13. -/
theorem qPochhammer_mul_pow_reverse {a q : ℂ} (ha : a≠0) (hq : q≠0) (m k : ℕ) :
    qPochhammer (a*q^m) q k=qPochhammer (q^(1-((m+k:ℕ):ℤ))/a) q k*(-(a*q^m))^k*q^(k.choose 2) := by
  have h := qPochhammer_reverse (mul_ne_zero ha (pow_ne_zero m hq)) hq k
  have he : q^(1-(k:ℤ))/(a*q^m)=q^(1-((m+k:ℕ):ℤ))/a := by
    rw [show (1-((m+k:ℕ):ℤ))=(1-(k:ℤ))-(m:ℤ) by push_cast; ring,zpow_sub₀ hq (1-(k:ℤ)) m,
      zpow_natCast,div_div,mul_comm a]
  rw [he] at h
  exact h

/-- `2·C(k,2)+k=k²`. -/
theorem choose_two_mul_two_add_self (k : ℕ) : (k.choose 2)*2+k=k*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ',Nat.choose_one_right]
    nlinarith

/-- Cancelling a natural power against an integer exponent difference. -/
private lemma qShiftBasic_zpow_natCast_sub_mul_pow {q : ℂ} (hq : q≠0) (c n : ℕ) :
    q^((c:ℤ)-(n:ℤ))*q^n=q^c := by
  rw [← zpow_natCast q n,← zpow_add₀ hq]
  simp

/-- The q-shifted factorial `(a;q)_(n-k)` expressed through `(a;q)_n` and `(q^(1-n)/a;q)_k` (DLMF
17.2.E13). -/
@[dlmf 17.2.E13]
theorem qPochhammer_sub_index {a q : ℂ} (ha : a≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n)
    (hd : qPochhammer (q^(1-(n:ℤ))/a) q k≠0) :
    qPochhammer a q (n-k)=qPochhammer a q n/qPochhammer (q^(1-(n:ℤ))/a) q k*(-q/a)^k*
      q^((k.choose 2:ℤ)-(n:ℤ)*k) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel,qPochhammer_add,qPochhammer_mul_pow_reverse ha hq m k]
  generalize qPochhammer (q^(1-((m+k:ℕ):ℤ))/a) q k = X at hd ⊢
  have hE := qShiftBasic_zpow_natCast_sub_mul_pow hq (k.choose 2) ((m+k)*k)
  rw [show (((m+k)*k:ℕ):ℤ)=((m+k:ℕ):ℤ)*(k:ℤ) by push_cast; ring] at hE
  generalize q^((k.choose 2:ℤ)-((m+k:ℕ):ℤ)*(k:ℤ)) = E at hE ⊢
  have hk2 := choose_two_mul_two_add_self k
  have hQ : q^(k.choose 2)*q^(k.choose 2)*q^k=q^(k*k) := by rw [← pow_add,← pow_add]; congr 1; omega
  have hAB : (-(a*q^m))^k*(-(q/a))^k=q^((m+1)*k) := by
    rw [← mul_pow,show (-(a*q^m))*(-(q/a))=q^(m+1) by field_simp; ring,← pow_mul]
  have hP : q^((m+k)*k)=q^((m+1)*k)*q^(k.choose 2)*q^(k.choose 2) := by
    rw [← pow_add,← pow_add]; congr 1; nlinarith
  have hC : q^(k.choose 2)≠0 := pow_ne_zero _ hq
  have h1 : E*q^((m+1)*k)*q^(k.choose 2)=1 := by
    rw [hP] at hE
    apply mul_right_cancel₀ hC
    linear_combination hE
  field_simp
  rw [show qPochhammer a q m*(-(a*q^m))^k*q^(k.choose 2)*(-(q/a))^k*E=
    qPochhammer a q m*(((-(a*q^m))^k*(-(q/a))^k)*E*q^(k.choose 2)) by ring,hAB,
    show q^((m+1)*k)*E*q^(k.choose 2)=E*q^((m+1)*k)*q^(k.choose 2) by ring,h1,mul_one]

/-- Ratio form of the index subtraction formula for `(a;q)_(n-k)/(b;q)_(n-k)` (DLMF 17.2.E14). -/
@[dlmf 17.2.E14]
theorem qPochhammer_sub_index_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) {k n : ℕ}
    (hk : k≤n) (hda : qPochhammer (q^(1-(n:ℤ))/a) q k≠0) (hdb : qPochhammer (q^(1-(n:ℤ))/b) q k≠0) :
    qPochhammer a q (n-k)/qPochhammer b q (n-k)=qPochhammer a q n/qPochhammer b q n*
      (qPochhammer (q^(1-(n:ℤ))/b) q k/qPochhammer (q^(1-(n:ℤ))/a) q k)*(b/a)^k := by
  rw [qPochhammer_sub_index ha hq hk hda,qPochhammer_sub_index hb hq hk hdb]
  by_cases hB : qPochhammer b q n=0
  · simp [hB]
  have hQ : q^((k.choose 2:ℤ)-(n:ℤ)*k)≠0 := zpow_ne_zero _ hq
  rw [show (b/a)^k=(-q/a)^k/(-q/b)^k by rw [← div_pow]; congr 1; field_simp]
  have h1 : (-q/b)^k≠0 := pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr hq) hb)
  field_simp

/-- The shifted factorial `(a q^(-n);q)_k` in terms of `(a;q)_k`, `(q/a;q)_n` and `(q^(1-k)/a;q)_n`
(DLMF 17.2.E15). -/
@[dlmf 17.2.E15]
theorem qPochhammer_shift_negative_general {a q : ℂ} (ha : a≠0) (hq : q≠0) (k n : ℕ)
    (hd : qPochhammer (q^(1-(k:ℤ))/a) q n≠0) :
    qPochhammer (a*q^(-(n:ℤ))) q k=qPochhammer a q k*qPochhammer (q/a) q n/qPochhammer
      (q^(1-(k:ℤ))/a) q n*q^(-(n:ℤ)*k) := by
  have h1 := qPochhammer_add (a*q^(-(n:ℤ))) q n k
  have h2 := qPochhammer_add (a*q^(-(n:ℤ))) q k n
  rw [Nat.add_comm k n] at h2
  have e1 : a*q^(-(n:ℤ))*q^n=a := by rw [zpow_neg,zpow_natCast]; field_simp
  have e2 : a*q^(-(n:ℤ))*q^k=(a*q^k)*q^(-(n:ℤ)) := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 := qPochhammer_shift_negative ha hq n
  have hak : a*q^k≠0 := mul_ne_zero ha (pow_ne_zero _ hq)
  have h4 := qPochhammer_shift_negative hak hq n
  have e3 : q/(a*q^k)=q^(1-(k:ℤ))/a := by
    rw [zpow_sub₀ hq,zpow_one,zpow_natCast]; field_simp
  rw [e3] at h4
  rw [h1,h3,h4] at h2
  rw [show -(n:ℤ)*k = -((n*k:ℕ):ℤ) by push_cast; ring]
  simp only [zpow_neg,zpow_natCast] at h2 ⊢
  generalize qPochhammer (q^(1-(k:ℤ))/a) q n = Y at hd h2 ⊢
  have hqn : q^(n.choose 2)≠0 := pow_ne_zero _ hq
  have hq1 : (-(a*q^k)/q)^n≠0 := pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr hak) hq)
  have hkey : (-a/q)^n=(-(a*q^k)/q)^n*(q^(n*k))⁻¹ := by
    rw [pow_mul',← inv_pow,← mul_pow]; congr 1; field_simp
  rw [hkey] at h2
  have hP : q^(n*k)≠0 := pow_ne_zero _ hq
  generalize (-(a*q^k)/q)^n = W at hq1 h2
  generalize q^(n*k) = P at hP h2 ⊢
  generalize q^(n.choose 2) = R at hqn h2
  generalize qPochhammer (a*q^(-(n:ℤ))) q k = Z at h2 ⊢
  field_simp at h2 ⊢
  linear_combination -h2

/-- The shifted factorial `(a q^(-n);q)_(n-k)` in terms of `(q/a;q)_n` and `(q/a;q)_k` (DLMF
17.2.E16). -/
@[dlmf 17.2.E16]
theorem qPochhammer_shift_negative_sub {a q : ℂ} (ha : a≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n)
    (hd : qPochhammer (q/a) q k≠0) :
    qPochhammer (a*q^(-(n:ℤ))) q (n-k)=qPochhammer (q/a) q n/qPochhammer (q/a) q k*(-a/q)^(n-k)*
      q^((k.choose 2:ℤ)-(n.choose 2:ℤ)) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel]
  have h1 := qPochhammer_add (a*q^(-((j+k:ℕ):ℤ))) q j k
  have e1 : a*q^(-((j+k:ℕ):ℤ))*q^j=a*q^(-(k:ℤ)) := by
    rw [mul_assoc,← zpow_natCast q j,← zpow_add₀ hq]; congr 2; push_cast; ring
  rw [e1,qPochhammer_shift_negative ha hq,qPochhammer_shift_negative ha hq] at h1
  rw [zpow_sub₀ hq]
  simp only [zpow_neg,zpow_natCast] at h1 ⊢
  have hw : (-a/q)≠0 := div_ne_zero (neg_ne_zero.mpr ha) hq
  rw [pow_add] at h1
  have hk1 : (-a/q)^k≠0 := pow_ne_zero _ hw
  have hk2 : q^(k.choose 2)≠0 := pow_ne_zero _ hq
  have hk3 : q^((j+k).choose 2)≠0 := pow_ne_zero _ hq
  generalize (-a/q)^k = W at hk1 h1
  generalize q^(k.choose 2) = R at hk2 h1 ⊢
  generalize q^((j+k).choose 2) = T at hk3 h1 ⊢
  generalize qPochhammer (a*(q^(j+k))⁻¹) q j = Z at h1 ⊢
  generalize qPochhammer (q/a) q k = Y at hd h1 ⊢
  field_simp at h1 ⊢
  linear_combination -h1

/-- Positive shift: `(a q^n;q)_k = (a;q)_k (a q^k;q)_n/(a;q)_n` (DLMF 17.2.E17). -/
@[dlmf 17.2.E17]
theorem qPochhammer_shift_positive {a q : ℂ} (k n : ℕ) (hd : qPochhammer a q n≠0) :
    qPochhammer (a*q^n) q k=qPochhammer a q k*qPochhammer (a*q^k) q n/qPochhammer a q n := by
  apply (eq_div_iff hd).2
  have h := qPochhammer_add a q n k
  rw [Nat.add_comm n k,qPochhammer_add] at h
  simpa [mul_comm] using h.symm

/-- The shifted factorial `(a q^k;q)_(n-k) = (a;q)_n/(a;q)_k` for `k ≤ n` (DLMF 17.2.E18). -/
@[dlmf 17.2.E18]
theorem qPochhammer_shift_sub {a q : ℂ} {k n : ℕ} (hk : k≤n) (hd : qPochhammer a q k≠0) :
    qPochhammer (a*q^k) q (n-k)=qPochhammer a q n/qPochhammer a q k := by
  apply (eq_div_iff hd).2
  have h := qPochhammer_add a q k (n-k)
  rw [Nat.add_sub_of_le hk] at h
  simpa [mul_comm] using h.symm

/-- Splitting by parity: `(a;q)_(2n) = (a, a q;q²)_n` (DLMF 17.2.E19). -/
@[dlmf 17.2.E19]
theorem qPochhammer_even (a q : ℂ) (n : ℕ) :
    qPochhammer a q (2*n)=qPochhammerList [a,a*q] (q^2) n := by
  induction n with
  | zero => simp [qPochhammerList]
  | succ n ih =>
    rw [Nat.mul_succ,qPochhammer_add,ih]
    simp only [qPochhammerList,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      mul_one,qPochhammer_succ,qPochhammer_zero,pow_zero,pow_mul,pow_succ]
    ring

/-- Splitting into `k` blocks: `(a;q)_(kn) = ∏_(j<k) (a q^j;q^k)_n` (DLMF 17.2.E20). -/
@[dlmf 17.2.E20]
theorem qPochhammer_blocks (a q : ℂ) (k n : ℕ) :
    qPochhammer a q (k*n)=∏ j∈range k, qPochhammer (a*q^j) (q^k) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,qPochhammer_add,ih]
    simp_rw [qPochhammer_succ]
    rw [prod_mul_distrib,qPochhammer_eq_prod]
    congr 1
    apply prod_congr rfl
    intro j hj
    rw [pow_mul]
    ring

/-- Squared argument and base: `(a²;q²)_n = (a;q)_n (-a;q)_n` (DLMF 17.2.E21). -/
@[dlmf 17.2.E21]
theorem qPochhammer_squared (a q : ℂ) (n : ℕ) :
    qPochhammer (a^2) (q^2) n=qPochhammer a q n*qPochhammer (-a) q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [qPochhammer_succ,ih]
    ring

/-- The very-well-poised factor: `(q√a,-q√a;q)_n/(√a,-√a;q)_n = (a q²;q²)_n/(a;q²)_n = (1-a
q^(2n))/(1-a)` (DLMF 17.2.E22). -/
@[dlmf 17.2.E22]
theorem qPochhammer_vwp_ratio {a q : ℂ} (n : ℕ) (hd : qPochhammer a (q^2) n≠0) (ha : a≠1) :
    qPochhammerList [q*Complex.sqrt a,-q*Complex.sqrt a] q n/qPochhammerList
      [Complex.sqrt a,-Complex.sqrt a] q n=qPochhammer (a*q^2) (q^2) n/qPochhammer a (q^2) n ∧
      qPochhammer (a*q^2) (q^2) n/qPochhammer a (q^2) n=(1-a*q^(2*n))/(1-a) := by
  have hs : (Complex.sqrt a)^2=a := by
    rw [Complex.sqrt,← Complex.cpow_nat_mul]
    norm_num
  constructor
  · simp only [qPochhammerList,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    rw [show -q*Complex.sqrt a= -(q*Complex.sqrt a) by ring]
    rw [← qPochhammer_squared,← qPochhammer_squared]
    simp only [mul_pow,hs,mul_comm]
  · apply (div_eq_div_iff hd (sub_ne_zero.mpr (Ne.symm ha))).2
    have h := qPochhammer_add a (q^2) 1 n
    rw [qPochhammer_one,Nat.add_comm 1 n,qPochhammer_succ] at h
    simpa [← pow_mul,mul_comm] using h.symm

/-- Evaluating Mathlib’s root-of-unity factorization at one gives the finite product. -/
private lemma qShiftBasic_root_product {ω : ℂ} {k : ℕ} (hk : 0 < k)
    (hω : IsPrimitiveRoot ω k) (x : ℂ) :
    (∏ j ∈ range k, (1 - ω ^ j * x)) = 1 - x ^ k := by
  have h := X_pow_sub_C_eq_prod hω hk (rfl : x ^ k = x ^ k)
  have he := congrArg (Polynomial.eval (1 : ℂ)) h
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, one_pow] using he.symm

/-- Multiplying shifted factorials over all root-of-unity twists raises both parameter and base. -/
private lemma qShiftBasic_prod_roots {ω : ℂ} {k : ℕ} (hk : 0 < k)
    (hω : IsPrimitiveRoot ω k) (x q : ℂ) (n : ℕ) :
    (∏ j ∈ range k, qPochhammer (ω ^ j * x) q n) = qPochhammer (x ^ k) (q ^ k) n := by
  simp only [qPochhammer_eq_prod]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro l _
  rw [show (∏ j ∈ range k, (1 - ω ^ j * x * q ^ l)) =
    ∏ j ∈ range k, (1 - ω ^ j * (x * q ^ l)) by simp only [mul_assoc],
    qShiftBasic_root_product hk hω]
  simp only [mul_pow, ← pow_mul, Nat.mul_comm]

/-- The `k`-th root analogue of the very-well-poised factor, with `ω` a primitive `k`-th root of
unity (DLMF 17.2.E23). -/
@[dlmf 17.2.E23]
theorem qPochhammer_root_ratio {a q : ℂ} {k : ℕ} (hk : 0<k) (n : ℕ) (hd : qPochhammer a (q^k) n≠0)
    (ha : a≠1) :
    let ω := Complex.exp (2*π*I/k); let r := a^(1/(k:ℂ)); (∏ j∈range k, qPochhammer (q*ω^j*r) q n)/
      (∏ j∈range k, qPochhammer (ω^j*r) q n)=qPochhammer (a*q^k) (q^k) n/qPochhammer a (q^k) n ∧
      qPochhammer (a*q^k) (q^k) n/qPochhammer a (q^k) n=(1-a*q^(k*n))/(1-a) := by
  dsimp only
  let ω := Complex.exp (2 * π * I / k)
  let r := a ^ (1 / (k : ℂ))
  have hω : IsPrimitiveRoot ω k := Complex.isPrimitiveRoot_exp k hk.ne'
  have hr : r ^ k = a := by
    dsimp only [r]
    rw [← Complex.cpow_nat_mul]
    simp [Nat.cast_ne_zero.mpr hk.ne']
  constructor
  · rw [qShiftBasic_prod_roots hk hω r q n, hr]
    rw [show (∏ j ∈ range k, qPochhammer (q * ω ^ j * r) q n) =
      ∏ j ∈ range k, qPochhammer (ω ^ j * (r * q)) q n by
        apply prod_congr rfl; intro j _; congr 1; ring,
      qShiftBasic_prod_roots hk hω (r * q) q n, mul_pow, hr]
  · apply (div_eq_div_iff hd (sub_ne_zero.mpr (Ne.symm ha))).2
    have h := qPochhammer_add a (q ^ k) 1 n
    rw [qPochhammer_one, Nat.add_comm 1 n, qPochhammer_succ] at h
    simpa [← pow_mul, mul_comm] using h.symm

/-- Limits in a parameter: `(a/τ;q)_n τ^n → (-a)^n q^(n(n-1)/2)` as `τ → 0`, and likewise `(aσ;q)_n
σ^(-n)` as `σ → ∞` (DLMF 17.2.E24). -/
@[dlmf 17.2.E24]
theorem qPochhammer_parameter_limit (a q : ℂ) (n : ℕ) :
    Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n*τ^n) (𝓝[≠] 0) (𝓝 ((-a)^n*q^(n.choose 2))) ∧ Tendsto
      (fun σ : ℂ => qPochhammer (a*σ) q n*σ^(-(n:ℤ))) (Filter.cocompact ℂ)
      (𝓝 ((-a)^n*q^(n.choose 2))) := by
  have hfirst : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n*τ^n)
      (𝓝[≠] 0) (𝓝 ((-a)^n*q^(n.choose 2))) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : (n+1).choose 2=n.choose 2+n := by
        simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
      have ht : Tendsto (fun τ : ℂ => τ-a*q^n) (𝓝[≠] 0) (𝓝 (0-a*q^n)) :=
        (tendsto_id.mono_left nhdsWithin_le_nhds).sub_const _
      have hlim := ih.mul ht
      have hv : ((-a)^n*q^(n.choose 2))*(0-a*q^n)=(-a)^(n+1)*q^((n+1).choose 2) := by
        rw [hc,pow_add,pow_succ]
        ring
      rw [hv] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ0 : τ≠0 := by simpa using hτ
      simp only [qPochhammer_succ,pow_succ]
      field_simp
  refine ⟨hfirst,?_⟩
  have hinv : Tendsto (Inv.inv : ℂ → ℂ) (Filter.cocompact ℂ) (𝓝[≠] 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded' : Tendsto (Inv.inv : ℂ → ℂ) (Bornology.cobounded ℂ) (𝓝[≠] 0))
  simpa only [Function.comp_def,div_inv_eq_mul,zpow_neg,zpow_natCast,inv_pow] using hfirst.comp hinv

/-- Ratio limits: `(a/τ;q)_n/(b/τ;q)_n → (a/b)^n` as `τ → 0`, and likewise for `(aσ;q)_n/(bσ;q)_n`
as `σ → ∞` (DLMF 17.2.E25). -/
@[dlmf 17.2.E25]
theorem qPochhammer_parameter_ratio_limit {a b q : ℂ} (hb : b≠0) (hq : q≠0) (n : ℕ) :
    Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n/qPochhammer (b/τ) q n) (𝓝[≠] 0) (𝓝 ((a/b)^n)) ∧
      Tendsto (fun σ : ℂ => qPochhammer (a*σ) q n/qPochhammer (b*σ) q n) (Filter.cocompact ℂ)
      (𝓝 ((a/b)^n)) := by
  have hn : (-b)^n*q^(n.choose 2)≠0 :=
    mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr hb)) (pow_ne_zero _ hq)
  have hv : ((-a)^n*q^(n.choose 2))/((-b)^n*q^(n.choose 2))=(a/b)^n := by
    rw [mul_div_mul_right _ _ (pow_ne_zero _ hq),← div_pow]
    congr 1
    field_simp
  have hfirst : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n/qPochhammer (b/τ) q n)
      (𝓝[≠] 0) (𝓝 ((a/b)^n)) := by
    have h := (qPochhammer_parameter_limit a q n).1.div
      (qPochhammer_parameter_limit b q n).1 hn
    rw [hv] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ0 : τ≠0 := by simpa using hτ
    exact mul_div_mul_right _ _ (pow_ne_zero n hτ0)
  refine ⟨hfirst,?_⟩
  have hinv : Tendsto (Inv.inv : ℂ → ℂ) (Filter.cocompact ℂ) (𝓝[≠] 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded' : Tendsto (Inv.inv : ℂ → ℂ) (Bornology.cobounded ℂ) (𝓝[≠] 0))
  simpa only [Function.comp_def,div_inv_eq_mul] using hfirst.comp hinv

/-- The double parameter limit `(a/τ;q)_n (b/τ;q)_n/(c/τ²;q)_n → (-1)^n (ab/c)^n q^(n(n-1)/2)` as `τ
→ 0` (DLMF 17.2.E26). -/
@[dlmf 17.2.E26]
theorem qPochhammer_double_parameter_limit {a b c q : ℂ} (hc : c≠0) (hq : q≠0) (n : ℕ) :
    Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n*qPochhammer (b/τ) q n/qPochhammer (c/τ^2) q n)
      (𝓝[≠] 0) (𝓝 ((-1:ℂ)^n*(a*b/c)^n*q^(n.choose 2))) := by
  have hn : (-c)^n*q^(n.choose 2)≠0 :=
    mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr hc)) (pow_ne_zero _ hq)
  have ht : Tendsto (fun τ : ℂ => τ^2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using
        ((tendsto_id : Tendsto (fun τ : ℂ => τ) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).pow 2
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      simpa using pow_ne_zero 2 (show τ≠0 by simpa using hτ)
  have h := ((qPochhammer_parameter_limit a q n).1.mul
    (qPochhammer_parameter_limit b q n).1).div
    ((qPochhammer_parameter_limit c q n).1.comp ht) hn
  have hv : ((-a)^n*q^(n.choose 2)*((-b)^n*q^(n.choose 2)))/
      ((-c)^n*q^(n.choose 2))=(-1:ℂ)^n*(a*b/c)^n*q^(n.choose 2) := by
    have hqq : q^(n.choose 2)≠0 := pow_ne_zero _ hq
    calc
      _ = ((-a)^n*(-b)^n/(-c)^n)*q^(n.choose 2) := by field_simp
      _ = (((-a)*(-b)/(-c))^n)*q^(n.choose 2) := by rw [div_pow,mul_pow]
      _ = (-1:ℂ)^n*(a*b/c)^n*q^(n.choose 2) := by
        rw [show (-a)*(-b)/(-c)=(-1:ℂ)*(a*b/c) by ring,mul_pow]
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : τ≠0 := by simpa using hτ
  simp only [Pi.div_apply,Function.comp_apply]
  rw [mul_mul_mul_comm,← pow_mul,show 2*n=n+n by omega,pow_add]
  exact mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero n hτ0) (pow_ne_zero n hτ0))

end DLMF.QHypergeometric
