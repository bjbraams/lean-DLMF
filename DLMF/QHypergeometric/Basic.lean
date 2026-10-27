/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
public import DLMF.GeneralizedHypergeometric.Basic
public import Mathlib.Analysis.RCLike.Sqrt
public import DLMF.QSeries.Identities
public import DLMF.QSeries.QExponential

/-!
# Basic hypergeometric series: common definitions (DLMF §§17.1,17.2,17.4)

The finite, infinite and integer-index shifted factorials, the q-derivative, and the Jackson
integral reuse `DLMF.QSeries`. The integer triangular exponent reuses
`DLMF.QSeries.TripleProduct.tri`. The general unilateral and bilateral series below include
the phase factors specified by DLMF/Gasper–Rahman; both differences of parameter counts
are integers. `tsum` is totalized outside convergence, and all identities below state their
convergence and exceptional-parameter hypotheses separately.
The scalar-series interface below directly applies Mathlib's `ofScalars`, convergence-radius
bound, and change-of-origin analytic API; it does not impose nonzero upper parameters.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory
open scoped Real Topology ENNReal NNReal
namespace DLMF.QHypergeometric

/-- A product of finite q-shifted factorials; parameter repetitions are retained. -/
@[dlmf 17.2.E5]
def qPochhammerList (a : List ℂ) (q : ℂ) (n : ℕ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammer ai q n).prod
/-- A product of integer-index q-shifted factorials, reusing the negative-index convention. -/
def qPochhammerListInt (a : List ℂ) (q : ℂ) (n : ℤ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammerInt ai q n).prod
/-- A product of infinite q-shifted factorials. -/
@[dlmf 17.2.E6]
def qPochhammerListInf (a : List ℂ) (q : ℂ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammerInf ai q).prod
/-- The DLMF phase exponent for a unilateral series, computed in the integers. -/
def qPhiExponent (a b : List ℂ) : ℤ := 1+(b.length:ℤ)-(a.length:ℤ)
/-- The DLMF phase exponent for a bilateral series, computed in the integers. -/
def qPsiExponent (a b : List ℂ) : ℤ := (b.length:ℤ)-(a.length:ℤ)
/-- General unilateral basic-hypergeometric term, including the integer phase exponent. -/
def qPhiTerm (a b : List ℂ) (q z : ℂ) (n : ℕ) : ℂ :=
  qPochhammerList a q n/(qPochhammerList b q n*DLMF.QSeries.qPochhammer q q n)*
    (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri (n:ℤ))^qPhiExponent a b)*z^n
/-- General unilateral basic-hypergeometric series r-phi-s. -/
@[dlmf 17.4.E1]
def qPhi (a b : List ℂ) (q z : ℂ) : ℂ := ∑' n : ℕ, qPhiTerm a b q z n
/-- General bilateral basic-hypergeometric term, with integer index and phase exponent. -/
def qPsiTerm (a b : List ℂ) (q z : ℂ) (n : ℤ) : ℂ :=
  qPochhammerListInt a q n/qPochhammerListInt b q n*
    (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri n)^qPsiExponent a b)*z^n
/-- General bilateral basic-hypergeometric series r-psi-s. -/
@[dlmf 17.4.E3]
def qPsi (a b : List ℂ) (q z : ℂ) : ℂ := ∑' n : ℤ, qPsiTerm a b q z n
/-- A finite unilateral sum, including its term of index N. -/
def qPhiPartial (a b : List ℂ) (q z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N+1), qPhiTerm a b q z n
/-- Denominator parameters avoid the nonpositive q-lattice. -/
def qDenominatorRegular (b : List ℂ) (q : ℂ) : Prop :=
  ∀ bi∈b, ∀ n : ℕ, bi*q^n≠1
/-- Bilateral parameters avoid the additional positive q-lattice in the numerator. -/
def qBilateralRegular (a b : List ℂ) (q : ℂ) : Prop :=
  qDenominatorRegular b q ∧ ∀ ai∈a, ∀ n : ℕ, ai≠q^(n+1)
/-- Termination by an upper parameter q^(-N); lower-parameter validity is independent. -/
def qTerminating (a : List ℂ) (q : ℂ) : Prop :=
  ∃ ai∈a, ∃ N : ℕ, ai=q^(-(N:ℤ))

/-- The general definition agrees with the existing phase-free basicHG when r=s+1. -/
theorem qPhi_eq_basicHG {a b : List ℂ} (h : a.length=b.length+1) (q z : ℂ) :
    qPhi a b q z=DLMF.QSeries.basicHG a b q z := by
  have he : qPhiExponent a b=0 := by simp only [qPhiExponent]; omega
  unfold qPhi DLMF.QSeries.basicHG
  apply tsum_congr
  intro n
  simp [qPhiTerm, qPochhammerList, he]

/-- Integer shifted-factorial products agree with finite products at nonnegative indices. -/
theorem qPochhammerListInt_natCast (a : List ℂ) (q : ℂ) (n : ℕ) :
    qPochhammerListInt a q n=qPochhammerList a q n := by
  simp [qPochhammerListInt,qPochhammerList]

/-- Rogers–Ramanujan G; the term n=0 supplies the initial1. -/
def rogersG (q : ℂ) : ℂ := ∑' n : ℕ, q^(n*n)/DLMF.QSeries.qPochhammer q q n
/-- Rogers–Ramanujan H; the term n=0 supplies the initial1. -/
def rogersH (q : ℂ) : ℂ := ∑' n : ℕ, q^(n*(n+1))/DLMF.QSeries.qPochhammer q q n
/-- Complex-order shifted factorial, on the principal branch of q^ν. -/
def qPochhammerOrder (a q ν : ℂ) : ℂ :=
  DLMF.QSeries.qPochhammerInf a q/DLMF.QSeries.qPochhammerInf (a*q^ν) q
/-- Lower parameters are regular only through the final retained index of a terminating sum. -/
def qDenominatorRegularThrough (b : List ℂ) (q : ℂ) (N : ℕ) : Prop :=
  qPochhammerList b q N≠0
/-- Balanced/Saalschuetzian unilateral series: termination, r=s+1, z=q, and the product balance. -/
@[dlmf 17.4.E9]
def qBalanced (a b : List ℂ) (q z : ℂ) : Prop :=
  qTerminating a q ∧ a.length=b.length+1 ∧ z=q ∧ q*a.prod=b.prod
/-- k-balanced series; k=1 gives the product condition in the balanced case. -/
@[dlmf 17.4.E10]
def qKBalanced (k : ℤ) (a b : List ℂ) (q : ℂ) : Prop :=
  a.length=b.length+1 ∧ q^k*a.prod=b.prod
/-- Well-poised parameters, with a0 singled out and paired remaining upper/lower lists. -/
@[dlmf 17.4.E11]
def qWellPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  List.Forall₂ (fun ai bi => a0*q=ai*bi) a b
/-- Very-well-poised parameters, preserving the first two principal square-root parameters. -/
@[dlmf 17.4.E12]
def qVeryWellPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  qWellPoised a0 a b q ∧ ∃ bb : List ℂ,
    b=Complex.sqrt a0 :: -Complex.sqrt a0 :: bb
/-- Nearly-poised parameters: the paired relations hold except possibly at the last pair. -/
@[dlmf 17.4.E13]
def qNearlyPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  a.length=b.length ∧ List.Forall₂ (fun ai bi => a0*q=ai*bi) a.dropLast b.dropLast
/-- The idem notation is the sum obtained by singling out every parameter except the first. -/
def qIdem (f : ℂ → List ℂ → ℂ) (a : List ℂ) : ℂ :=
  ∑ j ∈ range (a.length-1), f (a[j+1]!) (a.eraseIdx (j+1))

open DLMF.QSeries
/-- qPochhammer order hasProd. -/
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

/-- qPochhammer order nat. -/
theorem qPochhammer_order_nat {a q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qPochhammerInf (a*q^n) q≠0) : qPochhammerOrder a q n=qPochhammer a q n := by
  unfold qPochhammerOrder
  rw [cpow_natCast]
  apply (div_eq_iff hd).2
  exact qPochhammerInf_mul_qPochhammer hq n

/-- qPochhammer invert base. -/
@[dlmf 17.2.E7]
theorem qPochhammer_invert_base {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q⁻¹ n=qPochhammer a⁻¹ q n*(-a)^n*q^(-(n.choose 2:ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n+1).choose 2=n.choose 2+n := by
      simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
    rw [qPochhammer_succ,qPochhammer_succ,ih,hc]
    simp only [Nat.cast_add,neg_add,zpow_add₀ hq,zpow_neg,zpow_natCast,pow_succ,inv_pow]
    field_simp
    ring

/-- qPochhammer invert base ratio. -/
@[dlmf 17.2.E8]
theorem qPochhammer_invert_base_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q⁻¹ n/qPochhammer b q⁻¹ n=qPochhammer a⁻¹ q n/qPochhammer b⁻¹ q n*(a/b)^n := by
  rw [qPochhammer_invert_base ha hq,qPochhammer_invert_base hb hq]
  rw [mul_div_mul_right _ _ (zpow_ne_zero _ hq),mul_div_mul_comm]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- qPochhammer reverse. -/
@[dlmf 17.2.E9]
theorem qPochhammer_reverse {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q n=qPochhammer (q^(1-(n:ℤ))/a) q n*(-a)^n*q^(n.choose 2) := by
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

/-- qPochhammer reverse ratio. -/
@[dlmf 17.2.E10]
theorem qPochhammer_reverse_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q n/qPochhammer b q n=qPochhammer (q^(1-(n:ℤ))/a) q n/qPochhammer (q^(1-(n:ℤ))/b) q n*(a/b)^n := by
  rw [qPochhammer_reverse ha hq,qPochhammer_reverse hb hq]
  rw [mul_div_mul_right _ _ (pow_ne_zero _ hq),mul_div_mul_comm]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- qPochhammer shift negative. -/
@[dlmf 17.2.E11]
theorem qPochhammer_shift_negative {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) : qPochhammer (a*q^(-(n:ℤ))) q n=qPochhammer (q/a) q n*(-a/q)^n*q^(-(n.choose 2:ℤ)) := by
  have h := DLMF.QSeries.TripleProduct.qPochhammer_shift_down hq ha n
  have hc : (n+1).choose 2=n.choose 2+n := by
    simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
  rw [hc,pow_add] at h
  simp only [zpow_neg,zpow_natCast,← div_eq_mul_inv,div_pow]
  field_simp
  linear_combination h

/-- qPochhammer negative. -/
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
  simp [← inv_pow,ha]
  rw [mul_assoc,← mul_pow,mul_inv_cancel₀ ha,one_pow,mul_one]

/-- qPochhammer shift negative ratio. -/
@[dlmf 17.2.E12]
theorem qPochhammer_shift_negative_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) : qPochhammer (a*q^(-(n:ℤ))) q n/qPochhammer (b*q^(-(n:ℤ))) q n=qPochhammer (q/a) q n/qPochhammer (q/b) q n*(a/b)^n := by
  rw [qPochhammer_shift_negative ha hq,qPochhammer_shift_negative hb hq]
  rw [mul_div_mul_right _ _ (zpow_ne_zero _ hq),mul_div_mul_comm]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- The reversal of a shifted block, used for 17.2.E13. -/
theorem qaR4_reverse_tail {a q : ℂ} (ha : a≠0) (hq : q≠0) (m k : ℕ) :
    qPochhammer (a*q^m) q k=qPochhammer (q^(1-((m+k:ℕ):ℤ))/a) q k*(-(a*q^m))^k*q^(k.choose 2) := by
  have h := qPochhammer_reverse (mul_ne_zero ha (pow_ne_zero m hq)) hq k
  have he : q^(1-(k:ℤ))/(a*q^m)=q^(1-((m+k:ℕ):ℤ))/a := by
    rw [show (1-((m+k:ℕ):ℤ))=(1-(k:ℤ))-(m:ℤ) by push_cast; ring,zpow_sub₀ hq (1-(k:ℤ)) m,
      zpow_natCast,div_div,mul_comm a]
  rw [he] at h
  exact h

/-- `2·C(k,2)+k=k²`. -/
theorem qaR4_choose_two_mul (k : ℕ) : (k.choose 2)*2+k=k*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ',Nat.choose_one_right]
    nlinarith

/-- Cancelling a natural power against an integer exponent difference. -/
lemma qaR4_zpow_choose_sub {q : ℂ} (hq : q≠0) (c n : ℕ) :
    q^((c:ℤ)-(n:ℤ))*q^n=q^c := by
  rw [← zpow_natCast q n,← zpow_add₀ hq]
  simp

/-- qPochhammer sub index. -/
@[dlmf 17.2.E13]
theorem qPochhammer_sub_index {a q : ℂ} (ha : a≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n) (hd : qPochhammer (q^(1-(n:ℤ))/a) q k≠0) : qPochhammer a q (n-k)=qPochhammer a q n/qPochhammer (q^(1-(n:ℤ))/a) q k*(-q/a)^k*q^((k.choose 2:ℤ)-(n:ℤ)*k) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel,qPochhammer_add,qaR4_reverse_tail ha hq m k]
  generalize qPochhammer (q^(1-((m+k:ℕ):ℤ))/a) q k = X at hd ⊢
  have hE := qaR4_zpow_choose_sub hq (k.choose 2) ((m+k)*k)
  rw [show (((m+k)*k:ℕ):ℤ)=((m+k:ℕ):ℤ)*(k:ℤ) by push_cast; ring] at hE
  generalize q^((k.choose 2:ℤ)-((m+k:ℕ):ℤ)*(k:ℤ)) = E at hE ⊢
  have hk2 := qaR4_choose_two_mul k
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

/-- qPochhammer sub index ratio. -/
@[dlmf 17.2.E14]
theorem qPochhammer_sub_index_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n) (hda : qPochhammer (q^(1-(n:ℤ))/a) q k≠0) (hdb : qPochhammer (q^(1-(n:ℤ))/b) q k≠0) : qPochhammer a q (n-k)/qPochhammer b q (n-k)=qPochhammer a q n/qPochhammer b q n*(qPochhammer (q^(1-(n:ℤ))/b) q k/qPochhammer (q^(1-(n:ℤ))/a) q k)*(b/a)^k := by
  rw [qPochhammer_sub_index ha hq hk hda,qPochhammer_sub_index hb hq hk hdb]
  by_cases hB : qPochhammer b q n=0
  · simp [hB]
  have hQ : q^((k.choose 2:ℤ)-(n:ℤ)*k)≠0 := zpow_ne_zero _ hq
  rw [show (b/a)^k=(-q/a)^k/(-q/b)^k by rw [← div_pow]; congr 1; field_simp]
  have h1 : (-q/b)^k≠0 := pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr hq) hb)
  field_simp

/-- qPochhammer shift negative general. -/
@[dlmf 17.2.E15]
theorem qPochhammer_shift_negative_general {a q : ℂ} (ha : a≠0) (hq : q≠0) (k n : ℕ) (hd : qPochhammer (q^(1-(k:ℤ))/a) q n≠0) : qPochhammer (a*q^(-(n:ℤ))) q k=qPochhammer a q k*qPochhammer (q/a) q n/qPochhammer (q^(1-(k:ℤ))/a) q n*q^(-(n:ℤ)*k) := by
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

/-- qPochhammer shift negative sub. -/
@[dlmf 17.2.E16]
theorem qPochhammer_shift_negative_sub {a q : ℂ} (ha : a≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n) (hd : qPochhammer (q/a) q k≠0) : qPochhammer (a*q^(-(n:ℤ))) q (n-k)=qPochhammer (q/a) q n/qPochhammer (q/a) q k*(-a/q)^(n-k)*q^((k.choose 2:ℤ)-(n.choose 2:ℤ)) := by
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

/-- qPochhammer shift positive. -/
@[dlmf 17.2.E17]
theorem qPochhammer_shift_positive {a q : ℂ} (k n : ℕ) (hd : qPochhammer a q n≠0) : qPochhammer (a*q^n) q k=qPochhammer a q k*qPochhammer (a*q^k) q n/qPochhammer a q n := by
  apply (eq_div_iff hd).2
  have h := qPochhammer_add a q n k
  rw [Nat.add_comm n k,qPochhammer_add] at h
  simpa [mul_comm] using h.symm

/-- qPochhammer shift sub. -/
@[dlmf 17.2.E18]
theorem qPochhammer_shift_sub {a q : ℂ} {k n : ℕ} (hk : k≤n) (hd : qPochhammer a q k≠0) : qPochhammer (a*q^k) q (n-k)=qPochhammer a q n/qPochhammer a q k := by
  apply (eq_div_iff hd).2
  have h := qPochhammer_add a q k (n-k)
  rw [Nat.add_sub_of_le hk] at h
  simpa [mul_comm] using h.symm

/-- qPochhammer even. -/
@[dlmf 17.2.E19]
theorem qPochhammer_even (a q : ℂ) (n : ℕ) : qPochhammer a q (2*n)=qPochhammerList [a,a*q] (q^2) n := by
  induction n with
  | zero => simp [qPochhammerList]
  | succ n ih =>
    rw [Nat.mul_succ,qPochhammer_add,ih]
    simp only [qPochhammerList,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      mul_one,qPochhammer_succ,qPochhammer_zero,pow_zero,pow_mul,pow_succ]
    ring

/-- qPochhammer blocks. -/
@[dlmf 17.2.E20]
theorem qPochhammer_blocks (a q : ℂ) (k n : ℕ) : qPochhammer a q (k*n)=∏ j∈range k, qPochhammer (a*q^j) (q^k) n := by
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

/-- qPochhammer squared. -/
@[dlmf 17.2.E21]
theorem qPochhammer_squared (a q : ℂ) (n : ℕ) : qPochhammer (a^2) (q^2) n=qPochhammer a q n*qPochhammer (-a) q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [qPochhammer_succ,ih,pow_mul]
    ring

/-- qPochhammer vwp ratio. -/
@[dlmf 17.2.E22]
theorem qPochhammer_vwp_ratio {a q : ℂ} (n : ℕ) (hd : qPochhammer a (q^2) n≠0) (ha : a≠1) : qPochhammerList [q*Complex.sqrt a,-q*Complex.sqrt a] q n/qPochhammerList [Complex.sqrt a,-Complex.sqrt a] q n=qPochhammer (a*q^2) (q^2) n/qPochhammer a (q^2) n ∧ qPochhammer (a*q^2) (q^2) n/qPochhammer a (q^2) n=(1-a*q^(2*n))/(1-a) := by
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

/-- qPochhammer root ratio. -/
@[dlmf 17.2.E23]
theorem qPochhammer_root_ratio {a q : ℂ} {k : ℕ} (hk : 0<k) (n : ℕ) (hd : qPochhammer a (q^k) n≠0) (ha : a≠1) : let ω := Complex.exp (2*π*I/k); let r := a^(1/(k:ℂ)); (∏ j∈range k, qPochhammer (q*ω^j*r) q n)/(∏ j∈range k, qPochhammer (ω^j*r) q n)=qPochhammer (a*q^k) (q^k) n/qPochhammer a (q^k) n ∧ qPochhammer (a*q^k) (q^k) n/qPochhammer a (q^k) n=(1-a*q^(k*n))/(1-a) := by
  sorry

/-- qPochhammer parameter limit. -/
@[dlmf 17.2.E24]
theorem qPochhammer_parameter_limit (a q : ℂ) (n : ℕ) : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n*τ^n) (𝓝[≠] 0) (𝓝 ((-a)^n*q^(n.choose 2))) ∧ Tendsto (fun σ : ℂ => qPochhammer (a*σ) q n*σ^(-(n:ℤ))) (Filter.cocompact ℂ) (𝓝 ((-a)^n*q^(n.choose 2))) := by
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

/-- qPochhammer parameter ratio limit. -/
@[dlmf 17.2.E25]
theorem qPochhammer_parameter_ratio_limit {a b q : ℂ} (hb : b≠0) (hq : q≠0) (n : ℕ) : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n/qPochhammer (b/τ) q n) (𝓝[≠] 0) (𝓝 ((a/b)^n)) ∧ Tendsto (fun σ : ℂ => qPochhammer (a*σ) q n/qPochhammer (b*σ) q n) (Filter.cocompact ℂ) (𝓝 ((a/b)^n)) := by
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

/-- qPochhammer double parameter limit. -/
@[dlmf 17.2.E26]
theorem qPochhammer_double_parameter_limit {a b c q : ℂ} (hc : c≠0) (hq : q≠0) (n : ℕ) : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n*qPochhammer (b/τ) q n/qPochhammer (c/τ^2) q n) (𝓝[≠] 0) (𝓝 ((-1:ℂ)^n*(a*b/c)^n*q^(n.choose 2))) := by
  have hn : (-c)^n*q^(n.choose 2)≠0 :=
    mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr hc)) (pow_ne_zero _ hq)
  have ht : Tendsto (fun τ : ℂ => τ^2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((tendsto_id : Tendsto (fun τ : ℂ => τ) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).pow 2
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

/-- qPhi hasSum. -/
theorem qPhi_hasSum {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q)
    (hr : a.length≤b.length+1) (hz : a.length=b.length+1 → ‖z‖<1) :
    HasSum (qPhiTerm a b q z) (qPhi a b q z) := by
  let K : ℕ := b.length+1-a.length
  let F (p : List ℂ) (n : ℕ) : ℂ := (p.map fun ai => 1-ai*q^n).prod
  let R (n : ℕ) : ℂ := F a n/(F b n*(1-q^(n+1)))*(-q^n)^K*z
  have hexp : qPhiExponent a b=(K:ℤ) := by
    dsimp [qPhiExponent,K]
    omega
  have htri (n : ℕ) : DLMF.QSeries.TripleProduct.tri n=(n.choose 2:ℤ) := by
    simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast n 0).symm
  have ht (n : ℕ) : qPhiTerm a b q z n=
      qPochhammerList a q n/(qPochhammerList b q n*qPochhammer q q n)*
      (((-1:ℂ)^n*q^(n.choose 2))^K)*z^n := by
    simp only [qPhiTerm,hexp,htri,zpow_natCast]
  have hp (p : List ℂ) (n : ℕ) : qPochhammerList p q (n+1)=qPochhammerList p q n*F p n := by
    induction p with
    | nil => simp [qPochhammerList,F]
    | cons c p ih =>
      simp only [qPochhammerList,List.map_cons,List.prod_cons] at ih ⊢
      rw [qPochhammer_succ,ih]
      simp only [F,List.map_cons,List.prod_cons]
      ring
  have hB (n : ℕ) : qPochhammerList b q n≠0 := by
    apply List.prod_ne_zero
    intro hy
    obtain ⟨bi,hbi,hzero⟩ := List.mem_map.mp hy
    exact (qPochhammer_ne_zero_of_factors hq
      (fun j => sub_ne_zero.mpr (hb bi hbi j).symm) n) hzero
  have hF (n : ℕ) : F b n≠0 := by
    apply List.prod_ne_zero
    intro hy
    obtain ⟨bi,hbi,hzero⟩ := List.mem_map.mp hy
    exact (sub_ne_zero.mpr (hb bi hbi n).symm) hzero
  have hrec (n : ℕ) : qPhiTerm a b q z (n+1)=R n*qPhiTerm a b q z n := by
    have hc : (n+1).choose 2=n.choose 2+n := by
      simpa [Nat.add_comm] using (Nat.choose_succ_succ' n 1)
    have hq1 : 1-q*q^n≠0 := by
      simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    simp only [ht,hp,qPochhammer_succ,R,hc,pow_add,pow_succ,mul_pow]
    rw [show (-q^n)^K=(-1:ℂ)^K*(q^n)^K by rw [← mul_pow,neg_one_mul]]
    field_simp [hB n,hF n,qPochhammer_self_ne_zero hq n,hq1]
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have hlimF (p : List ℂ) : Tendsto (F p) atTop (𝓝 1) := by
    induction p with
    | nil => simpa [F] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1))
    | cons c p ih =>
      have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1)).sub
        (hpow.const_mul c)).mul ih
      simpa [F] using h
  have hfrac : Tendsto (fun n : ℕ => F a n/(F b n*(1-q^(n+1)))) atTop (𝓝 1) := by
    have hqpow : Tendsto (fun n : ℕ => q^(n+1)) atTop (𝓝 0) := by
      simpa [pow_succ] using hpow.mul_const q
    have h := (hlimF a).div ((hlimF b).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1)).sub hqpow)) (by norm_num)
    simpa only [Pi.div_def,one_mul,mul_one,sub_zero,div_one] using h
  have hR : Tendsto R atTop (𝓝 (if K=0 then z else 0)) := by
    by_cases hK : K=0
    · simpa [R,hK] using hfrac.mul_const z
    · have h := (hfrac.mul (hpow.neg.pow K)).mul_const z
      simpa [R,hK,zero_pow hK] using h
  have hzlim : ‖(if K=0 then z else 0 : ℂ)‖<1 := by
    by_cases hK : K=0
    · simpa [hK] using hz (by dsimp [K] at hK; omega)
    · simp [hK]
  obtain ⟨r,hr,hr1⟩ := exists_between hzlim
  have hs : Summable (qPhiTerm a b q z) := by
    apply summable_of_ratio_norm_eventually_le hr1
    filter_upwards [hR.norm.eventually_lt tendsto_const_nhds hr] with n hn
    rw [hrec,norm_mul]
    exact mul_le_mul_of_nonneg_right (le_of_lt hn) (norm_nonneg _)
  exact hs.hasSum

/-- The integer-index factorial at a nonpositive index, uniformly in the index. -/
lemma qaR4_qPochhammerInt_neg (x q : ℂ) (m : ℕ) :
    qPochhammerInt x q (-(m:ℤ))=(qPochhammer (x*q^(-(m:ℤ))) q m)⁻¹ := by
  cases m with
  | zero => simp [qPochhammerInt]
  | succ n => rfl

/-- One step down in the integer-index factorial. -/
lemma qaR4_qPochhammerInt_neg_succ {x q : ℂ} (hq : q≠0) (m : ℕ) :
    qPochhammerInt x q (-((m+1:ℕ):ℤ))=
      qPochhammerInt x q (-(m:ℤ))/(1-x*q^(-((m+1:ℕ):ℤ))) := by
  rw [qaR4_qPochhammerInt_neg,qaR4_qPochhammerInt_neg,qPochhammer_succ']
  have e : x*q^(-((m+1:ℕ):ℤ))*q=x*q^(-(m:ℤ)) := by
    rw [mul_assoc,← zpow_add_one₀ hq]; congr 2; push_cast; ring
  rw [e,mul_inv,div_eq_mul_inv,mul_comm]

/-- One step down in a product of integer-index factorials. -/
lemma qaR4_qPochhammerListInt_neg_succ (l : List ℂ) {q : ℂ} (hq : q≠0) (m : ℕ) :
    qPochhammerListInt l q (-((m+1:ℕ):ℤ))=
      qPochhammerListInt l q (-(m:ℤ))/(l.map fun x => 1-x*q^(-((m+1:ℕ):ℤ))).prod := by
  induction l with
  | nil => simp [qPochhammerListInt]
  | cons c l ih =>
    simp only [qPochhammerListInt,List.map_cons,List.prod_cons] at ih ⊢
    rw [ih,qaR4_qPochhammerInt_neg_succ hq,div_mul_div_comm]

/-- The integer triangular number one step down. -/
lemma qaR4_tri_neg_succ (m : ℕ) :
    DLMF.QSeries.TripleProduct.tri (-((m+1:ℕ):ℤ))=
      DLMF.QSeries.TripleProduct.tri (-(m:ℤ))+((m+1:ℕ):ℤ) := by
  have h1 := DLMF.QSeries.TripleProduct.tri_mul_two (-((m+1:ℕ):ℤ))
  have h2 := DLMF.QSeries.TripleProduct.tri_mul_two (-(m:ℤ))
  push_cast at h1 h2 ⊢
  ring_nf at h1 h2 ⊢
  linarith

/-- Factoring the reciprocal power out of a list product. -/
lemma qaR4_list_prod_one_sub (l : List ℂ) {w Q : ℂ} (hw : w*Q=1) :
    (l.map fun x => 1-x*w).prod=w^l.length*(l.map fun x => Q-x).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,ih,pow_succ]
    linear_combination (-(w^l.length*(l.map fun x => Q-x).prod))*hw

/-- The ratio recursion for bilateral terms at negative indices. -/
lemma qaR4_qPsiTerm_neg_succ {a b : List ℂ} {q z : ℂ} (hq : q≠0) (hz : z≠0)
    (hr : a.length≤b.length) (ha : ∀ ai∈a, ∀ n : ℕ, ai≠q^(n+1)) (m : ℕ) :
    qPsiTerm a b q z (-((m+1:ℕ):ℤ))=
      (b.map fun x => q^(m+1)-x).prod/(a.map fun x => q^(m+1)-x).prod*
        (-1:ℂ)^(b.length-a.length)/z*qPsiTerm a b q z (-(m:ℤ)) := by
  set w : ℂ := q^(-((m+1:ℕ):ℤ)) with hwdef
  have hw : w*q^(m+1)=1 := by
    rw [hwdef,zpow_neg,zpow_natCast]; exact inv_mul_cancel₀ (pow_ne_zero _ hq)
  have hw0 : w≠0 := zpow_ne_zero _ hq
  have hE : qPsiExponent a b=((b.length-a.length:ℕ):ℤ) := by
    simp only [qPsiExponent]; omega
  have hA : (a.map fun x => q^(m+1)-x).prod≠0 := by
    apply List.prod_ne_zero
    intro h
    obtain ⟨x,hx,h0⟩ := List.mem_map.mp h
    exact ha x hx m (sub_eq_zero.mp h0).symm
  unfold qPsiTerm
  rw [qaR4_qPochhammerListInt_neg_succ a hq,qaR4_qPochhammerListInt_neg_succ b hq,
    qaR4_list_prod_one_sub a hw,qaR4_list_prod_one_sub b hw,hE,zpow_natCast,zpow_natCast,
    qaR4_tri_neg_succ]
  have hz1 : z^(-((m+1:ℕ):ℤ))=z^(-(m:ℤ))/z := by
    rw [show -((m+1:ℕ):ℤ)=-(m:ℤ)-1 by push_cast; ring,zpow_sub_one₀ hz]; rfl
  have hm1 : (-1:ℂ)^(-((m+1:ℕ):ℤ))=(-1:ℂ)^(-(m:ℤ))*(-1) := by
    rw [show -((m+1:ℕ):ℤ)=-(m:ℤ)+(-1) by push_cast; ring,zpow_add₀ (by norm_num)]
    simp
  have hq1 : q^(DLMF.QSeries.TripleProduct.tri (-(m:ℤ))+((m+1:ℕ):ℤ))=
      q^(DLMF.QSeries.TripleProduct.tri (-(m:ℤ)))*q^(m+1) := by
    rw [zpow_add₀ hq,zpow_natCast]
  rw [hz1,hm1,hq1]
  obtain ⟨e,he⟩ : ∃ e, b.length=a.length+e := ⟨b.length-a.length,by omega⟩
  rw [he,Nat.add_sub_cancel_left,pow_add w]
  have hwe : w^e*(q^(m+1))^e=1 := by rw [← mul_pow,hw,one_pow]
  rw [show ((-1:ℂ)^(-(m:ℤ))*(-1)*(q^(DLMF.QSeries.TripleProduct.tri (-(m:ℤ)))*q^(m+1)))^e=
    ((-1:ℂ)^(-(m:ℤ))*q^(DLMF.QSeries.TripleProduct.tri (-(m:ℤ))))^e*(-1)^e*(q^(m+1))^e by ring]
  generalize ((-1:ℂ)^(-(m:ℤ))*q^(DLMF.QSeries.TripleProduct.tri (-(m:ℤ))))^e = P
  generalize w^e=W at hwe ⊢
  generalize (q^(m+1))^e=Qe at hwe ⊢
  generalize q^(m+1)=Q at hA ⊢
  have hAr : w^a.length≠0 := pow_ne_zero _ hw0
  by_cases hB : qPochhammerListInt b q (-(m:ℤ))=0
  · simp [hB]
  by_cases hBp : (b.map fun x => Q-x).prod=0
  · simp [hBp]
  have hW : W≠0 := left_ne_zero_of_mul_eq_one hwe
  field_simp
  linear_combination (qPochhammerListInt a q (-(m:ℤ))*P)*hwe
/-- The limit of a list product of `q^(m+1)-x` as `m→∞`. -/
lemma qaR4_tendsto_list_prod_pow_sub (l : List ℂ) {q : ℂ} (hq : ‖q‖<1) :
    Tendsto (fun m : ℕ => (l.map fun x => q^(m+1)-x).prod) atTop
      (𝓝 ((-1:ℂ)^l.length*l.prod)) := by
  have hpow : Tendsto (fun m : ℕ => q^(m+1)) atTop (𝓝 0) := by
    simpa [pow_succ] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const q
  induction l with
  | nil => simp
  | cons c l ih =>
    have h := (hpow.sub_const c).mul ih
    have e : (0-c)*((-1:ℂ)^l.length*l.prod)=(-1:ℂ)^(l.length+1)*(c*l.prod) := by ring
    rw [e] at h
    simpa only [List.map_cons,List.prod_cons,List.length_cons] using h

/-- Nonnegative-index bilateral terms are unilateral terms with the extra numerator `q`. -/
lemma qaR4_qPsiTerm_natCast {a b : List ℂ} {q z : ℂ} (hq : ‖q‖<1) (n : ℕ) :
    qPsiTerm a b q z n=qPhiTerm (q::a) b q z n := by
  have hE : qPhiExponent (q::a) b=qPsiExponent a b := by
    simp only [qPhiExponent,qPsiExponent,List.length_cons]; push_cast; ring
  unfold qPsiTerm qPhiTerm
  rw [hE,qPochhammerListInt_natCast,qPochhammerListInt_natCast]
  simp only [qPochhammerList,List.map_cons,List.prod_cons,zpow_natCast]
  have h := qPochhammer_self_ne_zero hq n
  by_cases hb : (b.map fun bi => qPochhammer bi q n).prod=0
  · simp [hb]
  field_simp

/-- The negative-index bilateral terms are summable. -/
lemma qaR4_qPsiTerm_neg_summable {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1) :
    Summable (fun m : ℕ => qPsiTerm a b q z (-(m:ℤ))) := by
  set R : ℕ → ℂ := fun m => (b.map fun x => q^(m+1)-x).prod/(a.map fun x => q^(m+1)-x).prod*
        (-1:ℂ)^(b.length-a.length)/z
  have hrec (m : ℕ) : qPsiTerm a b q z (-((m+1:ℕ):ℤ))=R m*qPsiTerm a b q z (-(m:ℤ)) :=
    qaR4_qPsiTerm_neg_succ hq0 hz0 hr hab.2 m
  have hR : Tendsto R atTop (𝓝 ((-1:ℂ)^b.length*b.prod/((-1:ℂ)^a.length*a.prod)*
      (-1:ℂ)^(b.length-a.length)/z)) := by
    have hA : (-1:ℂ)^a.length*a.prod≠0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) ha
    exact (((qaR4_tendsto_list_prod_pow_sub b hq).div (qaR4_tendsto_list_prod_pow_sub a hq) hA).mul_const
      _).div_const _
  have hlim : ‖(-1:ℂ)^b.length*b.prod/((-1:ℂ)^a.length*a.prod)*
      (-1:ℂ)^(b.length-a.length)/z‖<1 := by
    convert hz using 1
    simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    rw [mul_one,div_div]
  obtain ⟨r,hr0,hr1⟩ := exists_between hlim
  apply summable_of_ratio_norm_eventually_le hr1
  filter_upwards [hR.norm.eventually_lt tendsto_const_nhds hr0] with n hn
  have := hrec n
  push_cast at this
  rw [show (-(((n+1:ℕ)):ℤ))=-((n:ℤ)+1) by push_cast; rfl, this,norm_mul]
  exact mul_le_mul_of_nonneg_right (le_of_lt hn) (norm_nonneg _)

/-- Both halves of a bilateral series in its annulus are summable. -/
lemma qaR4_qPsiTerm_summable_parts {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1)
    (hz' : a.length=b.length → ‖z‖<1) :
    Summable (fun n : ℕ => qPsiTerm a b q z n) ∧
      Summable (fun n : ℕ => qPsiTerm a b q z (-(n+1))) := by
  constructor
  · have h := (qPhi_hasSum (a := q::a) (b := b) (z := z) hq0 hq hab.1 (by simp; omega)
      (fun h => hz' (by simpa using h))).summable
    exact h.congr fun n => (qaR4_qPsiTerm_natCast hq n).symm
  · have h := (summable_nat_add_iff 1).mpr (qaR4_qPsiTerm_neg_summable hq0 hq hab ha hz0 hr hz)
    simpa only [Nat.cast_add,Nat.cast_one] using h

/-- The successor step of a finite factorial product. -/
lemma qaR4_qPochhammerList_succ (l : List ℂ) (q : ℂ) (n : ℕ) :
    qPochhammerList l q (n+1)=qPochhammerList l q n*(l.map fun x => 1-x*q^n).prod := by
  induction l with
  | nil => simp [qPochhammerList]
  | cons c l ih =>
    simp only [qPochhammerList,List.map_cons,List.prod_cons] at ih ⊢
    rw [qPochhammer_succ,ih]
    ring

/-- Rewriting `q^(m+1)-x` through the reciprocal parameter. -/
lemma qaR4_list_prod_pow_sub_recip (l : List ℂ) (q : ℂ) (m : ℕ) (hl : ∀ x∈l, x≠0) :
    (l.map fun x => q^(m+1)-x).prod=(-1:ℂ)^l.length*l.prod*
      ((l.map fun x => q/x).map fun y => 1-y*q^m).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have hc : c≠0 := hl c (by simp)
    simp only [List.map_cons,List.prod_cons,List.length_cons,List.map_map]
    rw [ih (fun x hx => hl x (by simp [hx]))]
    simp only [List.map_map]
    rw [pow_succ]
    field_simp
    ring

/-- Closed form of the negative-index bilateral terms. -/
lemma qaR4_qPsiTerm_neg_closed {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hb0 : b.prod≠0)
    (m : ℕ) :
    qPsiTerm a b q z (-(m:ℤ))=qPochhammerList (b.map fun bi => q/bi) q m/
      qPochhammerList (a.map fun ai => q/ai) q m*(b.prod/(a.prod*z))^m := by
  have hbx : ∀ x∈b, x≠0 := fun x hx h => hb0 (List.prod_eq_zero (h ▸ hx))
  have hax : ∀ x∈a, x≠0 := fun x hx h => ha (List.prod_eq_zero (h ▸ hx))
  induction m with
  | zero => simp [qPsiTerm,qPochhammerListInt,qPochhammerList,qPochhammerInt,
      DLMF.QSeries.TripleProduct.tri,Function.comp_def,List.map_const',List.prod_replicate]
  | succ m ih =>
    rw [qaR4_qPsiTerm_neg_succ hq0 hz0 hr hab.2 m,ih,qaR4_qPochhammerList_succ,
      qaR4_qPochhammerList_succ,qaR4_list_prod_pow_sub_recip b q m hbx,
      qaR4_list_prod_pow_sub_recip a q m hax]
    have hFa : ((a.map fun x => q/x).map fun y => 1-y*q^m).prod≠0 := by
      apply List.prod_ne_zero
      intro h
      obtain ⟨y,hy,h0⟩ := List.mem_map.mp h
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      apply hab.2 x hx m
      have hx0 := hax x hx
      field_simp at h0
      rw [pow_succ]
      linear_combination h0
    obtain ⟨e,he⟩ : ∃ e, b.length=a.length+e := ⟨b.length-a.length,by omega⟩
    rw [he,Nat.add_sub_cancel_left,pow_succ]
    generalize ((a.map fun x => q/x).map fun y => 1-y*q^m).prod = Fa at hFa ⊢
    generalize ((b.map fun x => q/x).map fun y => 1-y*q^m).prod = Fb
    by_cases hA : qPochhammerList (a.map fun ai => q/ai) q m=0
    · simp [hA]
    have h1 : ((-1:ℂ)^e)^2=1 := by rw [← pow_mul,pow_mul',neg_one_sq,one_pow]
    field_simp
    rw [pow_add]
    linear_combination (Fb*qPochhammerList (b.map fun bi => q/bi) q m*(-1:ℂ)^a.length)*h1
/-- qPsi hasSum. -/
theorem qPsi_hasSum {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1)
    (hz' : a.length=b.length → ‖z‖<1) : HasSum (qPsiTerm a b q z) (qPsi a b q z) := by
  obtain ⟨h1,h2⟩ := qaR4_qPsiTerm_summable_parts hq0 hq hab ha hz0 hr hz hz'
  exact (h1.of_nat_of_neg_add_one h2).hasSum

/-- qPsi split. -/
@[dlmf 17.4.E3]
theorem qPsi_split {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hb0 : b.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1)
    (hz' : a.length=b.length → ‖z‖<1) :
    qPsi a b q z=(∑' n : ℕ, qPsiTerm a b q z n)+
      ∑' n : ℕ, qPochhammerList (b.map fun bi => q/bi) q (n+1)/
        qPochhammerList (a.map fun ai => q/ai) q (n+1)*(b.prod/(a.prod*z))^(n+1) := by
  obtain ⟨h1,h2⟩ := qaR4_qPsiTerm_summable_parts hq0 hq hab ha hz0 hr hz hz'
  unfold qPsi
  rw [tsum_of_nat_of_neg_add_one h1 h2]
  congr 1
  apply tsum_congr
  intro n
  rw [← qaR4_qPsiTerm_neg_closed hq0 hz0 hr hab ha hb0 (n+1)]
  push_cast
  rfl

/-- qPhi terminates. -/
theorem qPhi_terminates {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (N : ℕ) (hb : qDenominatorRegularThrough b q N) :
    qPhi (q^(-(N:ℤ))::a) b q z=qPhiPartial (q^(-(N:ℤ))::a) b q z N := by
  unfold qPhi qPhiPartial
  apply tsum_eq_sum
  intro k hk
  have hNk : N<k := by simpa using hk
  have hz := qPochhammer_recip_pow_eq_zero hq0 hNk
  simp [qPhiTerm,qPochhammerList,hz]

/-- qIdem expansion. -/
theorem qIdem_expansion (f : ℂ → List ℂ → ℂ) (x : ℂ) (a : List ℂ) :
    f x a+qIdem f (x::a)=∑ j∈range (a.length+1), f ((x::a)[j]!) ((x::a).eraseIdx j) := by
  simp only [qIdem,List.length_cons,Nat.add_sub_cancel]
  rw [sum_range_succ']
  simp [add_comm]

/-- The bilateral split by actual negative indices, valid also for lower parameter zero. -/
@[dlmf 17.4.E3]
theorem qPsi_split_indices {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1)
    (hz' : a.length=b.length → ‖z‖<1) :
    qPsi a b q z=(∑' n : ℕ, qPsiTerm a b q z n)+
      ∑' n : ℕ, qPsiTerm a b q z (-(n:ℤ)-1) := by
  obtain ⟨h1,h2⟩ := qaR4_qPsiTerm_summable_parts hq0 hq hab ha hz0 hr hz hz'
  unfold qPsi
  rw [tsum_of_nat_of_neg_add_one h1 h2]
  congr 1
  apply tsum_congr
  intro n
  congr 1
  ring

/-- Formal coefficient limit in17.4.2, with its integer phase/scaling exponent. -/
@[dlmf 17.4.E2]
theorem qPhi_coefficient_classical_limit (a b : List ℂ) (z : ℂ) (n : ℕ)
    (hb : DLMF.Hypergeometric.genDenRegular (b:Multiset ℂ)) :
    Tendsto (fun q : ℝ => qPhiTerm (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q (((q:ℂ)-1)^qPhiExponent a b*z) n)
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genCoeff (a:Multiset ℂ) (b:Multiset ℂ) n*z^n)) := by
  sorry

/-- The analytic unilateral limit on the genuine classical convergence domain. -/
@[dlmf 17.4.E2]
theorem qPhi_classical_limit (a b : List ℂ) (z : ℂ)
    (hb : DLMF.Hypergeometric.genDenRegular (b:Multiset ℂ))
    (hr : a.length≤b.length+1) (hz : a.length=b.length+1 → ‖z‖<1) :
    Tendsto (fun q : ℝ => qPhi (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q (((q:ℂ)-1)^qPhiExponent a b*z))
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genHG (a:Multiset ℂ) (b:Multiset ℂ) z)) := by
  sorry

/-- The finite limit retains bottom poles that occur only after the final retained term. -/
@[dlmf 17.4.E2]
theorem qPhi_finite_classical_limit (a b : List ℂ) (z : ℂ) (N : ℕ)
    (hb : ∀ bi∈b, ∀ j<N, bi≠ -(j:ℂ)) :
    Tendsto (fun q : ℝ => qPhiPartial (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q (((q:ℂ)-1)^qPhiExponent a b*z) N)
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genFiniteHG N (a:Multiset ℂ) (b:Multiset ℂ) z)) := by
  sorry

/-- The bilateral limit is formal/coefficientwise; its analytic annulus collapses as q→1. -/
@[dlmf 17.4.E4]
theorem qPsi_coefficient_classical_limit (a b : List ℂ) (n : ℤ)
    (hlen : a.length=b.length)
    (ha : ∀ ai∈a, ∀ m : ℕ, ai≠(m+1:ℂ))
    (hb : DLMF.Hypergeometric.genDenRegular (b:Multiset ℂ)) :
    Tendsto (fun q : ℝ => qPsiTerm (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q 1 n)
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genBilateralCoeff (a:Multiset ℂ) (b:Multiset ℂ) n)) := by
  sorry

/-- The scalar coefficient of the general unilateral series. -/
def qPhiCoeff (a b : List ℂ) (q : ℂ) (n : ℕ) : ℂ := qPhiTerm a b q 1 n
/-- The variable enters each unilateral term as its natural power. -/
theorem qPhiTerm_eq_coeff_mul (a b : List ℂ) (q z : ℂ) (n : ℕ) :
    qPhiTerm a b q z n=qPhiCoeff a b q n*z^n := by
  simp [qPhiCoeff,qPhiTerm]
/-- Mathlib's formal scalar power series associated with the general q-series. -/
def qPhiPowerSeries (a b : List ℂ) (q : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (qPhiCoeff a b q)
/-- Convergence at a nonnegative real radius bounds the formal-series radius.
This uses Mathlib `FormalMultilinearSeries.le_radius_of_tendsto` directly. -/
theorem qPhiPowerSeries_radius_ge {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length+1) (r : ℝ≥0)
    (hz : a.length=b.length+1 → (r:ℝ)<1) :
    (r:ℝ≥0∞)≤(qPhiPowerSeries a b q).radius := by
  have hs := (qPhi_hasSum (z := (r:ℂ)) hq0 hq hb hr (by simpa using hz)).summable
  apply FormalMultilinearSeries.le_radius_of_tendsto (r := r)
  simpa [qPhiPowerSeries,FormalMultilinearSeries.ofScalars_norm,qPhiTerm_eq_coeff_mul,
    norm_mul,norm_pow,Complex.norm_of_nonneg r.property] using hs.tendsto_atTop_zero.norm
/-- The full q-series has the expected scalar power series on every admissible positive ball.
Upper parameters may be zero or terminating. -/
theorem qPhi_hasFPowerSeriesOnBall {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length+1) (r : ℝ≥0) (hr0 : 0<r)
    (hz : a.length=b.length+1 → (r:ℝ)<1) :
    HasFPowerSeriesOnBall (qPhi a b q) (qPhiPowerSeries a b q) 0 r := by
  refine ⟨qPhiPowerSeries_radius_ge hq0 hq hb hr r hz,by exact_mod_cast hr0,?_⟩
  intro z hzr
  have hz' : ‖z‖<(r:ℝ) := by
    exact_mod_cast (mem_eball_zero_iff.mp hzr)
  have hs := qPhi_hasSum (z := z) hq0 hq hb hr (fun h => hz'.trans (hz h))
  convert hs using 1
  · ext n
    simp [qPhiPowerSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,
      qPhiTerm_eq_coeff_mul,mul_comm]
  · simp

/-- Every convergent unilateral series is analytic on the open unit disk. -/
theorem qPhi_analytic_disc {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length+1) :
    AnalyticOnNhd ℂ (qPhi a b q) {z | ‖z‖<1} := by
  intro z hz
  obtain ⟨r,hzr,hr1⟩ := exists_between hz
  let R : ℝ≥0 := ⟨r,le_of_lt ((norm_nonneg z).trans_lt hzr)⟩
  have hR : 0<R := (norm_nonneg z).trans_lt hzr
  apply (qPhi_hasFPowerSeriesOnBall hq0 hq hb hr R hR (fun _ => hr1)).analyticAt_of_mem
  apply mem_eball_zero_iff.mpr
  exact_mod_cast hzr

/-- Unilateral series with at most as many upper as lower parameters are entire. -/
theorem qPhi_analytic_entire {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length) :
    AnalyticOnNhd ℂ (qPhi a b q) Set.univ := by
  intro z hz
  let R : ℝ≥0 := ⟨‖z‖+1,by positivity⟩
  have hR : 0<R := (norm_nonneg z).trans_lt (lt_add_one _)
  apply (qPhi_hasFPowerSeriesOnBall hq0 hq hb (by omega) R hR
    (fun h => False.elim (by omega))).analyticAt_of_mem
  apply mem_eball_zero_iff.mpr
  have : ‖z‖<‖z‖+1 := by linarith
  exact_mod_cast this

/-- The q-series has its explicit scalar Taylor series at the origin. -/
theorem qPhi_hasFPowerSeriesAt {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length+1) :
    HasFPowerSeriesAt (qPhi a b q) (qPhiPowerSeries a b q) 0 := by
  exact (qPhi_hasFPowerSeriesOnBall hq0 hq hb hr (1/2) (by norm_num)
    (fun _ => by norm_num)).hasFPowerSeriesAt
/-- Every Taylor derivative is its factorial times the explicit q-series coefficient.
This directly applies Mathlib's uniqueness of the scalar analytic expansion. -/
theorem qPhi_iteratedDeriv_zero {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length+1) (n : ℕ) :
    iteratedDeriv n (qPhi a b q) 0=(n.factorial:ℂ)*qPhiCoeff a b q n := by
  have hp := qPhi_hasFPowerSeriesAt hq0 hq hb hr
  have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simp only [qPhiPowerSeries,FormalMultilinearSeries.coeff_ofScalars] at hc
  have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simpa [mul_comm] using ((eq_div_iff hn).mp hc).symm

/-- zero phi zero. -/
@[dlmf 17.5.E1]
theorem zero_phi_zero {q : ℂ} (hq : ‖q‖<1) (z : ℂ) : qPhi [] [] q z=qPochhammerInf z q := by
  calc
    qPhi [] [] q z=∑' n : ℕ, q^(n.choose 2)*(-z)^n/qPochhammer q q n := by
      unfold qPhi
      apply tsum_congr
      intro n
      change (1/(1*qPochhammer q q n))*
        (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri (n:ℤ))^(1:ℤ))*z^n=
          q^(n.choose 2)*(-z)^n/qPochhammer q q n
      have htri : DLMF.QSeries.TripleProduct.tri (n:ℤ)=(n.choose 2:ℤ) := by
        simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast n 0).symm
      rw [htri,zpow_natCast,zpow_one,neg_pow]
      ring
    _ = _ := by simpa using tsum_qExp hq (-z)

/-- The infinite shifted factorial is entire in its first argument for a fixed base in the unit disk. -/
theorem qPochhammerInf_analytic {q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (fun a : ℂ => qPochhammerInf a q) Set.univ := by
  by_cases hq0 : q=0
  · subst q
    intro z hz
    have h : AnalyticAt ℂ (fun a : ℂ => 1-a) z := analyticAt_const.sub analyticAt_id
    simpa only [DLMF.QSeries.TripleProduct.qPochhammerInf_zero_right] using h
  · have h := qPhi_analytic_entire (a := []) (b := []) hq0 hq
      (by simp [qDenominatorRegular]) (by simp)
    rw [show qPhi [] [] q=(fun z => qPochhammerInf z q) from
      funext fun z => zero_phi_zero hq z] at h
    exact h

/-- Bilateral series are analytic on their actual open annulus, including valid lower zeros. -/
theorem qPsi_analytic_annulus {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hr : a.length≤b.length) :
    AnalyticOnNhd ℂ (qPsi a b q)
      {z | z≠0 ∧ ‖b.prod/(a.prod*z)‖<1 ∧ (a.length=b.length → ‖z‖<1)} := by
  sorry

/-- A holomorphic RHS germ continues the actual unilateral-series germ inside its domain.
This is a direct adapter of TauCeti's proved germ continuation API. -/
theorem qPhi_continuesInside_of_eq {a b : List ℂ} {q z₀ : ℂ} {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hz₀ : z₀∈U) (hF : AnalyticOnNhd ℂ F U)
    (heq : qPhi a b q=ᶠ[𝓝 z₀] F) : TauCeti.ContinuesInside (qPhi a b q) U z₀ := by
  exact (TauCeti.ContinuesInside.of_differentiableOn hU hF.differentiableOn).congr heq.symm

/-- A holomorphic RHS germ continues the actual bilateral-series germ inside its domain.
Only the germ in the convergence annulus is used, never a totalized value outside it. -/
theorem qPsi_continuesInside_of_eq {a b : List ℂ} {q z₀ : ℂ} {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hz₀ : z₀∈U) (hF : AnalyticOnNhd ℂ F U)
    (heq : qPsi a b q=ᶠ[𝓝 z₀] F) : TauCeti.ContinuesInside (qPsi a b q) U z₀ := by
  exact (TauCeti.ContinuesInside.of_differentiableOn hU hF.differentiableOn).congr heq.symm

end DLMF.QHypergeometric
