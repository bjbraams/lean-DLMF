/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations

/-!
# q-elementary functions and Carlitz polynomials (DLMF §17.3)

DLMF scales the two q-exponentials by1−q. Their product definitions retain analytic
continuation, while the series statements below retain their actual convergence domains.
The existing Jackson calculus, shifted factorials and Gaussian polynomial are reused.
The q-elementary series use the proved Heine/Euler q-series and Mathlib's even/odd
HasSum decomposition; all norm bounds retain the original complex convergence domains.

The Carlitz Stirling polynomial is defined by its polynomial recurrence, so the values at
q=0 and q=1 are removable extensions rather than totalized0/0 values of the closed formula.
The Eulerian expression likewise uses geometric polynomials at these removable points.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The scaled little q-exponential, including its meromorphic product continuation. -/
@[dlmf 17.3.E1]
def qExp (q x : ℂ) : ℂ := (qPochhammerInf ((1-q)*x) q)⁻¹
/-- The scaled big q-exponential, an entire product in its argument when |q|<1. -/
@[dlmf 17.3.E2]
def qExpBig (q x : ℂ) : ℂ := qPochhammerInf (-(1-q)*x) q
/-- The little q-sine. -/
@[dlmf 17.3.E3]
def qSin (q x : ℂ) : ℂ := (qExp q (I*x)-qExp q (-I*x))/(2*I)
/-- The big q-sine. -/
@[dlmf 17.3.E4]
def qSinBig (q x : ℂ) : ℂ := (qExpBig q (I*x)-qExpBig q (-I*x))/(2*I)
/-- The little q-cosine. -/
@[dlmf 17.3.E5]
def qCos (q x : ℂ) : ℂ := (qExp q (I*x)+qExp q (-I*x))/2
/-- The big q-cosine. -/
@[dlmf 17.3.E6]
def qCosBig (q x : ℂ) : ℂ := (qExpBig q (I*x)+qExpBig q (-I*x))/2
/-- Carlitz's q-Bernoulli expression, with the principal power q^(rx). -/
@[dlmf 17.3.E7]
def qBernoulli (n : ℕ) (x q : ℂ) : ℂ :=
  (1-q)^((1:ℤ)-n)*∑ j∈range (n+1), (-1:ℂ)^j*(n.choose j:ℂ)*
    (j+1:ℂ)/(1-q^(j+1))*q^((j:ℂ)*x)
/-- Carlitz's Eulerian polynomial, using the removable geometric-polynomial q-number. -/
def qEulerian (m s : ℕ) (q : ℂ) : ℂ :=
  q^((DLMF.QSeries.TripleProduct.tri ((s:ℤ)-m)+DLMF.QSeries.TripleProduct.tri s).toNat)*
    ∑ j∈range (s+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q (m+1) j*
      (∑ k∈range (s-j), q^k)^m
/-- Carlitz's second-kind q-Stirling polynomial, including removable endpoint values. -/
def qStirlingSecond (q : ℂ) : ℕ → ℕ → ℂ
  | 0,0 => 1
  | 0,_+1 => 0
  | _+1,0 => 0
  | m+1,s+1 => qStirlingSecond q m s+(∑ k∈range (s+1), q^k)*qStirlingSecond q m (s+1)
/-- Even and odd projections of a convergent q-series and its alternating partner.
This directly uses Mathlib `HasSum.even_add_odd` and summable injective subsequences. -/
private lemma qSeries_even_odd {c : ℕ → ℂ} {u v : ℂ} (hu : HasSum c u)
    (hv : HasSum (fun n => (-1:ℂ)^n*c n) v) :
    HasSum (fun n => c (2*n)) ((u+v)/2) ∧
    HasSum (fun n => c (2*n+1)) ((u-v)/2) := by
  have he : HasSum (fun n => c (2*n)) (∑' n, c (2*n)) := by
    simpa only [Function.comp_def] using (hu.summable.comp_injective
      (fun n m h => by dsimp only at h; omega : Function.Injective (fun n : ℕ => 2*n))).hasSum
  have ho : HasSum (fun n => c (2*n+1)) (∑' n, c (2*n+1)) := by
    simpa only [Function.comp_def] using (hu.summable.comp_injective
      (fun n m h => by dsimp only at h; omega : Function.Injective (fun n : ℕ => 2*n+1))).hasSum
  have h1 := (he.even_add_odd ho).unique hu
  have he' : HasSum (fun n => (-1:ℂ)^(2*n)*c (2*n)) (∑' n, c (2*n)) := by
    simpa [pow_mul] using he
  have ho' : HasSum (fun n => (-1:ℂ)^(2*n+1)*c (2*n+1)) (-(∑' n, c (2*n+1))) := by
    simpa [pow_add,pow_mul] using ho.neg
  have h2 := (he'.even_add_odd ho').unique hv
  have hev : (∑' n, c (2*n))=(u+v)/2 := by linear_combination (1/2:ℂ)*h1+(1/2:ℂ)*h2
  have hov : (∑' n, c (2*n+1))=(u-v)/2 := by linear_combination (1/2:ℂ)*h1-(1/2:ℂ)*h2
  exact ⟨hev ▸ he,hov ▸ ho⟩

/-- qExp hasSum. -/
@[dlmf 17.3.E1]
theorem qExp_hasSum {q x : ℂ} (hq : ‖q‖<1) (hx : ‖(1-q)*x‖<1) : HasSum (fun n : ℕ => (1-q)^n*x^n/qPochhammer q q n) (qExp q x) := by
  have hs := (summable_q_binomial_series (a := 0) hq hx).hasSum
  rw [← q_binomial_theorem hq hx] at hs
  convert hs using 1
  · ext n
    simp [qPochhammer_zero_param,mul_pow,div_eq_mul_inv,mul_comm]
  · simp [qExp,qPochhammerInf]

/-- qExpBig hasSum. -/
@[dlmf 17.3.E2]
theorem qExpBig_hasSum {q : ℂ} (hq : ‖q‖<1) (x : ℂ) : HasSum (fun n : ℕ => (1-q)^n*q^(n.choose 2)*x^n/qPochhammer q q n) (qExpBig q x) := by
  by_cases hq0 : q=0
  · subst q
    have hs : HasSum (fun n : ℕ => (0:ℂ)^(n.choose 2)*x^n) (∑ n∈range 2, (0:ℂ)^(n.choose 2)*x^n) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      have hn2 : 2≤n := by have hh : ¬n<2 := fun h => hn (mem_range.mpr h); omega
      have hchoose : n.choose 2≠0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
      simp [zero_pow hchoose]
    simpa [qExpBig,DLMF.QSeries.TripleProduct.qPochhammerInf_zero_right,qPochhammer_zero_param,
      sum_range_succ] using hs
  · have hs := qPhi_hasSum (a := []) (b := []) (z := -(1-q)*x) hq0 hq
      (by simp [qDenominatorRegular]) (by simp) (by simp)
    rw [zero_phi_zero hq] at hs
    convert hs using 1
    · ext n
      change (1-q)^n*q^(n.choose 2)*x^n/qPochhammer q q n=
        (1/(1*qPochhammer q q n))*
          (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri (n:ℤ))^(1:ℤ))*(-(1-q)*x)^n
      have hp : (-(1-q)*x)^n=(-1:ℂ)^n*(1-q)^n*x^n := by
        rw [mul_pow,neg_pow]
      rw [qTri_nat,zpow_natCast,zpow_one,hp]
      have hsign : (-1:ℂ)^n*(-1:ℂ)^n=1 := by rw [← mul_pow]; norm_num
      linear_combination (norm := ring_nf) -(q^(n.choose 2)*(1-q)^n*x^n/qPochhammer q q n)*hsign
    · simp [qExpBig,neg_mul]

/-- qSin hasSum. -/
@[dlmf 17.3.E3]
theorem qSin_hasSum {q x : ℂ} (hq : ‖q‖<1) (hx : ‖(1-q)*x‖<1) : HasSum (fun n : ℕ => (1-q)^(2*n+1)*(-1:ℂ)^n*x^(2*n+1)/qPochhammer q q (2*n+1)) (qSin q x) := by
  have hi : ‖(1-q)*(I*x)‖<1 := by
    rw [show (1-q)*(I*x)=I*((1-q)*x) by ring,norm_mul,norm_I,one_mul]
    exact hx
  have hn : ‖(1-q)*(-I*x)‖<1 := by
    rw [show (1-q)*(-I*x)= -I*((1-q)*x) by ring,norm_mul,norm_neg,norm_I,one_mul]
    exact hx
  have hu := qExp_hasSum hq hi
  have hv := qExp_hasSum hq hn
  have hv' : HasSum (fun n : ℕ => (-1:ℂ)^n*((1-q)^n*(I*x)^n/qPochhammer q q n))
      (qExp q (-I*x)) := by
    convert hv using 1
    ext n
    have hp : (-I*x)^n=(-1:ℂ)^n*(I*x)^n := by rw [neg_mul,neg_pow]
    rw [hp]
    ring
  have hs := (qSeries_even_odd hu hv').2.div_const I
  convert hs using 1
  · ext n
    have hp : (I*x)^(2*n+1)=(-1:ℂ)^n*I*x^(2*n+1) := by
      rw [mul_pow,pow_add,pow_mul,I_sq,pow_one]
    rw [hp]
    field_simp [qPochhammer_self_ne_zero hq (2*n+1)] <;> ring
  · simp [qSin,div_div]

/-- qSinBig hasSum. -/
@[dlmf 17.3.E4]
theorem qSinBig_hasSum {q : ℂ} (hq : ‖q‖<1) (x : ℂ) : HasSum (fun n : ℕ => (1-q)^(2*n+1)*q^(n*(2*n+1))*(-1:ℂ)^n*x^(2*n+1)/qPochhammer q q (2*n+1)) (qSinBig q x) := by
  have hu := qExpBig_hasSum hq (I*x)
  have hv := qExpBig_hasSum hq (-I*x)
  have hv' : HasSum (fun n : ℕ => (-1:ℂ)^n*((1-q)^n*q^(n.choose 2)*(I*x)^n/qPochhammer q q n))
      (qExpBig q (-I*x)) := by
    convert hv using 1
    ext n
    have hp : (-I*x)^n=(-1:ℂ)^n*(I*x)^n := by rw [neg_mul,neg_pow]
    rw [hp]
    ring
  have hs := (qSeries_even_odd hu hv').2.div_const I
  convert hs using 1
  · ext n
    have hp : (I*x)^(2*n+1)=(-1:ℂ)^n*I*x^(2*n+1) := by
      rw [mul_pow,pow_add,pow_mul,I_sq,pow_one]
    rw [hp]
    have hc : (2*n+1).choose 2=n*(2*n+1) := by
      rw [Nat.choose_two_right,show 2*n+1-1=2*n by omega,
        show (2*n+1)*(2*n)=(n*(2*n+1))*2 by ring,Nat.mul_div_cancel] <;> norm_num
    rw [hc]
    field_simp [qPochhammer_self_ne_zero hq (2*n+1)] <;> ring
  · simp [qSinBig,div_div]

/-- qCos hasSum. -/
@[dlmf 17.3.E5]
theorem qCos_hasSum {q x : ℂ} (hq : ‖q‖<1) (hx : ‖(1-q)*x‖<1) : HasSum (fun n : ℕ => (1-q)^(2*n)*(-1:ℂ)^n*x^(2*n)/qPochhammer q q (2*n)) (qCos q x) := by
  have hi : ‖(1-q)*(I*x)‖<1 := by
    rw [show (1-q)*(I*x)=I*((1-q)*x) by ring,norm_mul,norm_I,one_mul]
    exact hx
  have hn : ‖(1-q)*(-I*x)‖<1 := by
    rw [show (1-q)*(-I*x)= -I*((1-q)*x) by ring,norm_mul,norm_neg,norm_I,one_mul]
    exact hx
  have hu := qExp_hasSum hq hi
  have hv := qExp_hasSum hq hn
  have hv' : HasSum (fun n : ℕ => (-1:ℂ)^n*((1-q)^n*(I*x)^n/qPochhammer q q n))
      (qExp q (-I*x)) := by
    convert hv using 1
    ext n
    have hp : (-I*x)^n=(-1:ℂ)^n*(I*x)^n := by rw [neg_mul,neg_pow]
    rw [hp]
    ring
  have hs := (qSeries_even_odd hu hv').1
  convert hs using 1
  · ext n
    have hp : (I*x)^(2*n)=(-1:ℂ)^n*x^(2*n) := by rw [mul_pow,pow_mul,I_sq]
    rw [hp]
    ring
  · simp [qCos]

/-- qCosBig hasSum. -/
@[dlmf 17.3.E6]
theorem qCosBig_hasSum {q : ℂ} (hq : ‖q‖<1) (x : ℂ) : HasSum (fun n : ℕ => (1-q)^(2*n)*q^(n*(2*n-1))*(-1:ℂ)^n*x^(2*n)/qPochhammer q q (2*n)) (qCosBig q x) := by
  have hu := qExpBig_hasSum hq (I*x)
  have hv := qExpBig_hasSum hq (-I*x)
  have hv' : HasSum (fun n : ℕ => (-1:ℂ)^n*((1-q)^n*q^(n.choose 2)*(I*x)^n/qPochhammer q q n))
      (qExpBig q (-I*x)) := by
    convert hv using 1
    ext n
    have hp : (-I*x)^n=(-1:ℂ)^n*(I*x)^n := by rw [neg_mul,neg_pow]
    rw [hp]
    ring
  have hs := (qSeries_even_odd hu hv').1
  convert hs using 1
  · ext n
    have hp : (I*x)^(2*n)=(-1:ℂ)^n*x^(2*n) := by rw [mul_pow,pow_mul,I_sq]
    rw [hp]
    have hc : (2*n).choose 2=n*(2*n-1) := by
      rw [Nat.choose_two_right,show (2*n)*(2*n-1)=(n*(2*n-1))*2 by ring,Nat.mul_div_cancel] <;> norm_num
    rw [hc]
    ring
  · simp [qCosBig]

section qaR4_elementary_helpers
open Polynomial
/-- The integer triangular number is nonnegative. -/
lemma qaR4_tri_nonneg (n : ℤ) : 0≤DLMF.QSeries.TripleProduct.tri n := by
  have h := DLMF.QSeries.TripleProduct.tri_mul_two n
  have : 0≤n*(n-1) := by
    rcases le_or_gt n 0 with h0 | h0
    · nlinarith
    · nlinarith
  omega

/-- The Gaussian polynomial as an element of `ℂ[X]`. -/
noncomputable def qaR4_qBinomPoly : ℕ → ℕ → Polynomial ℂ
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => qaR4_qBinomPoly n k+X^(k+1)*qaR4_qBinomPoly n (k+1)

/-- Evaluation of the Gaussian polynomial. -/
lemma qaR4_qBinomPoly_eval (q : ℂ) (n k : ℕ) : (qaR4_qBinomPoly n k).eval q=qBinom q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [qaR4_qBinomPoly,qBinom]
  | succ n ih =>
    cases k with
    | zero => simp [qaR4_qBinomPoly]
    | succ k => simp [qaR4_qBinomPoly,qBinom_succ_succ,ih]

/-- The second-kind q-Stirling numbers as elements of `ℂ[X]`. -/
noncomputable def qaR4_qStirlingPoly : ℕ → ℕ → Polynomial ℂ
  | 0,0 => 1
  | 0,_+1 => 0
  | _+1,0 => 0
  | m+1,s+1 => qaR4_qStirlingPoly m s+(∑ k∈range (s+1), X^k)*qaR4_qStirlingPoly m (s+1)

/-- The unnormalized Carlitz sum `∑(-1)^j q^{C(j,2)}[s,j](1-q^{s-j})^m`. -/
noncomputable def qaR4_carlitzG (q : ℂ) (m s : ℕ) : ℂ :=
  ∑ j∈range (s+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q s j*(1-q^(s-j))^m

/-- The recursion of the Carlitz sum. -/
lemma qaR4_carlitzG_succ (q : ℂ) (m s : ℕ) :
    qaR4_carlitzG q (m+1) (s+1)=(1-q^(s+1))*(qaR4_carlitzG q m (s+1)+q^s*qaR4_carlitzG q m s) := by
  unfold qaR4_carlitzG
  have hsplit : ∀ j∈range (s+1+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q (s+1) j*(1-q^(s+1-j))^(m+1)=
      (1-q^(s+1))*((-1:ℂ)^j*q^(j.choose 2)*qBinom q (s+1) j*(1-q^(s+1-j))^m)-
      (-1:ℂ)^j*q^(j.choose 2)*q^(s+1-j)*((1-q^j)*qBinom q (s+1) j)*(1-q^(s+1-j))^m := by
    intro j hj
    have hjs : j≤s+1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have e : q^(s+1)=q^(s+1-j)*q^j := by rw [← pow_add,Nat.sub_add_cancel hjs]
    rw [pow_succ (1-q^(s+1-j)) m,e]
    ring
  rw [sum_congr rfl hsplit,sum_sub_distrib,← mul_sum,sum_range_succ' (fun j => (-1:ℂ)^j*q^(j.choose 2)*
    q^(s+1-j)*((1-q^j)*qBinom q (s+1) j)*(1-q^(s+1-j))^m)]
  simp only [pow_zero,sub_self,zero_mul,mul_zero,add_zero]
  have hterm : ∀ i∈range (s+1), (-1:ℂ)^(i+1)*q^((i+1).choose 2)*q^(s+1-(i+1))*
      ((1-q^(i+1))*qBinom q (s+1) (i+1))*(1-q^(s+1-(i+1)))^m=
      -((1-q^(s+1))*q^s*((-1:ℂ)^i*q^(i.choose 2)*qBinom q s i*(1-q^(s-i))^m)) := by
    intro i hi
    have his : i≤s := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [qaR4_qBinom_absorb q s i,show s+1-(i+1)=s-i by omega]
    have e : q^(i.choose 2+i)*q^(s-i)=q^(i.choose 2)*q^s := by
      rw [← pow_add,← pow_add]; congr 1; omega
    rw [show (i+1).choose 2=i.choose 2+i by rw [Nat.choose_succ_succ',Nat.choose_one_right]; ring]
    linear_combination (-(-1:ℂ)^i*(1-q^(s+1))*qBinom q s i*(1-q^(s-i))^m)*e
  rw [sum_congr rfl hterm,sum_neg_distrib,← mul_sum]
  ring

end qaR4_elementary_helpers

/-- qEulerian closed. -/
@[dlmf 17.3.E8]
theorem qEulerian_closed {q : ℂ} (hq1 : q≠1) (m s : ℕ) : qEulerian m s q=q^(DLMF.QSeries.TripleProduct.tri ((s:ℤ)-m)+DLMF.QSeries.TripleProduct.tri s)*(∑ j∈range (s+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q (m+1) j*(1-q^(s-j))^m/(1-q)^m) := by
  unfold qEulerian
  have hn : 0≤DLMF.QSeries.TripleProduct.tri ((s:ℤ)-m)+DLMF.QSeries.TripleProduct.tri s :=
    add_nonneg (qaR4_tri_nonneg _) (qaR4_tri_nonneg _)
  rw [← zpow_natCast,Int.toNat_of_nonneg hn]
  congr 1
  apply sum_congr rfl
  intro j _
  have hq : q-1≠0 := sub_ne_zero.mpr hq1
  have hq' : 1-q≠0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [geom_sum_eq hq1,div_pow]
  rw [show (q^(s-j)-1)^m/(q-1)^m=(1-q^(s-j))^m/(1-q)^m by
    rw [show q^(s-j)-1=-(1-q^(s-j)) by ring,show q-1=-(1-q) by ring,neg_pow,neg_pow (1-q)]
    field_simp]
  ring

/-- qStirling closed. -/
@[dlmf 17.3.E9]
theorem qStirling_closed {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (m s : ℕ) : qStirlingSecond q m s=q^(-(s.choose 2:ℤ))*(1-q)^s/qPochhammer q q s*(∑ j∈range (s+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q s j*(1-q^(s-j))^m/(1-q)^m) := by
  rw [← sum_div]
  change _=q^(-(s.choose 2:ℤ))*(1-q)^s/qPochhammer q q s*(qaR4_carlitzG q m s/(1-q)^m)
  have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
  induction m generalizing s with
  | zero =>
    cases s with
    | zero => simp [qStirlingSecond,qaR4_carlitzG]
    | succ s =>
      have h := qPochhammer_eq_sum_qBinom 1 q (s+1)
      rw [qPochhammer_succ',sub_self,zero_mul] at h
      simp only [one_pow,mul_one] at h
      simp only [qStirlingSecond,qaR4_carlitzG,pow_zero,mul_one]
      rw [show ∑ j∈range (s+1+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q (s+1) j=
        ∑ k∈range (s+1+1), qBinom q (s+1) k*(-1)^k*q^(k.choose 2) from
          sum_congr rfl fun k _ => by ring,← h]
      simp
  | succ m ih =>
    cases s with
    | zero => simp [qStirlingSecond,qaR4_carlitzG]
    | succ s =>
      rw [qStirlingSecond,ih,ih,qaR4_carlitzG_succ,geom_sum_eq (fun h => by simp [h] at hq)]
      have hqs := qPochhammer_self_ne_zero hq s
      have hqn : 1-q*q^s≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq s
      have hc : (s+1).choose 2=s.choose 2+s := by rw [Nat.choose_succ_succ',Nat.choose_one_right]; ring
      rw [qPochhammer_succ,hc]
      push_cast
      rw [neg_add,zpow_add₀ hq0,zpow_neg,zpow_neg]
      simp only [zpow_natCast]
      have hq1' : q-1≠0 := fun h => hq1 (by linear_combination -h)
      rw [pow_succ q s] at *
      generalize qaR4_carlitzG q m (s+1) = A
      generalize qaR4_carlitzG q m s = B
      generalize qPochhammer q q s = P at hqs ⊢
      field_simp
      ring

/-- qEulerian polynomial. -/
theorem qEulerian_polynomial (m s : ℕ) : ∃ P : Polynomial ℂ, ∀ q : ℂ, qEulerian m s q=P.eval q := by
  open Polynomial in
  refine ⟨X^((DLMF.QSeries.TripleProduct.tri ((s:ℤ)-m)+DLMF.QSeries.TripleProduct.tri s).toNat)*
    ∑ j∈range (s+1), C ((-1:ℂ)^j)*X^(j.choose 2)*qaR4_qBinomPoly (m+1) j*
      (∑ k∈range (s-j), X^k)^m,fun q => ?_⟩
  simp [qEulerian,eval_finsetSum,qaR4_qBinomPoly_eval]

/-- qStirling polynomial. -/
theorem qStirling_polynomial (m s : ℕ) : ∃ P : Polynomial ℂ, ∀ q : ℂ, qStirlingSecond q m s=P.eval q := by
  refine ⟨qaR4_qStirlingPoly m s,fun q => ?_⟩
  induction m generalizing s with
  | zero => cases s <;> simp [qaR4_qStirlingPoly,qStirlingSecond]
  | succ m ih =>
    cases s with
    | zero => simp [qaR4_qStirlingPoly,qStirlingSecond]
    | succ s => simp [qaR4_qStirlingPoly,qStirlingSecond,ih,Polynomial.eval_finsetSum]

/-- qBernoulli polynomial in qpow. -/
theorem qBernoulli_polynomial_in_qpow {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) : ∃ P : Polynomial ℂ, P.natDegree≤n ∧ ∀ x : ℂ, qBernoulli n x q=P.eval (q^x) := by
  open Polynomial in
  refine ⟨∑ j∈range (n+1), C ((1-q)^((1:ℤ)-n)*((-1:ℂ)^j*(n.choose j:ℂ)*(j+1:ℂ)/(1-q^(j+1))))*X^j,
    ?_,fun x => ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    have hjn : j≤n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    exact (natDegree_C_mul_X_pow_le _ _).trans hjn
  · simp only [qBernoulli,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,mul_sum]
    apply sum_congr rfl
    intro j _
    rw [cpow_nat_mul]
    ring

/-- qBernoulli rational integer argument. -/
theorem qBernoulli_rational_integer_argument (n : ℕ) (x : ℤ) : ∃ P Q : Polynomial ℂ, ∀ q : ℂ, q≠0 → ‖q‖<1 → Q.eval q≠0 ∧ qBernoulli n x q=P.eval q/Q.eval q := by
  classical
  open Polynomial in
  refine ⟨(1-X)*∑ j∈range (n+1), C ((-1:ℂ)^j*(n.choose j:ℂ)*(j+1:ℂ))*X^(((j:ℤ)*x+n*|x|).toNat)*
      ∏ i∈(range (n+1)).erase j, (1-X^(i+1)),
    (1-X)^n*(∏ i∈range (n+1), (1-X^(i+1)))*X^(n*x.natAbs),fun q hq0 hq => ?_⟩
  have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
  have hqi : ∀ i : ℕ, (1:ℂ)-q^(i+1)≠0 := fun i => by
    apply one_sub_ne_zero_of_norm_lt_one
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hQ : ((1-Polynomial.X : Polynomial ℂ)^n*(∏ i∈range (n+1), (1-Polynomial.X^(i+1) : Polynomial ℂ))*Polynomial.X^(n*x.natAbs)).eval q
      =(1-q)^n*(∏ i∈range (n+1), (1-q^(i+1)))*q^(n*x.natAbs) := by
    simp [Polynomial.eval_prod]
  have hQne : (1-q)^n*(∏ i∈range (n+1), (1-q^(i+1)))*q^(n*x.natAbs)≠0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq1) (prod_ne_zero_iff.mpr fun i _ => hqi i))
      (pow_ne_zero _ hq0)
  refine ⟨hQ ▸ hQne,?_⟩
  rw [hQ,eq_div_iff hQne]
  simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,
    Polynomial.eval_finsetSum,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_prod]
  unfold qBernoulli
  have hz : (1-q)^((1:ℤ)-n)*(1-q)^n=1-q := by
    rw [zpow_sub₀ hq1,zpow_one,zpow_natCast]; field_simp
  have hterm : ∀ j∈range (n+1), (-1:ℂ)^j*(n.choose j:ℂ)*(j+1:ℂ)/(1-q^(j+1))*q^((j:ℂ)*(x:ℂ))*
      ((∏ i∈range (n+1), (1-q^(i+1)))*q^(n*x.natAbs))=
      (-1:ℂ)^j*(n.choose j:ℂ)*(j+1:ℂ)*q^(((j:ℤ)*x+n*|x|).toNat)*∏ i∈(range (n+1)).erase j, (1-q^(i+1)) := by
    intro j hj
    have hjn : j≤n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [← mul_prod_erase _ _ hj]
    have hcp : q^((j:ℂ)*(x:ℂ))=q^((j:ℤ)*x) := by
      rw [← cpow_intCast]; push_cast; rfl
    have hnn : 0≤(j:ℤ)*x+n*|x| := by
      have : |(j:ℤ)*x|≤n*|x| := by
        rw [abs_mul,Nat.abs_cast]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjn) (abs_nonneg _)
      linarith [neg_abs_le ((j:ℤ)*x)]
    have hpow : q^((j:ℤ)*x)*q^(n*x.natAbs)=q^(((j:ℤ)*x+n*|x|).toNat) := by
      rw [← zpow_natCast,← zpow_natCast,← zpow_add₀ hq0,Int.toNat_of_nonneg hnn]
      congr 1; push_cast; rw [Int.abs_eq_natAbs]
    rw [hcp,← hpow]
    have := hqi j
    field_simp
  calc (1-q)^((1:ℤ)-n)*(∑ j∈range (n+1), (-1:ℂ)^j*(n.choose j:ℂ)*(j+1:ℂ)/(1-q^(j+1))*q^((j:ℂ)*(x:ℂ)))*
        ((1-q)^n*(∏ i∈range (n+1), (1-q^(i+1)))*q^(n*x.natAbs))
      =((1-q)^((1:ℤ)-n)*(1-q)^n)*∑ j∈range (n+1), (-1:ℂ)^j*(n.choose j:ℂ)*(j+1:ℂ)/(1-q^(j+1))*
        q^((j:ℂ)*(x:ℂ))*((∏ i∈range (n+1), (1-q^(i+1)))*q^(n*x.natAbs)) := by
          rw [mul_sum,sum_mul,mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
    _ = _ := by rw [hz,sum_congr rfl hterm]

end DLMF.QHypergeometric
