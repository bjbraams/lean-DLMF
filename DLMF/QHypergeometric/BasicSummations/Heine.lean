/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Calculus
public import DLMFMathlib.Analysis.Complex.GeometricNewtonSeries
public import DLMFMathlib.Analysis.Complex.SeparatingContour
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import DLMF.QHypergeometric.BasicSummations.OnePhiZero

/-!
# Heine's transformations and related two-phi-one identities (DLMF 17.6.4–17.6.29)

The q-analogues of Kummer's theorem, Heine's three transformations, Fine's expansions,
nonterminating and mixed-base sums, connection and contiguous relations, the q-differential
equation, and the Jackson-integral and Mellin–Barnes representations of `₂φ₁`. Cancelled
product forms retain exceptional upper parameters whenever the left series is regular.

## Main results

* `q_even_heine`, `q_odd_heine`, `q_bailey_daum`: 17.6.4–17.6.5.
* `heine_first`, `heine_second`, `heine_third`: 17.6.6–17.6.8.
* `heine_contiguous_17` … `heine_contiguous_24`: the contiguous relations 17.6.17–17.6.24.
* `heine_qDifferentialEquation`: 17.6.27.
* `heine_jackson_integral`, `heine_mellin_barnes`: 17.6.28 and 17.6.29.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The Jackson expression in Heine's integral, kept separate from its removable parameter values. -/
def qHeineJacksonValue (q : ℝ) (a b c z : ℂ) : ℂ :=
  qGamma q c/(qGamma q b*qGamma q (c-b))*
    jacksonIntegral q 1 (fun t => t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a)
/-- The integrand in the Mellin–Barnes representation of two-phi-one. -/
def qHeineBarnesKernel (a b c q z s : ℂ) : ℂ :=
  qPochhammerListInf [q^(1+s),c*q^s] q/qPochhammerListInf [a*q^s,b*q^s] q*
    π*(-z)^s/Complex.sin (π*s)
/-- The denominator-pole set on the logarithmic q-plane in the Barnes representation. -/
def qHeineBarnesLeft (a b q : ℂ) : Set ℂ :=
  {s | qPochhammerListInf [a*q^s,b*q^s] q=0}
/-- The nonnegative-integer poles belonging to the right side of the Barnes contour. -/
def qHeineBarnesRight : Set ℂ := Set.range (fun n : ℕ => (n:ℂ))
/-- The cancelled product form retains b=±q^(-m) whenever the left series is regular. -/
@[dlmf 17.6.E4]
theorem q_even_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q‖<‖b^2‖)
    (hc : QDenominatorRegular [c] (q^2)) :
    qPhi [b^2,b^2/c] [c] (q^2) (c*q/b^2)=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
         qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  sorry

/-- A base-`q²` summation of `2φ1(b²,b²/c;cq²;q²,cq³/b²)` as a combination of infinite products
(DLMF 17.6.E4, E5). -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q^3‖<‖b^2‖)
    (hc : QDenominatorRegular [c*q^2] (q^2))
    (hd : qPochhammerInf (c*q/b^2) (q^2)≠0) :
    qPhi [b^2,b^2/c] [c*q^2] (q^2) (c*q^3/b^2)=
      qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
         qPochhammerInf b q*qPochhammerInf (-c*q/b) q) := by
  sorry

/-- The only additional common product zero inside the stated convergence domain is handled as a removable limit. -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine_removable {b q : ℂ} (hb : b≠0) (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : QDenominatorRegular [b^2*q] (q^2)) :
    Tendsto (fun c : ℂ => qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
       qPochhammerInf b q*qPochhammerInf (-c*q/b) q))
      (𝓝[≠] (b^2/q)) (𝓝 (qPhi [b^2,q] [b^2*q] (q^2) (q^2))) := by
  sorry

/-- The Bailey–Daum q-Kummer sum `2φ1(a,b;aq/b;q,-q/b)` as a product of infinite q-shifted
factorials (DLMF 17.6.E5). -/
@[dlmf 17.6.E5]
theorem q_bailey_daum {a b q : ℂ} (hq : ‖q‖<1) (hb : ‖q‖<‖b‖)
    (hc : QDenominatorRegular [a*q/b] q) :
    qPhi [a,b] [a*q/b] q (-q/b)=qPochhammerInf (-q) q*
      qPochhammerListInf [a*q,a*q^2/b^2] (q^2)/qPochhammerListInf [-q/b,a*q/b] q := by
  sorry

/-- Heine's first transformation of `2φ1(a,b;c;q,z)` into a multiple of `2φ1(c/b,z;az;q,b)` (DLMF
17.6.E6). -/
@[dlmf 17.6.E6]
theorem heine_first {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1) (hb0 : b≠0)
    (hc : QDenominatorRegular [c,a*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,a*z] q/qPochhammerListInf [c,z] q*
      qPhi [c/b,z] [a*z] q b := by
  rw [qPhi_eq_basicHG (by simp),qPhi_eq_basicHG (by simp)]
  simpa [qPochhammerListInf] using DLMF.QSeries.heine_transformation hq hz hb hb0
    (hc c (by simp)) (hc (a*z) (by simp))

/-- Heine's second transformation of `2φ1(a,b;c;q,z)` into a multiple of `2φ1(abz/c,b;bz;q,c/b)`
(DLMF 17.6.E7). -/
@[dlmf 17.6.E7]
theorem heine_second {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0) (hcb : ‖c‖<‖b‖)
    (hc : QDenominatorRegular [c,b*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [c/b,b*z] q/qPochhammerListInf [c,z] q*
      qPhi [a*b*z/c,b] [b*z] q (c/b) := by
  sorry

/-- Heine's third transformation: `2φ1(a,b;c;q,z) = (abz/c;q)_∞/(z;q)_∞ 2φ1(c/a,c/b;c;q,abz/c)`
(DLMF 17.6.E8). -/
@[dlmf 17.6.E8]
theorem heine_third {a b c q z : ℂ} (ha : a≠0) (hb : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc0 : c≠0) (habz : ‖a*b*z‖<‖c‖) (hc : QDenominatorRegular [c] q) :
    qPhi [a,b] [c] q z=qPochhammerInf (a*b*z/c) q/qPochhammerInf z q*
      qPhi [c/a,c/b] [c] q (a*b*z/c) := by
  sorry

/-- Fine's first expansion of `2φ1(q,aq;bq;q,z)` (DLMF 17.6.E9). -/
@[dlmf 17.6.E9]
theorem heine_fine_expansion {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q,a*z*q^2/b,a*q/b] q) :
    qPhi [q,a*q] [b*q] q z= -(1-b)*(a*q/b)/(1-a*q/b)*
      (∑' n : ℕ, qPochhammerList [a*q,a*z*q/b] q n*q^n/qPochhammer (a*z*q^2/b) q n)+
      qPochhammerListInf [a*q,a*z*q/b] q/qPochhammerInf (a*q/b) q*qPhi [q,0] [b*q] q z := by
  sorry

/-- Fine's second expansion: `(1-z) 2φ1(q,aq;bq;q,z)` as a series in `(b/a;q)_n (-az)^n
q^(n(n+1)/2)` (DLMF 17.6.E10). -/
@[dlmf 17.6.E10]
theorem heine_fine_expansion_second {a b q z : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=
      ∑' n : ℕ, qPochhammer (b/a) q n*(-a*z)^n*q^((n*(n+1))/2)/qPochhammerList [b*q,z*q] q n := by
  sorry

/-- Fine's third expansion of `(1-z)/(1-b) 2φ1(q,aq;bq;q,z)` (DLMF 17.6.E11). -/
@[dlmf 17.6.E11]
theorem heine_fine_expansion_third {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1)
    (hd : QDenominatorRegular [b*q,a*q/b] q) :
    (1-z)/(1-b)*qPhi [q,a*q] [b*q] q z=
      (∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n)*b^n/qPochhammerList [z*q,a*q/b] q n)-
      a*q*∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n+1)*(b*q)^n/
        (qPochhammer (z*q) q n*qPochhammer (a*q/b) q (n+1)) := by
  sorry

/-- Fine's fourth expansion of `(1-z) 2φ1(q,aq;bq;q,z)` as a well-poised type series (DLMF
17.6.E12). -/
@[dlmf 17.6.E12]
theorem heine_fine_expansion_fourth {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=∑' n : ℕ,
      qPochhammerList [a*q,a*z*q/b] q n/qPochhammerList [b*q,z*q] q n*
        (1-a*z*q^(2*n+1))*(b*z)^n*q^(n*n) := by
  sorry

/-- A nonterminating summation combining two `2φ1` series at argument `q` into infinite products
(DLMF 17.6.E13). -/
@[dlmf 17.6.E13]
theorem heine_nonterminating_sum {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0)
    (hd : QDenominatorRegular [c,q^2/c,c/q,a*q/c,b*q/c] q) :
    qPhi [a,b] [c] q q+qPochhammerListInf [q/c,a,b] q/qPochhammerListInf [c/q,a*q/c,b*q/c] q*
      qPhi [a*q/c,b*q/c] [q^2/c] q q=qPochhammerListInf [q/c,a*b*q/c] q/qPochhammerListInf [a*q/c,b*q/c] q := by
  sorry

/-- A mixed-base transformation between a series in bases `q` and `q²` and a `2φ1` in base `q²`
(DLMF 17.6.E14). -/
@[dlmf 17.6.E14]
theorem heine_mixed_base {a b q z : ℂ} (hq : ‖q‖<1)
    (hd : QDenominatorRegular [a*z*b,b*z] (q^2))
    (hD : qPochhammerListInf [z,a*z*b] (q^2)≠0)
    (hL : Summable (fun n : ℕ => qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n)))
    (hR : Summable (qPhiTerm [a,b] [b*z] (q^2) (z*q))) :
    (∑' n : ℕ, qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n))=
      qPochhammerListInf [a*z,b*z] (q^2)/qPochhammerListInf [z,a*z*b] (q^2)*qPhi [a,b] [b*z] (q^2) (z*q) := by
  sorry

/-- The first three-term connection formula for `2φ1(a,b;c;q,z)` (DLMF 17.6.E15). -/
@[dlmf 17.6.E15]
theorem heine_connection_first {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (hbc : ‖b*q‖<‖c‖)
    (hd : QDenominatorRegular [c,c*q/(a*z),q^2/c,a*z/c,q/a,c/q,b*q/c] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [a*b*z/c,q/c] q/qPochhammerListInf [a*z/c,q/a] q*
      qPhi [c/a,c*q/(a*b*z)] [c*q/(a*z)] q (b*q/c)-
      qPochhammerListInf [b,q/c,c/a,a*z/q,q^2/(a*z)] q/
        qPochhammerListInf [c/q,b*q/c,q/a,a*z/c,c*q/(a*z)] q*qPhi [a*q/c,b*q/c] [q^2/c] q z := by
  sorry

/-- The second three-term connection formula for `2φ1(a,b;c;q,z)`, in terms of `z ↦ cq/(abz)`
(DLMF 17.6.E16). -/
@[dlmf 17.6.E16]
theorem heine_connection_second {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (harg : ‖c*q‖<‖a*b*z‖)
    (hd : QDenominatorRegular [c,a*q/b,b*q/a,b/a,a/b,z,q/z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,c/a,a*z,q/(a*z)] q/qPochhammerListInf [c,b/a,z,q/z] q*
      qPhi [a,a*q/c] [a*q/b] q (c*q/(a*b*z))+
      qPochhammerListInf [a,c/b,b*z,q/(b*z)] q/qPochhammerListInf [c,a/b,z,q/z] q*
      qPhi [b,b*q/c] [b*q/a] q (c*q/(a*b*z)) := by
  sorry

/-- Heine's contiguous relation in the lower parameter `c/q` versus `c` (DLMF 17.6.E17). -/
@[dlmf 17.6.E17]
theorem heine_contiguous_17 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c/q] q) :
    qPhi [a,b] [c/q] q z-qPhi [a,b] [c] q z=c*z*(1-a)*(1-b)/((q-c)*(1-c))*qPhi [a*q,b*q] [c*q] q z := by
  have hc := qDenominatorRegular_of_div_q hq0 hd
  have hc' := qDenominatorRegular_mul_q hc
  have h1 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hc
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b*q) hq0 hq hz hc').mul_left
    (c*z*(1-a)*(1-b)/((q-c)*(1-c))))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  have hcq1 := one_sub_ne_zero_of_qDenominatorRegular hd
  have hqc : q-c≠0 := by
    intro h; apply hcq1; rw [show c=q by linear_combination -h]; field_simp; ring
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc n
    have hcn : 1-c*q^n≠0 := fun h => hc c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ' (c/q),div_mul_cancel₀ _ hq0,
      qPochhammer_succ c,qPochhammer_mul_q hc1,qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation in the upper parameter `aq` versus `a` (DLMF 17.6.E18). -/
@[dlmf 17.6.E18]
theorem heine_contiguous_18 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b] [c] q z-qPhi [a,b] [c] q z=a*z*(1-b)/(1-c)*qPhi [a*q,b*q] [c*q] q z := by
  have h1 := hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hd
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have hd' := qDenominatorRegular_mul_q hd
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b*q) hq0 hq hz hd').mul_left
    (a*z*(1-b)/(1-c)))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hc1 := one_sub_ne_zero_of_qDenominatorRegular hd
    have hcq := qPochhammer_ne_zero_of_qDenominatorRegular hq hd' n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ' c,
      qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation shifting `a` and `c` together (DLMF 17.6.E19). -/
@[dlmf 17.6.E19]
theorem heine_contiguous_19 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b] [c*q] q z-qPhi [a,b] [c] q z=z*(1-b)*(a-c)/((1-c)*(1-c*q))*qPhi [a*q,b*q] [c*q^2] q z := by
  have hc' := qDenominatorRegular_mul_q hd
  have hc'' : QDenominatorRegular [c*q^2] q := by
    simpa [pow_two,mul_assoc] using qDenominatorRegular_mul_q hc'
  have h1 := hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hc'
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b*q) hq0 hq hz hc'').mul_left
    (z*(1-b)*(a-c)/((1-c)*(1-c*q))))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hd
  have hcq1 := one_sub_ne_zero_of_qDenominatorRegular hc'
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc' n
    have hcn : 1-c*q*q^n≠0 := fun h => hc' (c*q) (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [show c*q^2=(c*q)*q by ring,qPochhammer_mul_q hcq1,
      qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' b,qPochhammer_succ (c*q),
      qPochhammer_succ' c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer (a*q) q n = A
    generalize qPochhammer (b*q) q n = B
    generalize qPochhammer (c*q) q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*q*Q = D1 at hcn ⊢
    generalize hD2 : 1-c*q = D2 at hcq1 ⊢
    generalize hD3 : 1-c = D3 at hc1 ⊢
    field_simp
    simp only [← hD0,← hD1,← hD3]
    ring

/-- Heine's contiguous relation for `(aq, b/q)` versus `(a, b)` (DLMF 17.6.E20). -/
@[dlmf 17.6.E20]
theorem heine_contiguous_20 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    qPhi [a*q,b/q] [c] q z-qPhi [a,b] [c] q z=z*(a-b/q)/(1-c)*qPhi [a*q,b] [c*q] q z := by
  have hc' := qDenominatorRegular_mul_q hd
  have h1 := hasSum_qPhi_two_one (a := a*q) (b := b/q) hq0 hq hz hd
  have h2 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h3 := hasSum_prependZero ((hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hc').mul_left
    (z*(a-b/q)/(1-c)))
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hd
  intro n
  cases n with
  | zero => simp [prependZero]
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc' n
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ (a*q),qPochhammer_succ' a,qPochhammer_succ' (b/q),div_mul_cancel₀ _ hq0,
      qPochhammer_succ b,qPochhammer_succ' c,qPochhammer_succ q,pow_succ z]
    field_simp
    ring

/-- Heine's contiguous relation `b(1-a)φ(aq,b) - a(1-b)φ(a,bq) = (b-a)φ(a,b)` (DLMF 17.6.E21). -/
@[dlmf 17.6.E21]
theorem heine_contiguous_21 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    b*(1-a)*qPhi [a*q,b] [c] q z-a*(1-b)*qPhi [a,b*q] [c] q z=(b-a)*qPhi [a,b] [c] q z := by
  have h1 := (hasSum_qPhi_two_one (a := a*q) (b := b) hq0 hq hz hd).mul_left (b*(1-a))
  have h2 := (hasSum_qPhi_two_one (a := a) (b := b*q) hq0 hq hz hd).mul_left (a*(1-b))
  have h3 := (hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd).mul_left (b-a)
  refine (h1.sub h2).unique (h3.congr_fun ?_)
  intro n
  have ha1 : (1-a)*qPochhammer (a*q) q n=qPochhammer a q n*(1-a*q^n) := by
    rw [← qPochhammer_succ',qPochhammer_succ]
  have hb1 : (1-b)*qPochhammer (b*q) q n=qPochhammer b q n*(1-b*q^n) := by
    rw [← qPochhammer_succ',qPochhammer_succ]
  have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
  have hqq := qPochhammer_self_ne_zero hq n
  field_simp
  linear_combination (b*qPochhammer b q n*z^n)*ha1-(a*qPochhammer a q n*z^n)*hb1

/-- Heine's contiguous relation between `φ(a,b/q)`, `φ(a/q,b)` and `φ(a,b)` (DLMF 17.6.E22). -/
@[dlmf 17.6.E22]
theorem heine_contiguous_22 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    a*(c-b)*qPhi [a,b/q] [c] q z-b*(c-a)*qPhi [a/q,b] [c] q z=(a-b)*(c-a*b*z/q)*qPhi [a,b] [c] q z := by
  have h0 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have h1 := (hasSum_qPhi_two_one (a := a) (b := b/q) hq0 hq hz hd).mul_left (a*(c-b))
  have h2 := (hasSum_qPhi_two_one (a := a/q) (b := b) hq0 hq hz hd).mul_left (b*(c-a))
  have h3 := (h0.mul_left ((a-b)*c)).sub (hasSum_prependZero (h0.mul_left ((a-b)*(a*b/q)*z)))
  have key := (h1.sub h2).unique (h3.congr_fun ?_)
  · rw [key]; ring
  intro n
  cases n with
  | zero => simp [prependZero]; ring
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
    have hcn : 1-c*q^n≠0 := fun h => hd c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' (b/q),qPochhammer_succ' (a/q),div_mul_cancel₀ _ hq0,div_mul_cancel₀ _ hq0,
      qPochhammer_succ a,qPochhammer_succ b,qPochhammer_succ c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*Q = D1 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1]
    ring

/-- Heine's three-term contiguous relation between `φ(a/q,b)`, `φ(aq,b)` and `φ(a,b)` (DLMF
17.6.E23). -/
@[dlmf 17.6.E23]
theorem heine_contiguous_23 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c] q) :
    q*(c-a)*qPhi [a/q,b] [c] q z+(1-a)*(c-a*b*z)*qPhi [a*q,b] [c] q z=(c*(1+q-a)-a*q+a^2*z-a*b*z)*qPhi [a,b] [c] q z := by
  have h0 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have hp := hasSum_qPhi_two_one_mul_q (a := a) (b := b) hq0 hq hz hd
  have h1 := (hasSum_qPhi_two_one (a := a/q) (b := b) hq0 hq hz hd).mul_left (q*(c-a))
  have hL := (h1.add (hp.mul_left c)).sub (hasSum_prependZero (hp.mul_left (a*b*z)))
  have hR := (h0.mul_left (c*(1+q-a)-a*q)).add (hasSum_prependZero (h0.mul_left ((a^2-a*b)*z)))
  have key := hL.unique (hR.congr_fun ?_)
  · linear_combination key
  intro n
  cases n with
  | zero => simp [prependZero,qPochhammer_one]; ring
  | succ n =>
    simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
    have hcn : 1-c*q^n≠0 := fun h => hd c (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_succ' (a/q),div_mul_cancel₀ _ hq0,qPochhammer_succ a q (n+1),
      qPochhammer_succ a q n,qPochhammer_succ b,qPochhammer_succ c,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    try simp only [pow_succ q n]
    generalize q^n = Q at hcn hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c*Q = D1 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1]
    ring

/-- Heine's three-term contiguous relation between `φ(;c/q)`, `φ(;cq)` and `φ(;c)` (DLMF
17.6.E24). -/
@[dlmf 17.6.E24]
theorem heine_contiguous_24 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [c/q] q) :
    (1-c)*(q-c)*(a*b*z-c)*qPhi [a,b] [c/q] q z+z*(c-a)*(c-b)*qPhi [a,b] [c*q] q z=(c-1)*(c*(q-c)+z*(c*a+c*b-a*b-a*b*q))*qPhi [a,b] [c] q z := by
  have hc := qDenominatorRegular_of_div_q hq0 hd
  have hc' := qDenominatorRegular_mul_q hc
  have h0 := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hc
  have hm := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hd
  have hp := hasSum_qPhi_two_one (a := a) (b := b) hq0 hq hz hc'
  have hL := ((hasSum_prependZero (hm.mul_left ((1-c)*(q-c)*(a*b)*z))).sub
    (hm.mul_left ((1-c)*(q-c)*c))).add (hasSum_prependZero (hp.mul_left ((c-a)*(c-b)*z)))
  have hR := (h0.mul_left ((c-1)*(c*(q-c)))).add
    (hasSum_prependZero (h0.mul_left ((c-1)*(c*a+c*b-a*b-a*b*q)*z)))
  have key := hL.unique (hR.congr_fun ?_)
  · linear_combination key
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  have hcq1 := one_sub_ne_zero_of_qDenominatorRegular hd
  intro n
  cases n with
  | zero => simp [prependZero]; ring
  | succ n =>
    simp only [prependZero]
    obtain ⟨c0,rfl⟩ : ∃ c0, c=c0*q := ⟨c/q,by field_simp⟩
    simp only [mul_div_cancel_right₀ _ hq0] at hd ⊢
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
    have hc01 : 1-c0≠0 := one_sub_ne_zero_of_qDenominatorRegular hd
    have hcn : 1-c0*q^n≠0 := fun h => hd c0 (by simp) n (by linear_combination -h)
    have hcn' : 1-c0*q*q^n≠0 := fun h => hc (c0*q) (by simp) n (by linear_combination -h)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    rw [qPochhammer_mul_q hc1,qPochhammer_succ (c0*q),qPochhammer_succ c0,qPochhammer_mul_q hc01,
      qPochhammer_succ a,qPochhammer_succ b,qPochhammer_succ q,pow_succ z]
    generalize qPochhammer a q n = A
    generalize qPochhammer b q n = B
    generalize qPochhammer c0 q n = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    generalize q^n = Q at hcn hcn' hqn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-c0*q*Q = D1 at hcn' ⊢
    generalize hD2 : 1-c0*Q = D2 at hcn ⊢
    generalize hD3 : 1-c0*q = D3 at hc1 ⊢
    generalize hD4 : 1-c0 = D4 at hc01 ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2,← hD3,← hD4]
    ring

/-- The `n`-th q-derivative of `z ↦ 2φ1(a,b;c;q,dz)` raises all parameters by `q^n` (DLMF
17.6.E25). -/
@[dlmf 17.6.E25]
theorem heine_qDerivative {a b c d q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖d*z‖<1)
    (hc : QDenominatorRegular [c] q) (n : ℕ) :
    qDerivIterate n q (fun w => qPhi [a,b] [c] q (w*d)) z=
      qPochhammerList [a,b] q n*d^n/(qPochhammer c q n*(1-q)^n)*qPhi [a*q^n,b*q^n] [c*q^n] q (d*z) :=
  qDerivIterate_qPhi_two_one hq0 hq hc n z hz

/-- The `n`-th q-derivative of `2φ1` weighted by the ratio of infinite products
`(z;q)_∞/(abz/c;q)_∞` (DLMF 17.6.E26). -/
@[dlmf 17.6.E26]
theorem heine_weighted_qDerivative {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0)
    (hc : QDenominatorRegular [c] q) (hD : qPochhammerInf (a*b*z/c) q≠0) (n : ℕ) :
    qDerivIterate n q (fun w => qPochhammerInf w q/qPochhammerInf (a*b*w/c) q*qPhi [a,b] [c] q w) z=
      ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (c^n*qPochhammer c q n*(1-q)^n)*qPochhammerInf (z*q^n) q/qPochhammerInf (a*b*z/c) q*
        qPhi [a,b] [c*q^n] q (z*q^n) := by
  sorry

/-- The second-order q-differential equation satisfied by `2φ1(a,b;c;q,z)` (DLMF 17.6.E27). -/
@[dlmf 17.6.E27]
theorem heine_qDifferentialEquation {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [c] q) :
    let F := fun w => qPhi [a,b] [c] q w
    z*(c-a*b*q*z)*qDerivIterate 2 q F z+
      ((1-c)/(1-q)+((1-a)*(1-b)-(1-a*b*q))/(1-q)*z)*qDerivExtended q F z-
      (1-a)*(1-b)/(1-q)^2*F z=0 := by
  intro F
  have hF : F=fun w => qPhi [a,b] [c] q (w*1) := funext fun w => by simp [F]
  have hz' : ‖1*z‖<1 := by simpa using hz
  have hD1 : qDerivExtended q F z=qDerivIterate 1 q F z := rfl
  rw [hD1,hF,qDerivIterate_qPhi_two_one hq0 hq hc 1 z hz',qDerivIterate_qPhi_two_one hq0 hq hc 2 z hz']
  simp only [mul_one,one_mul,one_pow]
  have h0 := hasSum_qPhi_two_one_shift (a := a) (b := b) hq0 hq hz hc 0
  have h1 := hasSum_qPhi_two_one_shift (a := a) (b := b) hq0 hq hz hc 1
  have h2 := hasSum_qPhi_two_one_shift (a := a) (b := b) hq0 hq hz hc 2
  set S0 := qPochhammer a q 0*qPochhammer b q 0/qPochhammer c q 0*qPhi [a*q^0,b*q^0] [c*q^0] q z
  set S1 := qPochhammer a q 1*qPochhammer b q 1/qPochhammer c q 1*qPhi [a*q^1,b*q^1] [c*q^1] q z
  set S2 := qPochhammer a q 2*qPochhammer b q 2/qPochhammer c q 2*qPhi [a*q^2,b*q^2] [c*q^2] q z
  have hL := ((((hasSum_prependZero (h2.mul_left (c*z))).sub
    (hasSum_prependZero (hasSum_prependZero (h2.mul_left (a*b*q*z^2))))).add
    (h1.mul_left (1-c))).add (hasSum_prependZero (h1.mul_left (((1-a)*(1-b)-(1-a*b*q))*z)))).sub
    (h0.mul_left ((1-a)*(1-b)))
  have hq1 : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hq
  have hc1 := one_sub_ne_zero_of_qDenominatorRegular hc
  have hcq : 1-c*q≠0 := one_sub_ne_zero_of_qDenominatorRegular (qDenominatorRegular_mul_q hc)
  have key := hL.unique (hasSum_zero.congr_fun ?_)
  · have e : z*(c-a*b*q*z)*(qPochhammerList [a,b] q 2/(qPochhammer c q 2*(1-q)^2)*
        qPhi [a*q^2,b*q^2] [c*q^2] q z)+((1-c)/(1-q)+((1-a)*(1-b)-(1-a*b*q))/(1-q)*z)*
        (qPochhammerList [a,b] q 1/(qPochhammer c q 1*(1-q)^1)*qPhi [a*q^1,b*q^1] [c*q^1] q z)-
        (1-a)*(1-b)/(1-q)^2*qPhi [a,b] [c] q z=
        (c*z*S2-a*b*q*z^2*S2+(1-c)*S1+((1-a)*(1-b)-(1-a*b*q))*z*S1-(1-a)*(1-b)*S0)/(1-q)^2 := by
      simp only [S0,S1,S2,qPochhammerList,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
        mul_one,pow_zero,qPochhammer_zero]
      field_simp
      ring
    rw [e,key,zero_div]
  intro n
  rcases n with _ | _ | n
  · simp [prependZero,qPochhammer_one]
    field_simp
    ring
  · simp [prependZero]
    simp only [qPochhammer_succ _ _ 1,qPochhammer_one,pow_one]
    generalize hD0 : 1-q = D0 at hq1 ⊢
    generalize hD1 : 1-c = D1 at hc1 ⊢
    generalize hD2 : 1-c*q = D2 at hcq ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2]
    ring
  · simp only [prependZero]
    have hcc := qPochhammer_ne_zero_of_qDenominatorRegular hq hc (n+2)
    have hqq := qPochhammer_self_ne_zero hq n
    have hqn : 1-q*q^n≠0 := by simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n
    have hqn1 : 1-q*q^(n+1)≠0 := by
      simpa [pow_succ,mul_comm] using qPochhammerInf_pow_succ_ne_zero hq (n+1)
    have hcn : 1-c*q^(n+2)≠0 := fun h => hc c (by simp) (n+2) (by linear_combination -h)
    rw [show n+1+2=(n+2)+1 by ring,show n+1+1=n+2 by ring,Nat.add_zero,
      qPochhammer_succ a q (n+2),qPochhammer_succ b q (n+2),qPochhammer_succ c q (n+2),
      qPochhammer_succ q q (n+1),qPochhammer_succ q q n]
    generalize qPochhammer a q (n+2) = A
    generalize qPochhammer b q (n+2) = B
    generalize qPochhammer c q (n+2) = C at hcc ⊢
    generalize qPochhammer q q n = P at hqq ⊢
    rw [pow_succ z (n+1),pow_succ z n,show q^(n+2)=q^n*q*q by ring,show q^(n+1)=q^n*q by ring] at *
    generalize q^n = Q at hqn hqn1 hcn ⊢
    generalize hD0 : 1-q*Q = D0 at hqn ⊢
    generalize hD1 : 1-q*(Q*q) = D1 at hqn1 ⊢
    generalize hD2 : 1-c*(Q*q*q) = D2 at hcn ⊢
    field_simp
    simp only [← hD0,← hD1,← hD2]
    ring

/-- As `q → 1⁻`, the iterated q-derivatives of `2φ1(q^a,q^b;q^c;q,z)` tend to the derivatives of
the Gauss function `F(a,b;c;z)`. -/
theorem heine_classical_derivative_limit {a b c z : ℂ} (hc : ∀ n : ℕ, c≠ -(n:ℂ)) (hz : ‖z‖<1) (n : ℕ) :
    Tendsto (fun q : ℝ => qDerivIterate n q
      (fun w => qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q w) z)
      (𝓝[<] 1) (𝓝 (iteratedDeriv n (ordinaryHypergeometric a b c) z)) := by
  sorry

/-- As `q → 1⁻`, the coefficients of Heine's q-differential equation tend to those of the Gauss
hypergeometric equation. -/
theorem heine_qDifferentialEquation_classical_coefficients (a b c z : ℂ) :
    Tendsto (fun q : ℝ =>
      (z*((q:ℂ)^c-(q:ℂ)^(a+b+1)*z),
       (1-(q:ℂ)^c)/(1-q)+((1-(q:ℂ)^a)*(1-(q:ℂ)^b)-(1-(q:ℂ)^(a+b+1)))/(1-q)*z,
       -(1-(q:ℂ)^a)*(1-(q:ℂ)^b)/(1-q)^2))
      (𝓝[<] 1) (𝓝 (z*(1-z),c-(a+b+1)*z,-a*b)) := by
  have hc := tendsto_ofReal_cpow_one c
  have habc := tendsto_ofReal_cpow_one (a+b+1)
  have hb1 := tendsto_ofReal_cpow_one b
  have nc := tendsto_qNumber_one c
  have na := tendsto_qNumber_one a
  have nb := tendsto_qNumber_one b
  have nabc := tendsto_qNumber_one (a+b+1)
  refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ ?_)
  · have h := (hc.sub (habc.mul_const z)).const_mul z
    simpa using h
  · have h := nc.add (((na.mul ((tendsto_const_nhds (x := (1:ℂ))).sub hb1)).sub nabc).mul_const z)
    simp only [sub_self,mul_zero,zero_sub] at h
    convert h using 2 with q
    · by_cases hq : (1:ℂ)-q=0
      · simp [hq]
      field_simp
    · ring
  · have h := (na.mul nb).neg
    convert h using 2 with q
    · by_cases hq : (1:ℂ)-q=0
      · simp [hq]
      field_simp
    · ring

/-- Jackson integral representation of `2φ1(q^a,q^b;q^c;q,z)`, the q-analogue of Euler's integral
(DLMF 17.6.E28). -/
@[dlmf 17.6.E28]
theorem heine_jackson_integral {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {a b c z : ℂ}
    (hb : 0<b.re) (hz : ‖z‖<1)
    (hc : QDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q) :
    qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q z=
      qGamma q c/(qGamma q b*qGamma q (c-b))*
      jacksonIntegral q 1 (fun t => t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a) := by
  sorry

/-- The q-Mellin–Barnes integral representation of `2φ1(a,b;c;q,z)` (DLMF 17.6.E29). -/
@[dlmf 17.6.E29]
theorem heine_mellin_barnes {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz0 : z≠0) (hz : ‖z‖<1)
    (harg : |Complex.arg (-z)|<π) (hc : QDenominatorRegular [c] q)
    (L : ℝ → ℂ) (hL : ContDiff ℝ 1 L) (htail : Complex.HasVerticalTails L)
    (hsep : Complex.SeparatesPoleSets L (qHeineBarnesLeft a b q) qHeineBarnesRight)
    (hleft : Complex.StaysAwayFrom L (qHeineBarnesLeft a b q))
    (hright : Complex.StaysAwayFrom L qHeineBarnesRight) :
    Integrable (fun t : ℝ => qHeineBarnesKernel a b c q z (L t)*deriv L t) ∧
    qPhi [a,b] [c] q z= -1/(2*π*I)*qPochhammerListInf [a,b] q/qPochhammerListInf [q,c] q*
      ∫ t : ℝ, qHeineBarnesKernel a b c q z (L t)*deriv L t := by
  sorry

/-- The one-phi-zero product gives continuation of the actual series germ from zero. -/
theorem one_phi_zero_continues {a q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (qOnePhiZeroContinuation a q) {z | qPochhammerInf z q≠0} ∧
    (qPhi [a] [] q=ᶠ[𝓝 0] qOnePhiZeroContinuation a q) ∧
    TauCeti.ContinuesInside (qPhi [a] [] q) {z | qPochhammerInf z q≠0} 0 := by
  have hF := one_phi_zero_continuation_analytic (a := a) hq
  have hcont : Continuous (fun z : ℂ => qPochhammerInf z q) :=
    continuousOn_univ.mp (qPochhammerInf_analytic hq).continuousOn
  have hU : IsOpen {z : ℂ | qPochhammerInf z q≠0} := isOpen_ne_fun hcont continuous_const
  have h0 : (0:ℂ)∈{z : ℂ | qPochhammerInf z q≠0} := by simp [qPochhammerInf]
  have heq : qPhi [a] [] q=ᶠ[𝓝 0] qOnePhiZeroContinuation a q := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)] with z hz
    simpa only [qOnePhiZeroContinuation] using one_phi_zero (a := a) hq (by simpa using hz)
  exact ⟨hF,heq,qPhi_continuesInside_of_eq hU hF heq⟩

/-- The Jackson representation at Gamma-factor poles is its regular-parameter limit. -/
@[dlmf 17.6.E28]
theorem heine_jackson_parameter_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    {a b c₀ z : ℂ} (hb : 0<b.re) (hz : ‖z‖<1)
    (hc₀ : QDenominatorRegular [(q:ℂ)^c₀] q) :
    Tendsto (fun c : ℂ => qHeineJacksonValue q a b c z)
      (𝓝[{c : ℂ | QDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q}] c₀)
      (𝓝 (qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c₀] q z)) := by
  sorry

end DLMF.QHypergeometric
