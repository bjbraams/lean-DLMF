/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Convergence

/-!
# Further basic hypergeometric transformations (DLMF §17.9)

The functions are actual series, with their common convergence regions stated.
Terminating transformations retain the full natural truncation parameter; no
condition on its size is imposed. Lower parameters and denominator products are
excluded from the q-lattice where the printed quotients have poles. The general
phase factor is the integer exponent in `Basic`, including the 3-phi-1 case.
Watson's terminating transformation is reused directly from `DLMF.Bailey`.
-/

@[expose] public noncomputable section
open Complex
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- Quotient of finite q-products, retaining all parameter repetitions. -/
def qProductRatio (N : ℕ) (a b : List ℂ) (q : ℂ) : ℂ :=
  qPochhammerList a q N / qPochhammerList b q N

/-- Quotient of convergent infinite q-products. -/
def qProductRatioInf (a b : List ℂ) (q : ℂ) : ℂ :=
  qPochhammerListInf a q / qPochhammerListInf b q

/-- DLMF 17.9.E1: qPhi2 to qPhi2 2. -/
@[dlmf 17.9.E1]
theorem qPhi2_to_qPhi2_2 (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c,a*z,z] q)
    (hz : ‖z‖<1) :
    qPhi [a,b] [c] q (z) =
      qProductRatioInf [z*a] [z] q * qPhi [a,c/b] [c,a*z] q (b*z) := by
  sorry

/-- DLMF 17.9.E2: qPhi2 terminating to qPhi3 1. -/
@[dlmf 17.9.E2]
theorem qPhi2_terminating_to_qPhi3_1 (n : ℕ) (b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [c,b*q^(1-(n:ℤ))/c] q) :
    qPhi [q^(-(n:ℤ)),b] [c] q (z) =
      qProductRatio n [c/b] [c] q * b^n * qPhi [q^(-(n:ℤ)),b,q/z] [b*q^(1-(n:ℤ))/c] q (z/c) := by
  sorry

/-- DLMF 17.9.E3: qPhi2 two qPhi3 2. -/
@[dlmf 17.9.E3]
theorem qPhi2_two_qPhi3_2 (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [c,b*z/c,z,c/(b*z),b*z,b*z*q/c,c*q/(b*z)] q)
    (hz : ‖z‖<1) :
    qPhi [a,b] [c] q (z) =
      qProductRatioInf [a*b*z/c] [b*z/c] q * qPhi [a,c/b,0] [c,c*q/(b*z)] q (q) + qProductRatioInf [a,b*z,c/b] [c,z,c/(b*z)] q * qPhi [z,a*b*z/c,0] [b*z,b*z*q/c] q (q) := by
  sorry

/-- DLMF 17.9.E3_5: qPhi2 two qPhi3 2 alternative. -/
@[dlmf 17.9.E3_5]
theorem qPhi2_two_qPhi3_2_alternative (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c], x≠0)
    (hden : QDenominatorRegular [c,c/(a*b),a*b/c,z,q*a*b/c,q*c/(a*b),0] q)
    (hz : ‖z‖<1) :
    qPhi [a,b] [c] q (z) =
      qProductRatioInf [c/a,c/b] [c,c/(a*b)] q * qPhi [a,b,a*b*z/c] [q*a*b/c,0] q (q) + qProductRatioInf [a,b,a*b*z/c] [c,a*b/c,z] q * qPhi [c/a,c/b,z] [q*c/(a*b),0] q (q) := by
  sorry

/-- DLMF 17.9.E4: qPhi2 terminating reverse. -/
@[dlmf 17.9.E4]
theorem qPhi2_terminating_reverse (n : ℕ) (b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [c,b*q^(1-(n:ℤ))/c,0] q) :
    qPhi [q^(-(n:ℤ)),b] [c] q (z) =
      qProductRatio n [c/b] [c] q * (b*z/q)^n * qPhi [q^(-(n:ℤ)),q/z,q^(1-(n:ℤ))/c] [b*q^(1-(n:ℤ))/c,0] q (q) := by
  sorry

/-- DLMF 17.9.E5: qPhi2 terminating sears. -/
@[dlmf 17.9.E5]
theorem qPhi2_terminating_sears (n : ℕ) (b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c], x≠0)
    (hden : QDenominatorRegular [c,b*q^(1-(n:ℤ))/c,0] q) :
    qPhi [q^(-(n:ℤ)),b] [c] q (z) =
      qProductRatio n [c/b] [c] q * qPhi [q^(-(n:ℤ)),b,b*z*q^(-(n:ℤ))/c] [b*q^(1-(n:ℤ))/c,0] q (q) := by
  sorry

/-- DLMF 17.9.E6: qPhi3 sears first. -/
@[dlmf 17.9.E6]
theorem qPhi3_sears_first (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c], x≠0)
    (hden : QDenominatorRegular [d,e,d*e/(a*b*c),d*e/(b*c)] q)
    (hz : ‖d*e/(a*b*c)‖<1)
    (he : ‖e/a‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [e/a,d*e/(b*c)] [e,d*e/(a*b*c)] q * qPhi [a,d/b,d/c] [d,d*e/(b*c)] q (e/a) := by
  sorry

/-- DLMF 17.9.E7: qPhi3 sears second. -/
@[dlmf 17.9.E7]
theorem qPhi3_sears_second (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c], x≠0)
    (hden : QDenominatorRegular [d,e,d*e/(a*b*c),d*e/(a*b),d*e/(b*c)] q)
    (hz : ‖d*e/(a*b*c)‖<1)
    (hb : ‖b‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [b,d*e/(a*b),d*e/(b*c)] [d,e,d*e/(a*b*c)] q * qPhi [d/b,e/b,d*e/(a*b*c)] [d*e/(a*b),d*e/(b*c)] q (b) := by
  sorry

/-- DLMF 17.9.E8: qPhi3 terminating first. -/
@[dlmf 17.9.E8]
theorem qPhi3_terminating_first (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,d], x≠0)
    (hden : QDenominatorRegular [d,e,d*e/(b*c)] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (q) =
      qProductRatio n [d*e/(b*c)] [e] q * (b*c/d)^n * qPhi [q^(-(n:ℤ)),d/b,d/c] [d,d*e/(b*c)] q (q) := by
  sorry

/-- DLMF 17.9.E9: qPhi3 terminating second. -/
@[dlmf 17.9.E9]
theorem qPhi3_terminating_second (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q^(1-(n:ℤ))/e] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (q) =
      qProductRatio n [e/c] [e] q * c^n * qPhi [q^(-(n:ℤ)),c,d/b] [d,c*q^(1-(n:ℤ))/e] q (b*q/e) := by
  sorry

/-- DLMF 17.9.E10: qPhi3 terminating third. -/
@[dlmf 17.9.E10]
theorem qPhi3_terminating_third (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q^(1-(n:ℤ))/e] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (d*e*q^n/(b*c)) =
      qProductRatio n [e/c] [e] q * qPhi [q^(-(n:ℤ)),c,d/b] [d,c*q^(1-(n:ℤ))/e] q (q) := by
  sorry

/-- DLMF 17.9.E11: qPhi3 terminating fourth. -/
@[dlmf 17.9.E11]
theorem qPhi3_terminating_fourth (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [c,d,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q^(1-(n:ℤ))/e,c*q^(1-(n:ℤ))/d] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (q) =
      qProductRatio n [e/c,d/c] [e,d] q * c^n * qPhi [q^(-(n:ℤ)),c,c*b*q^(1-(n:ℤ))/(d*e)] [c*q^(1-(n:ℤ))/e,c*q^(1-(n:ℤ))/d] q (q) := by
  sorry

/-- DLMF 17.9.E12: qPhi3 three term. -/
@[dlmf 17.9.E12]
theorem qPhi3_three_term (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,d,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q/d,q/a,e/(b*c),b*c*q/e,d/q,b*q/d,q^2/d,e*q/d,c*q/a] q)
    (hz : ‖d*e/(a*b*c)‖<1)
    (hb : ‖b*q/d‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [e/b,e/c,c*q/a,q/d] [e,c*q/d,q/a,e/(b*c)] q * qPhi [c,d/a,c*q/e] [c*q/a,b*c*q/e] q (b*q/d) - qProductRatioInf [q/d,e*q/d,b,c,d/a,d*e/(b*c*q),b*c*q^2/(d*e)] [d/q,e,b*q/d,c*q/d,q/a,e/(b*c),b*c*q/e] q * qPhi [a*q/d,b*q/d,c*q/d] [q^2/d,e*q/d] q (d*e/(a*b*c)) := by
  sorry

/-- DLMF 17.9.E13: qPhi3 connection. -/
@[dlmf 17.9.E13]
theorem qPhi3_connection (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,e], x≠0)
    (hden : QDenominatorRegular [d,e,e/(b*c),b*c/e,d*e/(a*b*c),b*c*q/e,d*e/(b*c),e*q/(b*c)] q)
    (hz : ‖d*e/(a*b*c)‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [e/b,e/c] [e,e/(b*c)] q * qPhi [d/a,b,c] [d,b*c*q/e] q (q) + qProductRatioInf [d/a,b,c,d*e/(b*c)] [d,e,b*c/e,d*e/(a*b*c)] q * qPhi [e/b,e/c,d*e/(a*b*c)] [d*e/(b*c),e*q/(b*c)] q (q) := by
  sorry

/-- DLMF 17.9.E14: qPhi4 balanced transformations. -/
@[dlmf 17.9.E14]
theorem qPhi4_balanced_transformations (n : ℕ) (a b c d e f q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,d,e,f], x≠0)
    (hden : QDenominatorRegular [d,e,f,a*q^(1-(n:ℤ))/e,a*q^(1-(n:ℤ))/f,e*f/(a*b),e*f/(a*c),e*f/(a*b*c),q^(1-(n:ℤ))/a] q)
    (hbal : d*e*f=a*b*c*q^(1-(n:ℤ))) :
    (qPhi [q^(-(n:ℤ)),a,b,c] [d,e,f] q (q)) = qProductRatio n [e/a,f/a] [e,f] q * a^n * qPhi [q^(-(n:ℤ)),a,d/b,d/c] [d,a*q^(1-(n:ℤ))/e,a*q^(1-(n:ℤ))/f] q (q) ∧
    (qPhi [q^(-(n:ℤ)),a,b,c] [d,e,f] q (q)) = qProductRatio n [a,e*f/(a*b),e*f/(a*c)] [e,f,e*f/(a*b*c)] q * qPhi [q^(-(n:ℤ)),e/a,f/a,e*f/(a*b*c)] [e*f/(a*b),e*f/(a*c),q^(1-(n:ℤ))/a] q (q) := by
  sorry

/-- DLMF 17.9.E16: nonterminating watson. -/
@[dlmf 17.9.E16]
theorem nonterminating_watson (a b c d e f q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,d,e,f], x≠0)
    (hden : QDenominatorRegular [a^(1/2:ℂ),-a^(1/2:ℂ),a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,a*q/(d*e*f),d*e*f/a,a^2*q^2/(b*c*d*e*f),d*e*f/(a*q),a^2*q^2/(b*d*e*f),a^2*q^2/(c*d*e*f),a*q^2/(d*e*f)] q)
    (hz : ‖a^2*q^2/(b*c*d*e*f)‖<1) :
    qPhi [a,q*a^(1/2:ℂ),-q*a^(1/2:ℂ),b,c,d,e,f] [a^(1/2:ℂ),-a^(1/2:ℂ),a*q/b,a*q/c,a*q/d,a*q/e,a*q/f] q (a^2*q^2/(b*c*d*e*f)) =
      qProductRatioInf [a*q,a*q/(d*e),a*q/(d*f),a*q/(e*f)] [a*q/d,a*q/e,a*q/f,a*q/(d*e*f)] q * qPhi [a*q/(b*c),d,e,f] [a*q/b,a*q/c,d*e*f/a] q (q) + qProductRatioInf [a*q,a*q/(b*c),d,e,f,a^2*q^2/(b*d*e*f),a^2*q^2/(c*d*e*f)] [a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,a^2*q^2/(b*c*d*e*f),d*e*f/(a*q)] q * qPhi [a*q/(d*e),a*q/(d*f),a*q/(e*f),a^2*q^2/(b*c*d*e*f)] [a^2*q^2/(b*d*e*f),a^2*q^2/(c*d*e*f),a*q^2/(d*e*f)] q (q) := by
  sorry

/-- DLMF 17.9.E17: qPhi3 terminating quadratic. -/
@[dlmf 17.9.E17]
theorem qPhi3_terminating_quadratic (n : ℕ) (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [a*q/b,a*q/c,z,a*z,q/z] q)
    (ha : a=q^(-(n:ℤ))) :
    qPhi [a,b,c] [a*q/b,a*q/c] q (a*q*z/(b*c)) =
      qProductRatioInf [a*z] [z] q * qPhi [a^(1/2:ℂ),-a^(1/2:ℂ),(a*q)^(1/2:ℂ),-(a*q)^(1/2:ℂ),a*q/(b*c)] [a*q/b,a*q/c,a*z,q/z] q (q) := by
  sorry

/-- DLMF 17.9.E18: qPhi4 square. -/
@[dlmf 17.9.E18]
theorem qPhi4_square (a b q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [z], x≠0)
    (hden : QDenominatorRegular [a*b*q^(1/2:ℂ),-a*b*q^(1/2:ℂ),-a*b,a^2*b^2] q)
    (hterm : QTerminating [a,b,a*b*z,a*b/z] q ∧ QTerminating [a^2,b^2,a*b,a*b*z,a*b/z] q) :
    qPhi [a,b,a*b*z,a*b/z] [a*b*q^(1/2:ℂ),-a*b*q^(1/2:ℂ),-a*b] q (q) ^ 2 =
      qPhi [a^2,b^2,a*b,a*b*z,a*b/z] [a*b*q^(1/2:ℂ),-a*b*q^(1/2:ℂ),-a*b,a^2*b^2] q (q) := by
  sorry

/-- DLMF 17.9.E19: mixed base even odd. -/
@[dlmf 17.9.E19]
theorem mixed_base_even_odd (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c,a*z] q)
    (hb : ‖b‖<1)
    (hz : ‖z‖<1) :
    (∑' n : ℕ, qPochhammer a (q^2) n * qPochhammer b q n * z^n / (qPochhammer (q^2) (q^2) n * qPochhammer c q n)) =
      qPochhammerInf b q * qPochhammerInf (a*z) (q^2) / (qPochhammerInf c q * qPochhammerInf z (q^2)) * (∑' n : ℕ, qPochhammer (c/b) q (2*n) * qPochhammer z (q^2) n * b^(2*n) / (qPochhammer q q (2*n) * qPochhammer (a*z) (q^2) n)) + qPochhammerInf b q * qPochhammerInf (a*z*q) (q^2) / (qPochhammerInf c q * qPochhammerInf (z*q) (q^2)) * (∑' n : ℕ, qPochhammer (c/b) q (2*n+1) * qPochhammer (z*q) (q^2) n * b^(2*n+1) / (qPochhammer q q (2*n+1) * qPochhammer (a*z*q) (q^2) n)) := by
  sorry

/-- DLMF 17.9.E20: mixed base general. -/
@[dlmf 17.9.E20]
theorem mixed_base_general (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c] q)
    (k : ℕ)
    (hk : 0<k)
    (hb : ‖b‖<1)
    (hz : ‖z‖<1)
    (hbase : QDenominatorRegular [a*z] (q^k)) :
    (∑' n : ℕ, qPochhammer a (q^k) n * qPochhammer b q (k*n) * z^n / (qPochhammer (q^k) (q^k) n * qPochhammer c q (k*n))) =
      qPochhammerInf b q * qPochhammerInf (a*z) (q^k) / (qPochhammerInf c q * qPochhammerInf z (q^k)) * (∑' n : ℕ, qPochhammer (c/b) q n * qPochhammer z (q^k) n * b^n / (qPochhammer q q n * qPochhammer (a*z) (q^k) n)) := by
  sorry

end DLMF.QHypergeometric
