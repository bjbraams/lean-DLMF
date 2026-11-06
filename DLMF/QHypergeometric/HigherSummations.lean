/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bailey
public import DLMF.QHypergeometric.Dixon
public import DLMF.QHypergeometric.WhippleSummation
public import DLMF.QHypergeometric.QuadraticSummation
public import DLMF.QHypergeometric.QuadraticCompanion
public import DLMF.QHypergeometric.PfaffSaalschutz
public import DLMF.QHypergeometric.ParitySummation
public import DLMF.QHypergeometric.Convergence
public import DLMF.QHypergeometric.BasicSummations
public import DLMF.QHypergeometric.TwoPhiTwoSums
public import DLMF.QHypergeometric.BibasicBilateral
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Higher basic summations (DLMF §17.7)

This file proves the summation formulas of DLMF §17.7 (the `₂φ₂` sums 17.7.1–17.7.3 are in
`DLMF.QHypergeometric.TwoPhiTwoSums`): the `q`-Pfaff–Saalschütz
and `q`-Dixon sums, very-well-poised `₄φ₃`, `₆φ₅` and `₈φ₇` sums, the `q`-Karlsson–Minton
formulas and bibasic sums, together with counterexamples to two printed formulas.

## Main definitions

* `qMintonUpper`, `qMintonLower`, `qMintonWeight`: the parameters of the `q`-Karlsson–Minton
  formulas.
* `sixTerm`: the terms of the terminating very-well-poised `₆φ₅` sum.
* `bibasicDifferencePrinted`: the expression printed in DLMF 17.7.23.

## Main results

* `q_pfaff_saalschutz`, `nonterminating_saalschutz`: DLMF 17.7.4–17.7.5.
* `q_dixon_terminating`: the terminating `q`-Dixon sum (DLMF 17.7.6), collected in
  `DLMF.QHypergeometric.Dixon` with its cancelled-product extension.
* `eight_phi_seven_quadratic_sum`, `four_phi_three_parity`, `eight_phi_seven_even_sum`,
  `four_phi_three_infinite_product`: DLMF 17.7.8–17.7.11 (the `₄φ₃` sum 17.7.7 is
  `four_phi_three_sum` in `DLMF.QHypergeometric.VeryWellPoisedSums`).
* `four_phi_three_base_square_first`, `four_phi_three_base_square_second`:
  DLMF 17.7.12–17.7.13.
* `jackson_eight_phi_seven`: Jackson's `₈φ₇` summation (DLMF 17.7.14).
* `six_phi_five_terminating`, `nonterminating_eight_phi_seven`: DLMF 17.7.16–17.7.17; the
  nonterminating `₆φ₅` sum 17.7.15 is `six_phi_five_sum` in
  `DLMF.QHypergeometric.VeryWellPoisedSums`.
* `q_karlsson_minton`, `q_karlsson_minton_zero_corrected`: DLMF 17.7.18 and the corrected
  17.7.19.
* `bibasic_gosper`, `bibasic_gasper`, `bibasic_bilateral_finite`: DLMF 17.7.20–17.7.22.
* `bibasic_difference_corrected`: the corrected DLMF 17.7.23.
* `karlsson_printed_counter`, `bibasic_printed_counter`: counterexamples to the printed
  DLMF 17.7.19 and 17.7.23.

## Implementation notes

Finite sums retain parameter poles occurring only after the final retained term. Infinite
sums retain their actual convergence disks. Cleared products handle regular zero upper
parameters without evaluating `0` times an infinite product quotient.

The corrected DLMF 17.7.19 follows Gasper–Rahman, Basic Hypergeometric Series, (1.9.7), with
argument `a⁻¹q^{-Σm}`. The corrected DLMF 17.7.23 follows George Gasper, Lecture Notes for an
Introductory Minicourse on q-Series (1995), (4.1.23), with `p` and `q` interchanged:
https://sites.math.northwestern.edu/~george/preprints/ggLecNotesq-Series/ggLecNotesq-Series.pdf
The first denominator is `(p;p)_k` and the final shifted-factorial base is `p`.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- Shifted upper parameters for the q-Karlsson–Minton formulas. -/
def qMintonUpper (p : List (ℂ × ℕ)) (q : ℂ) : List ℂ := p.map fun x => x.1*q^x.2
/-- The corresponding unshifted lower parameters. -/
def qMintonLower (p : List (ℂ × ℕ)) : List ℂ := p.map Prod.fst
/-- Total nonnegative parameter displacement. -/
def qMintonWeight (p : List (ℂ × ℕ)) : ℕ := (p.map Prod.snd).sum
/-- The square-root-product cancellation in the four-phi-three sum. -/
def qFourPhiThreeValue (a b c q : ℂ) : ℂ :=
  let r := Complex.sqrt a
  let t := Complex.sqrt q
  qPochhammerListInf [r*t,-r*t,-r*q,q*r/b,q*r/c,a*q/(b*c)] q/
    qPochhammerListInf [a*q/b,a*q/c,q*r/(b*c)] q
/-- Pointwise definedness of integer shifted factorials before taking ratios. -/
def QIntPochhammerListDefined (p : List ℂ) (q : ℂ) (k : ℤ) : Prop :=
  0≤k ∨ ∀ a∈p, qPochhammer (a*q^k) q (-k).toNat≠0
attribute [local fun_prop] continuous_qPochhammer

/-- The nonterminating q-Saalschütz sum, combining two balanced `3φ2` series at argument `q` (DLMF
17.7.E5). -/
@[dlmf 17.7.E5]
theorem nonterminating_saalschutz {a b c e f q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (he : e≠0) (hf : f≠0) (hbal : e*f=a*b*c*q)
    (hd : QDenominatorRegular [e,f,q^2/e,q*f/e,e/q,a*q/e,b*q/e,c*q/e] q) :
    qPhi [a,b,c] [e,f] q q+
      qPochhammerListInf [q/e,a,b,c,q*f/e] q/qPochhammerListInf [e/q,a*q/e,b*q/e,c*q/e,f] q*
        qPhi [a*q/e,b*q/e,c*q/e] [q^2/e,q*f/e] q q=
      qPochhammerListInf [q/e,f/a,f/b,f/c] q/qPochhammerListInf [a*q/e,b*q/e,c*q/e,f] q := by
  sorry

/-- A quadratic very-well-poised `8φ7` summation with `ℓ = -c√(ab/q)` (DLMF 17.7.E8). -/
@[dlmf 17.7.E8]
theorem eight_phi_seven_quadratic_sum {a b c q ell : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc : c≠0)
    (hell : ell= -c*Complex.sqrt (a*b/q)) (hz : ‖ell*q‖<‖a*b‖)
    (hd : QDenominatorRegular
        [Complex.sqrt ell, -Complex.sqrt ell, ell*q/a, ell*q/b, ell*q/c, -ell*q/c, c^2] q) :
    qPhi [ell,q*Complex.sqrt ell,-q*Complex.sqrt ell,a,b,c,-c,ell*q/c^2]
      [Complex.sqrt ell,-Complex.sqrt ell,ell*q/a,ell*q/b,ell*q/c,-ell*q/c,c^2] q (-ell*q/(a*b))=
      qPochhammerListInf [ell*q,c^2/ell] q*qPochhammerListInf [a*q,b*q,c^2*q/a,c^2*q/b] (q^2)/
        (qPochhammerListInf [ell*q/a, ell*q/b] q*qPochhammerListInf
            [q, a*b*q, c^2*q, c^2*q/(a*b)] (q^2)) := by
  sorry

/-- A terminating `4φ3` summation at argument `q` whose value depends on the parity of `n` (DLMF
17.7.E9). -/
@[dlmf 17.7.E9]
theorem four_phi_three_parity {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [Complex.sqrt (a*q),-Complex.sqrt (a*q),c^2] q n) :
    qPhi [q^(-(n:ℤ)),a*q^n,c,-c] [Complex.sqrt (a*q),-Complex.sqrt (a*q),c^2] q q=
      if Odd n then 0 else qPochhammer q (q^2) (n/2)*
        ((range (n/2)).prod (fun j => c^2-a*q^(2*j+1)))/
        qPochhammerList [a*q,c^2*q] (q^2) (n/2) := by
  exact ParitySummation.four_phi_three_parity hq0 hq n hd

/-- A very-well-poised `8φ7` summation with parameters built from `-c` (DLMF 17.7.E10). -/
@[dlmf 17.7.E10]
theorem eight_phi_seven_even_sum {a c d q : ℂ} (ha : a≠0) (hd0 : d≠0) (hq : ‖q‖<1) (hc : ‖c‖<1)
    (hd : QDenominatorRegular [Complex.sqrt (-c),-Complex.sqrt (-c),-c*q/a,-a*c,-q,c*q/d,c*d] q) :
    qPhi [-c,q*Complex.sqrt (-c),-q*Complex.sqrt (-c),a,q/a,c,-d,-q/d]
      [Complex.sqrt (-c),-Complex.sqrt (-c),-c*q/a,-a*c,-q,c*q/d,c*d] q c=
      qPochhammerListInf [-c,-c*q] q*qPochhammerListInf [a*c*d,a*c*q/d,c*d*q/a,c*q^2/(a*d)] (q^2)/
        qPochhammerListInf [c*d,c*q/d,-a*c,-c*q/a] q := by
  sorry

/-- A terminating balanced `4φ3` with parameters `q^(-n), q^(n+1), c, -c` summed by infinite
products (DLMF 17.7.E11). -/
@[dlmf 17.7.E11]
theorem four_phi_three_infinite_product {c e q : ℂ} (he : e≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegular [e,c^2*q/e,-q] q) :
    qPhi [q^(-(n:ℤ)),q^(n+1),c,-c] [e,c^2*q/e,-q] q q=
      q^((n+1).choose 2)*qPochhammerListInf
          [e*q^(-(n:ℤ)), e*q^(n+1), c^2*q^(1-(n:ℤ))/e, c^2*q^(n+2)/e] (q^2)/
        qPochhammerListInf [e,c^2*q/e] q := by
  exact WhippleSummation.four_phi_three_infinite_product he hq0 hq n hd

/-- The cleared product retains the regular upper parameter a=0. -/
@[dlmf 17.7.E12]
theorem four_phi_three_base_square_first {a b q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [b,b*q,a^2*q^2] (q^2) n) :
    qPhi [a,a*q,b^2*q^(2*n),q^(-(2*n:ℤ))] [b,b*q,a^2*q^2] (q^2) (q^2)=
      qPochhammer (-q) q n*((range n).prod (fun j => a-b*q^j))/qPochhammerList [-a*q,b] q n := by
  exact QuadraticSummation.first_quadratic_sum hq0 hq n hd

/-- The n=0 removable quotient is 1, and the cleared product retains a=0. -/
@[dlmf 17.7.E13]
theorem four_phi_three_base_square_second {a b q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : QDenominatorRegularThrough [b,b*q,a^2] (q^2) n) :
    qPhi [a,a*q,b^2*q^(2*(n:ℤ)-2),q^(-(2*n:ℤ))] [b,b*q,a^2] (q^2) (q^2)=
      if n=0 then 1 else qPochhammer (-q) q n*((range n).prod (fun j => a-b*q^j))*(1-b*q^((n:ℤ)-1))/
        (qPochhammerList [-a,b] q n*(1-b*q^(2*(n:ℤ)-1))) := by
  exact QuadraticCompanion.second_quadratic_sum hq0 hq n hd

/-- The very-well-poised factor of an `₈φ₇` term as the unit-Bailey numerator. -/
theorem veryWellPoised_factor_eq_unitD {a q : ℂ} (k : ℕ) (hk : k = 0 ∨ (a ≠ 1 ∧
    qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0)) :
    qPochhammer a q k * qPochhammer (q*Complex.sqrt a) q k * qPochhammer (-q*Complex.sqrt a) q k /
      (qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k) =
    DLMF.Bailey.unitD a q k := by
  rcases hk with rfl | ⟨ha, hk⟩
  · simp [DLMF.Bailey.unitD]
  have hs : (Complex.sqrt a)^2 = a := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
  have h1 := DLMF.Bailey.qPochhammer_sqrt_factor (q := q) hs k
  have h2 := DLMF.Bailey.qPochhammer_mul_one_sub_pow a q k
  have h1a : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  rw [div_eq_iff hk]
  apply mul_left_cancel₀ h1a
  linear_combination qPochhammer a q k * h1 + qPochhammer (Complex.sqrt a) q k *
    qPochhammer (-Complex.sqrt a) q k * h2

/-- Jackson's `₈φ₇` terms are the rational terms of Watson's transformation. -/
private lemma qPhiTerm_jackson_eq_watsonR8 {a b c d e q : ℂ} (hq0 : q≠0) (n : ℕ)
    (hbcde : b*c*d*e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ))) (k : ℕ)
    (hk : k = 0 ∨ (a ≠ 1 ∧
      qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0)) :
    qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q k =
    DLMF.Bailey.watsonR8 a b c d e q n k := by
  have hz : a^2*q^2*q^n/(b*c*d*e) = q := by
    rw [div_eq_iff hbcde]
    have : a^2*q = b*c*d*e*q^(-(n:ℤ)) := hbal
    rw [zpow_neg, zpow_natCast] at this
    field_simp at this
    linear_combination q*this
  have hu := veryWellPoised_factor_eq_unitD k hk
  set R := qPochhammer b q k * qPochhammer c q k * qPochhammer d q k * qPochhammer e q k *
      qPochhammer (q^(-(n:ℤ))) q k / (qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k *
      qPochhammer (a*q/d) q k * qPochhammer (a*q/e) q k * qPochhammer (a*q^(n+1)) q k *
      qPochhammer q q k) * q^k with hR
  calc _ = qPochhammer a q k * qPochhammer (q*Complex.sqrt a) q k *
        qPochhammer (-q*Complex.sqrt a) q k /
        (qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k) * R := by
        simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil, hR]
        norm_num
        ring
    _ = _ := by
        rw [hu, hR, DLMF.Bailey.watsonR8, hz, zpow_neg, zpow_natCast, inv_pow,
          show a*q^(n+1) = a*q*q^n by ring]
        ring

/-- Jackson's sum when Watson's balanced `₄φ₃` has a regular cancelled parameter. -/
private lemma jackson_sum_of_regular {a b c d e q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hb : b≠0) (hc : c≠0) (hd : d≠0) (he : e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ)))
    (hS : qPochhammer (Complex.sqrt a) q n * qPochhammer (-Complex.sqrt a) q n ≠ 0)
    (hB : qPochhammer (a*q/b) q n ≠ 0) (hC : qPochhammer (a*q/c) q n ≠ 0)
    (hD : qPochhammer (a*q/d) q n ≠ 0) (hE : qPochhammer (a*q/e) q n ≠ 0)
    (hN : qPochhammer (a*q^(n+1)) q n ≠ 0) (hY : qPochhammer (a*q/(b*c)) q n ≠ 0) :
    ∑ k ∈ range (n+1), qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q k =
    qPochhammerList [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q n/
        qPochhammerList [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q n := by
  have hqn : q^(-(n:ℤ)) ≠ 0 := zpow_ne_zero _ hq0
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hbal
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) he) hqn) hbal.symm
  have hbcde : b*c*d*e ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) he
  -- Step A: the terms are Watson's rational terms
  have hA : ∀ k ∈ range (n+1), qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q k =
      DLMF.Bailey.watsonR8 a b c d e q n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    refine qPhiTerm_jackson_eq_watsonR8 hq0 n hbcde hbal k ?_
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact Or.inl h0
    · right
      have h1 : qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0 :=
        mul_ne_zero (qPochhammer_ne_zero_of_le (left_ne_zero_of_mul hS) hkn)
          (qPochhammer_ne_zero_of_le (right_ne_zero_of_mul hS) hkn)
      refine ⟨fun h1a => ?_, h1⟩
      have h2 : qPochhammer (Complex.sqrt a) q 1 * qPochhammer (-Complex.sqrt a) q 1 ≠ 0 :=
        mul_ne_zero (qPochhammer_ne_zero_of_le (left_ne_zero_of_mul hS) (by omega))
          (qPochhammer_ne_zero_of_le (right_ne_zero_of_mul hS) (by omega))
      have hs : (Complex.sqrt a)^2 = a := by
        rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
      apply h2
      simp only [qPochhammer_one]
      linear_combination -hs - h1a
  have hYeq : d*e*q⁻¹^n/a = a*q/(b*c) := by
    rw [zpow_neg, zpow_natCast] at hbal
    rw [inv_pow]
    field_simp
    field_simp at hbal
    linear_combination -hbal
  have hW := DLMF.Bailey.watson_transformation_rational n ha hb hc hd he hq0
      (fun m _ => qPochhammer_self_ne_zero hq m)
    hB hC hD hE (by rw [hYeq]; exact hY) (by rw [show a*q*q^n = a*q^(n+1) by ring]; exact hN)
  rw [sum_congr rfl hA, hW]
  have hXeq : d*e*q^(1-(n:ℤ))/(a*q/b) = a*q/c := by
    rw [zpow_sub₀ hq0, zpow_one, zpow_natCast]
    rw [zpow_neg, zpow_natCast] at hbal
    field_simp
    field_simp at hbal
    linear_combination -hbal
  have hCs : ∀ k ∈ range (n+1), DLMF.Bailey.watsonR4 a b c d e q n k =
      saalTerm d e (a*q/b) q n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hYk : qPochhammer (a*q/(b*c)) q k ≠ 0 := qPochhammer_ne_zero_of_le hY hkn
    rw [DLMF.Bailey.watsonR4, hYeq, saalTerm, hXeq]
    simp only [zpow_neg, zpow_natCast, inv_pow]
    field_simp
  rw [sum_congr rfl hCs, PfaffSaalschutz.sum_eq_cleared_value
    (div_ne_zero (mul_ne_zero ha hq0) hb) hq0 hq n hB
    (by rw [hXeq]; exact hC), saalValue]
  have e2 : a*q/b/e = c*d/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  have e3 : a*q/b/(d*e) = c/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  have e4 : a*q/(d*e) = b*c/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  have e5 : a*q/e = b*c*d/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  rw [PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer hd,
    PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer he,
      PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer (mul_ne_zero hd he), e2, e3, e4,
    qPochhammer_shift_negative (div_ne_zero (mul_ne_zero hc hd) ha) hq0,
    qPochhammer_shift_negative (div_ne_zero hc ha) hq0,
    qPochhammer_shift_negative (div_ne_zero (mul_ne_zero hb hc) ha) hq0,
    show a*q/b/d = a*q/(b*d) by ring]
  rw [e5, qPochhammer_shift_negative (div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) ha) hq0]
    at hE
  rw [e5, qPochhammer_shift_negative (div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) ha) hq0]
  have hE' := left_ne_zero_of_mul (left_ne_zero_of_mul hE)
  rw [show q/(c*d/a) = a*q/(c*d) by field_simp, show q/(c/a) = a*q/c by field_simp,
    show q/(b*c/a) = a*q/(b*c) by field_simp, show q/(b*c*d/a) = a*q/(b*c*d) by field_simp] at *
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hC0 : q^(-(n.choose 2:ℤ)) ≠ 0 := zpow_ne_zero _ hq0
  simp only [neg_div]
  rw [neg_pow (c*d/a/q), neg_pow (c/a/q), neg_pow (b*c/a/q), neg_pow (b*c*d/a/q)]
  simp only [div_pow, mul_pow]
  have hm1 : ((-1:ℂ))^n ≠ 0 := pow_ne_zero _ (by norm_num)
  generalize qPochhammer (a*q) q n = P1 at *
  generalize qPochhammer (a*q/(b*c)) q n = P2 at *
  generalize qPochhammer (a*q/d) q n = P3 at *
  generalize qPochhammer (a*q/(b*c*d)) q n = P4 at *
  generalize qPochhammer (a*q/(b*d)) q n = P5 at *
  generalize qPochhammer (a*q/(c*d)) q n = P6 at *
  generalize qPochhammer (a*q/b) q n = P7 at *
  generalize qPochhammer (a*q/c) q n = P8 at *
  generalize q^(-(n.choose 2:ℤ)) = Z at *
  generalize ((-1:ℂ))^n = M at *
  field_simp

/-- Away from one point, `1 - X/t` has no zeros near a nonzero point. -/
private lemma eventually_one_sub_div_ne (X b : ℂ) (hb : b ≠ 0) :
    ∀ᶠ t in 𝓝[≠] b, 1 - X/t ≠ 0 := by
  by_cases h : 1 - X/b = 0
  · have hX : X = b := by field_simp at h; linear_combination -h
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_ne_nhds hb)] with t ht ht0
    rw [hX]
    intro h'
    apply ht
    rw [Set.mem_singleton_iff]
    field_simp at h'
    linear_combination h'
  · have hc : ContinuousAt (fun t : ℂ => 1 - X/t) b := by fun_prop (disch := exact hb)
    exact nhdsWithin_le_nhds (hc.eventually_ne h)

/-- `(aq/(tc);q)_n` is nonzero for `t` near, but distinct from, a nonzero point. -/
private lemma eventually_qPochhammer_div_mul_ne_zero (a c q b : ℂ) (n : ℕ) (hb : b ≠ 0) :
    ∀ᶠ t in 𝓝[≠] b, qPochhammer (a*q/(t*c)) q n ≠ 0 := by
  have h := (Finset.eventually_all (range n)).mpr fun j _ =>
    eventually_one_sub_div_ne (a*q*q^j/c) b hb
  filter_upwards [h, nhdsWithin_le_nhds (eventually_ne_nhds hb)] with t ht ht0
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro j hj
  have := ht j hj
  by_cases hc : c = 0
  · simp [hc]
  · convert this using 2; field_simp

/-- Nonvanishing of a list of shifted factorials passes to shorter lengths. -/
private lemma qPochhammerList_ne_zero_of_le {q : ℂ} {k n : ℕ} (hk : k ≤ n) :
    ∀ l : List ℂ, qPochhammerList l q n ≠ 0 → qPochhammerList l q k ≠ 0
  | [], _ => by simp [qPochhammerList]
  | x :: l, h => by
    simp only [qPochhammerList, List.map_cons, List.prod_cons] at h ⊢
    exact mul_ne_zero (qPochhammer_ne_zero_of_le (left_ne_zero_of_mul h) hk)
      (qPochhammerList_ne_zero_of_le hk l (right_ne_zero_of_mul h))

/-- In Jackson's sum, `(aq/(bcd);q)_n ≠ 0` follows from `(aq/e;q)_n ≠ 0` by the balance. -/
private lemma qPochhammer_div_mul_mul_ne_zero_of_balanced {a b c d e q : ℂ} (hq0 : q≠0) (n : ℕ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hd : d≠0) (he : e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ))) (hE : qPochhammer (a*q/e) q n ≠ 0) :
    qPochhammer (a*q/(b*c*d)) q n ≠ 0 := by
  have e5 : a*q/e = b*c*d/a*q^(-(n:ℤ)) := by field_simp; linear_combination hbal
  rw [e5, qPochhammer_shift_negative (div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) ha) hq0,
    show q/(b*c*d/a) = a*q/(b*c*d) by field_simp] at hE
  exact left_ne_zero_of_mul (left_ne_zero_of_mul hE)

/-- Jackson's terminating very-well-poised balanced `8φ7` summation (DLMF 17.7.E14). -/
@[dlmf 17.7.E14]
theorem jackson_eight_phi_seven {a b c d e q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hbcd : b*c*d≠0) (he : e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ)))
    (hd : QDenominatorRegularThrough
        [Complex.sqrt a, -Complex.sqrt a, a*q/b, a*q/c, a*q/d, a*q/e, a*q^(n+1)] q n) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q=
      qPochhammerList [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q n/
        qPochhammerList [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q n := by
  have hb : b ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc : c ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hbcd
  have hqn : q^(-(n:ℤ)) ≠ 0 := zpow_ne_zero _ hq0
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hbal
    exact (mul_ne_zero (mul_ne_zero hbcd he) hqn) hbal.symm
  have hdd := hd
  simp only [QDenominatorRegularThrough, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, ne_eq, mul_eq_zero, not_or] at hdd
  obtain ⟨hS1, hS2, hB, hC, hD, hE, hN⟩ := hdd
  rw [PfaffSaalschutz.qPhi_eq_sum_of_mem hq0 n (by simp)]
  by_cases hY : qPochhammer (a*q/(b*c)) q n ≠ 0
  · exact jackson_sum_of_regular hq0 hq n hb hc hd0 he hbal (mul_ne_zero hS1 hS2) hB hC hD hE hN hY
  set E : ℂ → ℂ := fun t => a^2*q*q^n/(t*c*d) with hEdef
  have hEb : e = E b := by
    simp only [hEdef]
    rw [zpow_neg, zpow_natCast] at hbal
    field_simp
    field_simp at hbal
    linear_combination -hbal
  have hE0 : ∀ t, t ≠ 0 → E t ≠ 0 := fun t ht => by
    simp only [hEdef]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hq0) (pow_ne_zero n hq0))
      (mul_ne_zero (mul_ne_zero ht hc) hd0)
  have hbalE : ∀ t, t ≠ 0 → a^2*q = t*c*d*E t*q^(-(n:ℤ)) := fun t ht => by
    simp only [hEdef, zpow_neg, zpow_natCast]
    field_simp
  subst hEb
  have hbcd' : b*c*d ≠ 0 := hbcd
  set g : ℂ → ℂ := fun t => (∑ k ∈ range (n+1),
      qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,q^(-(n:ℤ))]
        [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)] q q k) -
      qPochhammerList [a*q,a*q/(t*c),a*q/(t*d),a*q/(c*d)] q n/
        qPochhammerList [a*q/t,a*q/c,a*q/d,a*q/(t*c*d)] q n with hgdef
  suffices g b = 0 by simpa [hgdef, sub_eq_zero] using this
  have hcore : ∀ t, t ≠ 0 → qPochhammer (a*q/t) q n ≠ 0 → qPochhammer (a*q/E t) q n ≠ 0 →
      qPochhammer (a*q/(t*c)) q n ≠ 0 → g t = 0 := by
    intro t ht hBt hEt hYt
    simp only [hgdef, sub_eq_zero]
    exact jackson_sum_of_regular hq0 hq n ht hc hd0 (hE0 t ht) (hbalE t ht)
        (mul_ne_zero hS1 hS2) hBt hC
      hD hEt hN hYt
  have hEc : ContinuousAt E b := by simp only [hEdef]; fun_prop (disch := exact hbcd')
  have hEb0 := hE0 b hb
  have hBc : ContinuousAt (fun t : ℂ => qPochhammer (a*q/t) q n) b := by
    fun_prop (disch := exact hb)
  have hEtc : ContinuousAt (fun t : ℂ => qPochhammer (a*q/E t) q n) b := by
    fun_prop (disch := exact hEb0)
  have hev : g =ᶠ[𝓝[≠] b] fun _ => 0 := by
    filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds hb),
      nhdsWithin_le_nhds (hBc.eventually_ne hB), nhdsWithin_le_nhds (hEtc.eventually_ne hE),
      eventually_qPochhammer_div_mul_ne_zero a c q b n hb] with t h1 h2 h3 h4
    exact hcore t h1 h2 h3 h4
  have hbcdn := qPochhammer_div_mul_mul_ne_zero_of_balanced hq0 n ha hb hc hd0 hEb0 hbal hE
  have hg : ContinuousAt g b := by
    simp only [hgdef]
    refine ContinuousAt.sub ?_ ?_
    · refine tendsto_finsetSum _ fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hU := qPochhammerList_ne_zero_of_le hkn _ hd
      have hden : qPochhammerList [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/E b,
          a*q^(n+1)] q k * qPochhammer q q k ≠ 0 := mul_ne_zero hU (qPochhammer_self_ne_zero hq k)
      have hform : (fun t => qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,q^(-(n:ℤ))]
          [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)] q q k) =
          fun t => qPochhammerList [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,q^(-(n:ℤ))] q k /
            (qPochhammerList [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)]
              q k * qPochhammer q q k) * q^k := by
        funext t
        simp only [qPhiTerm, qPhiExponent, List.length_cons, List.length_nil]
        norm_num
      show ContinuousAt (fun t => qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,t,c,d,E t,
        q^(-(n:ℤ))] [Complex.sqrt a,-Complex.sqrt a,a*q/t,a*q/c,a*q/d,a*q/E t,a*q^(n+1)] q q k) b
      rw [hform]
      refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ hden) continuousAt_const
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop (disch := first | exact hb | exact hEb0)
    · have hden : qPochhammerList [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q n ≠ 0 := by
        simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one]
        exact mul_ne_zero hB (mul_ne_zero hC (mul_ne_zero hD hbcdn))
      refine ContinuousAt.div ?_ ?_ hden
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop (disch := first | exact hb | exact mul_ne_zero hb hc | exact mul_ne_zero hb hd0)
      · simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        fun_prop (disch := first | exact hb | exact hbcd')
  have h1 : Tendsto g (𝓝[≠] b) (𝓝 (g b)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hev.symm)

/-- The rational terms of the terminating very-well-poised `₆φ₅` sum. -/
def sixTerm (a b c q : ℂ) (n k : ℕ) : ℂ :=
  DLMF.Bailey.unitD a q k * (qPochhammer b q k * qPochhammer c q k * qPochhammer (q^(-(n:ℤ))) q k) /
    (qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k * qPochhammer (a*q^(n+1)) q k *
      qPochhammer q q k) * (a*q^(n+1)/(b*c))^k

/-- The terminating `₆φ₅` sum in rational form when `(aq;q)_{2n} ≠ 0`, from Bailey's lemma. -/
private lemma sum_sixTerm_of_qPochhammer_two_mul_ne_zero {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (n : ℕ) (hb : b≠0) (hc : c≠0)
    (hB : qPochhammer (a*q/b) q n ≠ 0) (hC : qPochhammer (a*q/c) q n ≠ 0)
    (haq : qPochhammer (a*q) q (n+n) ≠ 0) :
    ∑ k ∈ range (n+1), sixTerm a b c q n k =
      qPochhammer (a*q) q n * qPochhammer (a*q/(b*c)) q n /
        (qPochhammer (a*q/b) q n * qPochhammer (a*q/c) q n) := by
  have hqq : ∀ m, qPochhammer q q m ≠ 0 := qPochhammer_self_ne_zero hq
  have h := DLMF.Bailey.bailey_relation (a := a) (q := q) (n := n) (rho1 := b) (rho2 := c)
    (α := DLMF.Bailey.unitAlpha a q) (β := fun k => if k = 0 then 1 else 0)
    (fun k hk => DLMF.Bailey.unit_pair a q k (fun m _ => hqq m)
      (qPochhammer_ne_zero_of_le haq (by omega))) hb hc (fun m _ => hqq m) haq hB hC
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (by simp)] at h
  have han : qPochhammer (a*q) q n ≠ 0 := qPochhammer_ne_zero_of_le haq (by omega)
  have key : ∀ k ∈ range (n+1), qPochhammer b q k * qPochhammer c q k *
      (a*q/(b*c))^k * DLMF.Bailey.unitAlpha a q k / (qPochhammer (a*q/b) q k *
        qPochhammer (a*q/c) q k) / (qPochhammer q q (n-k) * qPochhammer (a*q) q (n+k)) =
      sixTerm a b c q n k / (qPochhammer q q n * qPochhammer (a*q) q n) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hQp : q^(1-(n:ℤ))/q = q^(-(n:ℤ)) := by
      rw [zpow_sub₀ hq0, zpow_one, zpow_neg]; field_simp
    have hNm : qPochhammer (q^(-(n:ℤ))) q k ≠ 0 :=
      PfaffSaalschutz.pochhammer_zpow_neg_ne_zero hq0 hq hkn
    have h2 := qPochhammer_sub_index hq0 hq0 hkn (by rw [hQp]; exact hNm)
    rw [hQp] at h2
    have h3 := qPochhammer_add (a*q) q n k
    rw [show a*q*q^n = a*q^(n+1) by ring] at h3
    have hBk := qPochhammer_ne_zero_of_le hB hkn
    have hCk := qPochhammer_ne_zero_of_le hC hkn
    have hNk : qPochhammer (a*q^(n+1)) q k ≠ 0 := by
      intro h0; apply haq
      rw [show n+n = (n+k) + (n-k) by omega, qPochhammer_add, h3, h0]; simp
    rw [h2, h3, DLMF.Bailey.unitAlpha, sixTerm,
      show (-q/q) = -1 by field_simp]
    have hE : q^((k.choose 2:ℤ)-(n:ℤ)*k) = q^(k.choose 2) / q^(n*k) := by
      rw [zpow_sub₀ hq0]; norm_cast
    rw [hE]
    have hm1 : ((-1:ℂ))^k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hqk := hqq k
    have hc2 : q^(k.choose 2) ≠ 0 := pow_ne_zero _ hq0
    have hnk : q^(n*k) ≠ 0 := pow_ne_zero _ hq0
    simp only [div_pow, mul_pow, ← pow_mul]
    rw [show (n+1)*k = n*k + k by ring, pow_add]
    field_simp
    ring
  rw [sum_congr rfl key, ← sum_div] at h
  simp only [ite_true, pow_zero, mul_one, Nat.sub_zero, qPochhammer_zero, one_mul] at h
  have hqn := hqq n
  rw [eq_div_iff (mul_ne_zero hqn han)] at h
  rw [← h]
  field_simp

/-- Away from one point, `1 - tX` has no zeros near any point. -/
private lemma eventually_one_sub_mul_ne (X a : ℂ) : ∀ᶠ t in 𝓝[≠] a, 1 - t*X ≠ 0 := by
  by_cases h : 1 - a*X = 0
  · filter_upwards [self_mem_nhdsWithin] with t ht h'
    apply ht
    rw [Set.mem_singleton_iff]
    have hX : X ≠ 0 := by rintro rfl; simp at h
    apply mul_right_cancel₀ hX
    linear_combination h - h'
  · have hc : ContinuousAt (fun t : ℂ => 1 - t*X) a := by fun_prop
    exact nhdsWithin_le_nhds (hc.eventually_ne h)

attribute [local fun_prop] DLMF.Bailey.continuous_unitD

/-- The terminating `₆φ₅` sum in rational form for every regular `a`. -/
lemma sum_sixTerm_eq {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hb : b≠0) (hc : c≠0)
    (hB : qPochhammer (a*q/b) q n ≠ 0) (hC : qPochhammer (a*q/c) q n ≠ 0)
    (hN : qPochhammer (a*q^(n+1)) q n ≠ 0) :
    ∑ k ∈ range (n+1), sixTerm a b c q n k =
      qPochhammer (a*q) q n * qPochhammer (a*q/(b*c)) q n /
        (qPochhammer (a*q/b) q n * qPochhammer (a*q/c) q n) := by
  set g : ℂ → ℂ := fun t => ∑ k ∈ range (n+1), sixTerm t b c q n k -
    qPochhammer (t*q) q n * qPochhammer (t*q/(b*c)) q n /
        (qPochhammer (t*q/b) q n * qPochhammer (t*q/c) q n) with hgdef
  suffices g a = 0 by simpa [hgdef, sub_eq_zero] using this
  have hBc : ContinuousAt (fun t : ℂ => qPochhammer (t*q/b) q n) a := by fun_prop
  have hCc : ContinuousAt (fun t : ℂ => qPochhammer (t*q/c) q n) a := by fun_prop
  have hNc : ContinuousAt (fun t : ℂ => qPochhammer (t*q^(n+1)) q n) a := by fun_prop
  have hev : g =ᶠ[𝓝[≠] a] fun _ => 0 := by
    have hA := (Finset.eventually_all (range (n+n))).mpr fun j _ =>
      eventually_one_sub_mul_ne (q*q^j) a
    filter_upwards [nhdsWithin_le_nhds (hBc.eventually_ne hB),
      nhdsWithin_le_nhds (hCc.eventually_ne hC), hA] with t h1 h2 h3
    simp only [hgdef, sub_eq_zero]
    refine sum_sixTerm_of_qPochhammer_two_mul_ne_zero hq0 hq n hb hc h1 h2 ?_
    rw [qPochhammer_eq_prod, prod_ne_zero_iff]
    intro j hj
    have := h3 j hj
    rwa [show t*q*q^j = t*(q*q^j) by ring]
  have hg : ContinuousAt g a := by
    simp only [hgdef]
    refine ContinuousAt.sub ?_ ?_
    · refine tendsto_finsetSum _ fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hden : qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k * qPochhammer (a*q^(n+1)) q k *
          qPochhammer q q k ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (qPochhammer_ne_zero_of_le hB hkn)
          (qPochhammer_ne_zero_of_le hC hkn)) (qPochhammer_ne_zero_of_le hN hkn))
          (qPochhammer_self_ne_zero hq k)
      have hbc : b*c ≠ 0 := mul_ne_zero hb hc
      show ContinuousAt (fun t => sixTerm t b c q n k) a
      simp only [sixTerm]
      fun_prop (disch := first | exact hden | exact hbc)
    · fun_prop (disch :=
          first | exact mul_ne_zero hB hC | exact hb | exact hc | exact mul_ne_zero hb hc)
  have h1 : Tendsto g (𝓝[≠] a) (𝓝 (g a)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hev.symm)

/-- The terminating very-well-poised `6φ5` summation with upper parameter `q^(-n)` (DLMF
17.7.E16). -/
@[dlmf 17.7.E16]
theorem six_phi_five_terminating {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hbc : b*c≠0)
    (hd : QDenominatorRegularThrough [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q n) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q (a*q^(n+1)/(b*c))=
      qPochhammerList [a*q,a*q/(b*c)] q n/qPochhammerList [a*q/b,a*q/c] q n := by
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  have hc : c ≠ 0 := right_ne_zero_of_mul hbc
  have hdd := hd
  simp only [QDenominatorRegularThrough, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, ne_eq, mul_eq_zero, not_or] at hdd
  obtain ⟨hS1, hS2, hB, hC, hN⟩ := hdd
  rw [PfaffSaalschutz.qPhi_eq_sum_of_mem hq0 n (by simp)]
  have hterm : ∀ k ∈ range (n+1), qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q (a*q^(n+1)/(b*c)) k =
      sixTerm a b c q n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hk' : k = 0 ∨ (a ≠ 1 ∧
        qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0) := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exact Or.inl h0
      · right
        refine ⟨fun h1a => ?_, mul_ne_zero (qPochhammer_ne_zero_of_le hS1 hkn)
          (qPochhammer_ne_zero_of_le hS2 hkn)⟩
        have h2 : qPochhammer (Complex.sqrt a) q 1 * qPochhammer (-Complex.sqrt a) q 1 ≠ 0 :=
          mul_ne_zero (qPochhammer_ne_zero_of_le hS1 (by omega))
            (qPochhammer_ne_zero_of_le hS2 (by omega))
        have hs : (Complex.sqrt a)^2 = a := by
          rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
        apply h2
        simp only [qPochhammer_one]
        linear_combination -hs - h1a
    have hu := veryWellPoised_factor_eq_unitD k hk'
    calc _ = qPochhammer a q k * qPochhammer (q*Complex.sqrt a) q k *
          qPochhammer (-q*Complex.sqrt a) q k /
          (qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k) *
          ((qPochhammer b q k * qPochhammer c q k * qPochhammer (q^(-(n:ℤ))) q k) /
          (qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k * qPochhammer (a*q^(n+1)) q k *
            qPochhammer q q k) * (a*q^(n+1)/(b*c))^k) := by
          simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
          norm_num
          ring
      _ = _ := by rw [hu, sixTerm]; ring
  rw [sum_congr rfl hterm, sum_sixTerm_eq hq0 hq n hb hc hB hC hN]
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- The nonterminating very-well-poised balanced `8φ7` summation (DLMF 17.7.E17). -/
@[dlmf 17.7.E17]
theorem nonterminating_eight_phi_seven {a b c d e f q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (habcdef : a*b*c*d*e*f≠0) (hbal : q*a^2=b*c*d*e*f)
    (hd : QDenominatorRegular [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,
      b/Complex.sqrt a,-b/Complex.sqrt a,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f,
      b*c/a,b*d/a,b*e/a,b*f/a,b^2*q/a] q) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,f]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f] q q-
      b/a*qPochhammerListInf [a*q,c,d,e,f,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f] q/
        qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,b*c/a,b*d/a,b*e/a,b*f/a,b^2*q/a] q*
        qPhi [b^2/a,q*b/Complex.sqrt a,-q*b/Complex.sqrt a,b,b*c/a,b*d/a,b*e/a,b*f/a]
          [b/Complex.sqrt a,-b/Complex.sqrt a,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f] q q=
      qPochhammerListInf [a*q,b/a,a*q/(c*d),a*q/(c*e),a*q/(c*f),a*q/(d*e),a*q/(d*f),a*q/(e*f)] q/
        qPochhammerListInf [a*q/c,a*q/d,a*q/e,a*q/f,b*c/a,b*d/a,b*e/a,b*f/a] q := by
  sorry

/-- The finite parameter-shift factors occurring in the q-Karlsson–Minton identities. -/
private def qMintonFactor (p : List (ℂ × ℕ)) (q w : ℂ) : ℂ :=
  (p.map fun x => qPochhammer (x.1 * w) q x.2).prod

/-- A polynomial of total degree at most `N` annihilates the q-binomial series at
`az = q⁻ᴺ` when each factor is a finite q-shifted factorial. -/
private lemma qMintonFactor_hasSum_zero {a q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (p : List (ℂ × ℕ)) {N : ℕ} (hN : qMintonWeight p ≤ N) {z : ℂ}
    (hz : ‖z‖ < 1) (haz : a * z = q ^ (-(N : ℤ))) :
    HasSum (fun n : ℕ => qPochhammer a q n / qPochhammer q q n *
      qMintonFactor p q (q ^ n) * z ^ n) 0 := by
  induction p generalizing N z with
  | nil =>
    have hv : qPochhammerInf (a * z) q = 0 := by
      rw [haz, qPochhammerInf_mul_qPochhammer hq (N + 1)]
      have hzero : qPochhammer (q ^ (-(N : ℤ))) q (N + 1) = 0 := by
        simpa only [zpow_neg, zpow_natCast] using
          qPochhammer_recip_pow_eq_zero hq0 (Nat.lt_succ_self N)
      rw [hzero, zero_mul]
    have hs := summable_q_binomial_series (a := a) hq hz
    have hval := q_binomial_theorem (a := a) hq hz
    rw [hv, zero_div] at hval
    simpa [qMintonFactor, ← hval] using hs.hasSum
  | cons x p ih =>
    rcases x with ⟨x, m⟩
    have hdeg : m + qMintonWeight p ≤ N := by simpa [qMintonWeight] using hN
    have hsum : ∀ i ∈ range (m + 1), HasSum (fun n : ℕ =>
        (qBinom q m i * (-1) ^ i * q ^ i.choose 2 * x ^ i) *
        (qPochhammer a q n / qPochhammer q q n * qMintonFactor p q (q ^ n) *
          (z * q ^ i) ^ n)) 0 := by
      intro i hi
      have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have hiN : i ≤ N := by omega
      have hzi : ‖z * q ^ i‖ < 1 := by
        rw [norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (norm_nonneg z)
          (pow_le_one₀ (norm_nonneg q) hq.le)).trans_lt hz
      have hai : a * (z * q ^ i) = q ^ (-((N - i : ℕ) : ℤ)) := by
        rw [← mul_assoc, haz, ← zpow_natCast, ← zpow_add₀ hq0]
        congr 1
        omega
      simpa only [mul_zero] using (ih (N := N - i) (by omega) hzi hai).mul_left
        (qBinom q m i * (-1) ^ i * q ^ i.choose 2 * x ^ i)
    have hs := hasSum_sum hsum
    simp only [sum_const_zero] at hs
    convert hs using 1
    funext n
    simp only [qMintonFactor, List.map_cons, List.prod_cons] at *
    rw [qPochhammer_eq_sum_qBinom (x * q ^ n) q m, ← mul_assoc, mul_sum, sum_mul, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n i]
    ring

/-- Moving integer parameter shifts between the upper and lower q-factorials. -/
private lemma qMintonFactor_ratio {q : ℂ} (hq : ‖q‖ < 1) (p : List (ℂ × ℕ))
    (hd : QDenominatorRegular (qMintonLower p) q) (n : ℕ) :
    qPochhammerList (qMintonUpper p q) q n / qPochhammerList (qMintonLower p) q n =
      qMintonFactor p q (q ^ n) / qMintonFactor p q 1 := by
  induction p with
  | nil => simp [qMintonUpper, qMintonLower, qPochhammerList, qMintonFactor]
  | cons x p ih =>
    rcases x with ⟨x, m⟩
    have hx : ∀ j : ℕ, x * q ^ j ≠ 1 := fun j => hd x (by simp [qMintonLower]) j
    have hxn := qPochhammer_ne_zero_of_factors hq (fun j h => hx j (sub_eq_zero.mp h).symm) n
    have hxm := qPochhammer_ne_zero_of_factors hq (fun j h => hx j (sub_eq_zero.mp h).symm) m
    have hp : QDenominatorRegular (qMintonLower p) q := fun b hb =>
      hd b (by simp [qMintonLower] at hb ⊢; exact Or.inr hb)
    simp only [qMintonUpper, qMintonLower, qPochhammerList, qMintonFactor,
      List.map_cons, List.prod_cons, mul_one] at ih ⊢
    rw [mul_div_mul_comm, ih hp]
    have hr : qPochhammer (x * q ^ m) q n / qPochhammer x q n =
        qPochhammer (x * q ^ n) q m / qPochhammer x q m := by
      apply (div_eq_div_iff hxn hxm).mpr
      rw [mul_comm _ (qPochhammer x q m), ← qPochhammer_add,
        mul_comm _ (qPochhammer x q n), ← qPochhammer_add, Nat.add_comm]
    rw [hr, mul_div_mul_comm]

/-- The base case of Karlsson–Minton is q-Gauss, including the regular upper parameter zero. -/
private lemma qMinton_gauss_base {a b q z : ℂ} (ha : a ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hd : QDenominatorRegular [b * q] q) (hz : ‖z‖ < 1) (haz : a * z = q) :
    HasSum (qPhiTerm [a, b] [b * q] q z)
      (qPochhammerListInf [q, b * q / a] q / qPochhammerListInf [b * q, q / a] q) := by
  have hez : z = q / a := (eq_div_iff ha).mpr (by rw [mul_comm]; exact haz)
  subst z
  have hs := qPhi_hasSum (a := [a, b]) (b := [b * q]) hq0 hq hd (by simp) (fun _ => hz)
  by_cases hb : b = 0
  · subst b
    have he : qPhi [a, 0] [0] q (q / a) = qPochhammerInf q q / qPochhammerInf (q / a) q := by
      rw [qPhi]
      calc
        (∑' n : ℕ, qPhiTerm [a, 0] [0] q (q / a) n) =
            ∑' n : ℕ, qPochhammer a q n / qPochhammer q q n * (q / a) ^ n := by
          apply tsum_congr
          intro n
          simp [qPhiTerm, qPhiExponent, qPochhammerList]
        _ = _ := by
          rw [← q_binomial_theorem hq hz, show a * (q / a) = q by field_simp]
    simpa [he, qPochhammerListInf, qPochhammerInf] using hs
  · have hnorm : ‖b * q‖ < ‖a * b‖ := by
      rw [norm_div, div_lt_one₀ (norm_pos_iff.mpr ha)] at hz
      simp only [norm_mul]
      nlinarith [norm_pos_iff.mpr hb]
    have he := q_gauss (a := a) (b := b) (c := b * q) hq hnorm hd
    have e1 : b * q / (a * b) = q / a := by field_simp
    have e2 : b * q / b = q := by field_simp
    rw [e1, e2] at he
    rw [he] at hs
    simpa [qPochhammerListInf, mul_comm, mul_left_comm, mul_assoc] using hs

/-- Multiplication of the finite parameter polynomial by one more linear factor uses
q-binomial annihilation, reducing Karlsson–Minton to its q-Gauss base case. -/
private lemma qMintonFactor_hasSum_gauss {a b q : ℂ} (ha : a ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hd : QDenominatorRegular [b * q] q) (p : List (ℂ × ℕ))
    {z : ℂ} (hz : ‖z‖ < 1) (haz : a * z = q ^ (1 - (qMintonWeight p : ℤ))) :
    HasSum (fun n : ℕ => qPhiTerm [a, b] [b * q] q z n * qMintonFactor p q (q ^ n))
      ((p.map (fun x => (range x.2).prod (fun j => b - x.1 * q ^ j))).prod *
        (qPochhammerListInf [q, b * q / a] q / qPochhammerListInf [b * q, q / a] q)) := by
  induction p generalizing z with
  | nil =>
    simpa [qMintonFactor] using qMinton_gauss_base ha hq0 hq hd hz
      (by simpa [qMintonWeight] using haz)
  | cons x p ih =>
    rcases x with ⟨x, m⟩
    induction m generalizing z with
    | zero =>
      simpa [qMintonFactor, qMintonWeight] using ih hz (by simpa [qMintonWeight] using haz)
    | succ m ihm =>
      have hzq : ‖z * q‖ < 1 := by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg z) hq.le).trans_lt hz
      have ha0 : a * z = q ^ (-(qMintonWeight ((x, m) :: p) : ℤ)) := by
        convert haz using 1
        simp [qMintonWeight]
        congr 1
        ring
      have haq : a * (z * q) = q ^ (1 - (qMintonWeight ((x, m) :: p) : ℤ)) := by
        rw [← mul_assoc, ha0]
        calc
          q ^ (-(qMintonWeight ((x, m) :: p) : ℤ)) * q =
              q ^ (-(qMintonWeight ((x, m) :: p) : ℤ)) * q ^ (1 : ℤ) := by rw [zpow_one]
          _ = _ := by rw [← zpow_add₀ hq0]; congr 1; ring
      have hrec := ihm hzq haq
      have hzero := qMintonFactor_hasSum_zero hq0 hq ((x, m) :: p) le_rfl hz ha0
      have hs := (hrec.mul_left (b - x * q ^ m)).add (hzero.mul_left (1 - b))
      simp only [mul_zero, add_zero] at hs
      convert hs using 1
      · funext n
        simp only [qMintonFactor, List.map_cons, List.prod_cons, qPochhammer_succ]
        rw [qPhiTerm_two_one, qPhiTerm_two_one, mul_pow]
        have hbrel : qPochhammer b q n * (1 - b * q ^ n) = (1 - b) * qPochhammer (b * q) q n := by
          rw [← qPochhammer_succ, qPochhammer_succ']
        have hB := qPochhammer_ne_zero_of_qDenominatorRegular hq hd n
        have hQ := qPochhammer_self_ne_zero hq n
        generalize qPochhammer a q n = A
        generalize qPochhammer b q n = B at hbrel ⊢
        generalize qPochhammer (b * q) q n = C at hbrel hB ⊢
        generalize qPochhammer (x * q ^ n) q m = X
        generalize (List.map (fun x => qPochhammer (x.1 * q ^ n) q x.2) p).prod = P
        field_simp
        linear_combination A * X * P * z ^ n * hbrel
      · simp only [List.map_cons, List.prod_cons, prod_range_succ]
        ring

/-- The cleared finite product includes b=0 without a spurious0 times infinity. -/
@[dlmf 17.7.E18]
theorem q_karlsson_minton {a b q : ℂ} (ha : a ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (p : List (ℂ × ℕ))
    (hz : ‖a⁻¹ * q ^ (1 - (qMintonWeight p : ℤ))‖ < 1)
    (hd : QDenominatorRegular (b * q :: qMintonLower p) q) :
    qPhi (a :: b :: qMintonUpper p q) (b * q :: qMintonLower p) q
        (a⁻¹ * q ^ (1 - (qMintonWeight p : ℤ))) =
      qPochhammerListInf [q, b * q / a] q / qPochhammerListInf [b * q, q / a] q *
      (p.map (fun x => (range x.2).prod (fun j => b - x.1 * q ^ j))).prod /
        (p.map fun x => qPochhammer x.1 q x.2).prod := by
  let z := a⁻¹ * q ^ (1 - (qMintonWeight p : ℤ))
  have hreg : QDenominatorRegular [b * q] q := fun c hc =>
    hd c (by simp only [List.mem_singleton] at hc; simp [hc])
  have hp : QDenominatorRegular (qMintonLower p) q := fun c hc => hd c (by simp [hc])
  have hs := qMintonFactor_hasSum_gauss ha hq0 hq hreg p hz
    (show a * z = q ^ (1 - (qMintonWeight p : ℤ)) by dsimp [z]; field_simp)
  have hs' := hs.mul_right (qMintonFactor p q 1)⁻¹
  have he : qPhiTerm (a :: b :: qMintonUpper p q) (b * q :: qMintonLower p) q z =
      fun n : ℕ => (qPhiTerm [a, b] [b * q] q z n * qMintonFactor p q (q ^ n)) *
        (qMintonFactor p q 1)⁻¹ := by
    funext n
    have hexp : qPhiExponent (a :: b :: qMintonUpper p q) (b * q :: qMintonLower p) = 0 := by
      simp [qPhiExponent, qMintonUpper, qMintonLower]
      ring
    rw [qPhiTerm, hexp, zpow_zero, mul_one, qPhiTerm_two_one]
    rw [show qPochhammerList (a :: b :: qMintonUpper p q) q n =
        qPochhammer a q n * qPochhammer b q n * qPochhammerList (qMintonUpper p q) q n by
      simp [qPochhammerList]; ring]
    rw [show qPochhammerList (b * q :: qMintonLower p) q n =
        qPochhammer (b * q) q n * qPochhammerList (qMintonLower p) q n by
      simp [qPochhammerList]]
    rw [show qPochhammer a q n * qPochhammer b q n * qPochhammerList (qMintonUpper p q) q n /
        (qPochhammer (b * q) q n * qPochhammerList (qMintonLower p) q n *
            qPochhammer q q n) * z ^ n =
        (qPochhammer a q n * qPochhammer b q n /
          (qPochhammer (b * q) q n * qPochhammer q q n) * z ^ n) *
          (qPochhammerList (qMintonUpper p q) q n / qPochhammerList (qMintonLower p) q n) by ring,
      qMintonFactor_ratio hq p hp n]
    ring
  have hsum := (he.symm ▸ hs').tsum_eq
  change qPhi (a :: b :: qMintonUpper p q) (b * q :: qMintonLower p) q z = _
  rw [show qPhi (a :: b :: qMintonUpper p q) (b * q :: qMintonLower p) q z =
    (p.map (fun x => (range x.2).prod (fun j => b - x.1 * q ^ j))).prod *
      (qPochhammerListInf [q, b * q / a] q / qPochhammerListInf [b * q, q / a] q) *
        (qMintonFactor p q 1)⁻¹ from hsum]
  simp only [qMintonFactor, mul_one]
  ring

/-- The primary-source argument is q^(−Σm)/a; the printed extra q is disproved below. -/
@[dlmf 17.7.E19]
theorem q_karlsson_minton_zero_corrected {a q : ℂ} (ha : a ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (p : List (ℂ × ℕ))
    (hz : ‖a⁻¹ * q ^ (-(qMintonWeight p : ℤ))‖ < 1) (hd : QDenominatorRegular (qMintonLower p) q) :
    qPhi (a :: qMintonUpper p q) (qMintonLower p) q (a⁻¹ * q ^ (-(qMintonWeight p : ℤ))) = 0 := by
  let z := a⁻¹ * q ^ (-(qMintonWeight p : ℤ))
  have hs := qMintonFactor_hasSum_zero hq0 hq p le_rfl hz
    (show a * z = q ^ (-(qMintonWeight p : ℤ)) by dsimp [z]; field_simp)
  have hs' := hs.mul_right (qMintonFactor p q 1)⁻¹
  rw [zero_mul] at hs'
  have he : qPhiTerm (a :: qMintonUpper p q) (qMintonLower p) q z =
      fun n : ℕ => (qPochhammer a q n / qPochhammer q q n *
        qMintonFactor p q (q ^ n) * z ^ n) * (qMintonFactor p q 1)⁻¹ := by
    funext n
    have hexp : qPhiExponent (a :: qMintonUpper p q) (qMintonLower p) = 0 := by
      simp [qPhiExponent, qMintonUpper, qMintonLower]
      ring
    simp only [qPhiTerm, hexp, zpow_zero, mul_one]
    rw [show qPochhammerList (a :: qMintonUpper p q) q n =
      qPochhammer a q n * qPochhammerList (qMintonUpper p q) q n by
      simp [qPochhammerList]]
    rw [show qPochhammer a q n * qPochhammerList (qMintonUpper p q) q n /
        (qPochhammerList (qMintonLower p) q n * qPochhammer q q n) =
      qPochhammer a q n / qPochhammer q q n *
        (qPochhammerList (qMintonUpper p q) q n / qPochhammerList (qMintonLower p) q n) by ring,
      qMintonFactor_ratio hq p hd n]
    ring
  exact (he.symm ▸ hs').tsum_eq

/-- Gosper's bibasic summation of a finite series in the two bases `p` and `q` (DLMF 17.7.E20). -/
@[dlmf 17.7.E20]
theorem bibasic_gosper {a c p q : ℂ} (ha : a≠1) (hc : c≠0) (n : ℕ)
    (hd : qPochhammer q q n*qPochhammer (a*p/c) p n≠0) :
    (∑ k∈range (n+1), (1-a*p^k*q^k)/(1-a)*qPochhammer a p k*qPochhammer c q k/
      (qPochhammer q q k*qPochhammer (a*p/c) p k)*c^(-(k:ℤ)))=
      qPochhammer (a*p) p n*qPochhammer (c*q) q n/
        (qPochhammer q q n*qPochhammer (a*p/c) p n)*c^(-(n:ℤ)) := by
  have h1a : 1-a≠0 := sub_ne_zero.mpr (Ne.symm ha)
  induction n with
  | zero => simp; field_simp; exact h1a
  | succ n ih =>
    have hq1 := qPochhammer_ne_zero_of_le (left_ne_zero_of_mul hd) (Nat.le_succ n)
    have hp1 := qPochhammer_ne_zero_of_le (right_ne_zero_of_mul hd) (Nat.le_succ n)
    rw [sum_range_succ, ih (mul_ne_zero hq1 hp1)]
    rw [qPochhammer_succ] at hd
    have e1 : 1 - q*q^n ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
    have e2 : 1 - a*p/c*p^n ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hd)
    rw [qPochhammer_succ' a, qPochhammer_succ' c, qPochhammer_succ (a*p), qPochhammer_succ (c*q),
      qPochhammer_succ q q n, qPochhammer_succ (a*p/c) p n]
    have e3 : c - a*p*p^n ≠ 0 := by
      intro h; apply e2; field_simp; linear_combination h
    simp only [zpow_neg, zpow_natCast]
    field_simp
    ring

/-- Gasper's bibasic summation of a finite series in the two bases `p` and `q` (DLMF 17.7.E21). -/
@[dlmf 17.7.E21]
theorem bibasic_gasper {a b c p q : ℂ} (ha : a≠1) (hb : b≠1) (hbc : b*c≠0) (hq : q≠0) (n : ℕ)
    (hd : qPochhammerList [q,a*q/b] q n*qPochhammerList [a*p/c,b*c*p] p n≠0) :
    (∑ k∈range (n+1), (1-a*p^k*q^k)*(1-b*p^k*q^(-(k:ℤ)))/((1-a)*(1-b))*
      qPochhammerList [a,b] p k*qPochhammerList [c,a/(b*c)] q k/
        (qPochhammerList [q,a*q/b] q k*qPochhammerList [a*p/c,b*c*p] p k)*q^k)=
      qPochhammerList [a*p,b*p] p n*qPochhammerList [c*q,a*q/(b*c)] q n/
        (qPochhammerList [q,a*q/b] q n*qPochhammerList [a*p/c,b*c*p] p n) := by
  have h1a : 1-a≠0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1b : 1-b≠0 := sub_ne_zero.mpr (Ne.symm hb)
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hbc
  have hc0 : c ≠ 0 := right_ne_zero_of_mul hbc
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at hd ⊢
  induction n with
  | zero => simp; field_simp; exact ⟨h1a, h1b⟩
  | succ n ih =>
    simp only [qPochhammer_succ] at hd
    have f1 : qPochhammer q q n ≠ 0 := by intro h; apply hd; simp [h]
    have f2 : qPochhammer (a*q/b) q n ≠ 0 := by intro h; apply hd; simp [h]
    have f3 : qPochhammer (a*p/c) p n ≠ 0 := by intro h; apply hd; simp [h]
    have f4 : qPochhammer (b*c*p) p n ≠ 0 := by intro h; apply hd; simp [h]
    have g1 : 1 - q*q^n ≠ 0 := by intro h; apply hd; simp [h]
    have g2 : b - a*q*q^n ≠ 0 := by
      intro h; apply hd
      have : 1 - a*q/b*q^n = 0 := by field_simp; linear_combination h
      simp [this]
    have g3 : c - a*p*p^n ≠ 0 := by
      intro h; apply hd
      have : 1 - a*p/c*p^n = 0 := by field_simp; linear_combination h
      simp [this]
    have g4 : 1 - b*c*p*p^n ≠ 0 := by intro h; apply hd; simp [h]
    rw [sum_range_succ, ih (by simp [f1, f2, f3, f4])]
    rw [qPochhammer_succ' a, qPochhammer_succ' b, qPochhammer_succ' c, qPochhammer_succ' (a/(b*c)),
      qPochhammer_succ (a*p), qPochhammer_succ (b*p), qPochhammer_succ (c*q),
      qPochhammer_succ (a*q/(b*c)), qPochhammer_succ q q n, qPochhammer_succ (a*q/b) q n,
      qPochhammer_succ (a*p/c) p n, qPochhammer_succ (b*c*p) p n]
    rw [show a/(b*c)*q = a*q/(b*c) by ring]
    have g5 : q^n ≠ 0 := pow_ne_zero n hq
    have g4' : 1 - p*b*c*p^n ≠ 0 := by rw [show p*b*c = b*c*p by ring]; exact g4
    have f4' : qPochhammer (p*b*c) p n ≠ 0 := by rw [show p*b*c = b*c*p by ring]; exact f4
    simp only [zpow_neg, zpow_natCast]
    field_simp
    ring

/-- Telescoping over an integer interval. -/
private lemma sum_Icc_sub_telescope (T : ℤ → ℂ) {a b : ℤ} (h : a ≤ b + 1) :
    ∑ k ∈ Finset.Icc a b, (T k - T (k-1)) = T b - T (a-1) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, b = a - 1 + t := ⟨(b - (a-1)).toNat, by omega⟩
  clear h
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show a - 1 + ((t+1 : ℕ) : ℤ) = a - 1 + t + 1 by push_cast; ring,
      ← insert_Icc_right_eq_Icc_add_one (by omega), sum_insert (by simp), ih]
    simp only [add_sub_cancel_right]
    ring

/-- A defined integer-index shifted factorial at a negative index is nonzero. -/
private lemma qPochhammerListInt_negSucc_ne_zero {l : List ℂ} {r : ℂ} {j : ℕ}
    (h : QIntPochhammerListDefined l r (Int.negSucc j)) :
    qPochhammerListInt l r (Int.negSucc j) ≠ 0 := by
  rcases h with h | h
  · exact absurd h (by omega)
  · unfold qPochhammerListInt
    refine List.prod_ne_zero fun hmem => ?_
    obtain ⟨x, hx, hx0⟩ := List.mem_map.1 hmem
    rw [qPochhammerInt_negSucc, inv_eq_zero] at hx0
    apply h x hx
    rw [show (-Int.negSucc j).toNat = j+1 by omega, show Int.negSucc j = -(j+1 : ℤ) by omega]
    exact hx0

open BibasicBilateral in
/-- A bilateral finite bibasic summation over the indices `-m ≤ k ≤ n` (DLMF 17.7.E22). -/
@[dlmf 17.7.E22]
theorem bibasic_bilateral_finite {a b c d p q : ℂ} (hbc : b*c≠0) (hp : p≠0) (hq : q≠0) (m n : ℕ)
    (hP : d*(1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c))≠0)
    (hF : ∀ k∈Finset.Icc (-(m:ℤ)) (n:ℤ),
      QIntPochhammerListDefined [a,b] p k ∧ QIntPochhammerListDefined [c,a*d^2/(b*c)] q k ∧
      QIntPochhammerListDefined [d*q, a*d*q/b] q k ∧
          QIntPochhammerListDefined [a*d*p/c, b*c*p/d] p k ∧
      qPochhammerListInt [d*q,a*d*q/b] q k*qPochhammerListInt [a*d*p/c,b*c*p/d] p k≠0)
    (hR : qPochhammerList [1/c,b*c/(a*d^2)] q (m+1)*qPochhammerList [1/a,1/b] p (m+1)≠0) :
    (∑ k∈Finset.Icc (-(m:ℤ)) (n:ℤ), (1-a*d*p^k*q^k)*(1-b*p^k/(d*q^k))/((1-a*d)*(1-b/d))*
      qPochhammerListInt [a,b] p k*qPochhammerListInt [c,a*d^2/(b*c)] q k/
        (qPochhammerListInt [d*q,a*d*q/b] q k*qPochhammerListInt [a*d*p/c,b*c*p/d] p k)*q^k)=
      (1-a)*(1-b)*(1-c)*(1-a*d^2/(b*c))/(d*(1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)))*
      (qPochhammerList [a*p,b*p] p n*qPochhammerList [c*q,a*d^2*q/(b*c)] q n/
        (qPochhammerList [d*q,a*d*q/b] q n*qPochhammerList [a*d*p/c,b*c*p/d] p n)-
       qPochhammerList [c/(a*d),d/(b*c)] p (m+1)*qPochhammerList [1/d,b/(a*d)] q (m+1)/
        (qPochhammerList [1/c,b*c/(a*d^2)] q (m+1)*qPochhammerList [1/a,1/b] p (m+1))) := by
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  have hc : c ≠ 0 := right_ne_zero_of_mul hbc
  have hd : d ≠ 0 := fun h => hP (by simp [h])
  have hP' : (1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)) ≠ 0 := fun h => hP (by
    linear_combination d*h)
  have hR1 := qPochhammerList_ne_zero_of_le (show 0+1 ≤ m+1 by omega) _ (left_ne_zero_of_mul hR)
  have hR2 := qPochhammerList_ne_zero_of_le (show 0+1 ≤ m+1 by omega) _ (right_ne_zero_of_mul hR)
  show ∑ k ∈ Finset.Icc (-(m:ℤ)) n, summand a b c d p q k =
    scale a b c d * (upperValue a b c d p q n - lowerValue a b c d p q m)
  set T : ℤ → ℂ := fun k => if 0 ≤ k then scale a b c d * upperValue a b c d p q k.toNat
    else scale a b c d * lowerValue a b c d p q (-k-1).toNat with hT
  have hpt : ∀ k ∈ Finset.Icc (-(m:ℤ)) n, summand a b c d p q k = T k - T (k-1) := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    rcases k with k | j
    · rcases k with _ | k
      · show summand a b c d p q 0 = T 0 - T (0-1)
        rw [summand_zero hb hc hd hP' (mul_ne_zero hR1 hR2)]
        simp [hT]
        ring
      · have h5 := (hF _ hk).2.2.2.2
        simp only [qPochhammerListInt, Int.ofNat_eq_natCast,
          qPochhammerInt_natCast] at h5
        rw [Int.ofNat_eq_natCast, summand_natCast_succ hb hc hd hq k hP' (by
          simpa only [qPochhammerList] using h5)]
        simp only [hT]
        split_ifs with h1 h2 h2
        · rw [show ((((k+1 : ℕ) : ℤ)).toNat) = k+1 by omega,
            show ((((k+1 : ℕ) : ℤ) - 1).toNat) = k by omega]
          ring
        all_goals omega
    · have hj : j + 2 ≤ m + 1 := by
        have := hk'.1; simp [Int.negSucc_eq] at this; omega
      have hR1' := qPochhammerList_ne_zero_of_le hj _ (left_ne_zero_of_mul hR)
      have hR2' := qPochhammerList_ne_zero_of_le hj _ (right_ne_zero_of_mul hR)
      obtain ⟨d1, d2, d3, d4, -⟩ := hF _ hk
      have hFj := mul_ne_zero (mul_ne_zero (mul_ne_zero
        (qPochhammerListInt_negSucc_ne_zero d1) (qPochhammerListInt_negSucc_ne_zero d2))
        (qPochhammerListInt_negSucc_ne_zero d3)) (qPochhammerListInt_negSucc_ne_zero d4)
      have hT1 : T (Int.negSucc j) = scale a b c d * lowerValue a b c d p q j := by
        simp only [hT]; split_ifs with h
        · omega
        · congr 2; omega
      have hT2 : T (Int.negSucc j - 1) = scale a b c d * lowerValue a b c d p q (j+1) := by
        simp only [hT]; split_ifs with h
        · omega
        · congr 2; omega
      rw [hT1, hT2, ← mul_sub]
      rcases eq_or_ne a 0 with rfl | ha
      · exact summand_negSucc_of_eq_zero hb hc hd hp hq j hP' hFj (mul_ne_zero hR1' hR2')
      · exact summand_negSucc ha hb hc hd hp hq j hP' hFj (mul_ne_zero hR1' hR2')
  rw [sum_congr rfl hpt, sum_Icc_sub_telescope T (by omega)]
  simp only [hT]
  split_ifs with h1 h2 h2
  · omega
  · rw [show ((n:ℤ)).toNat = n by omega, show (-(-(m:ℤ) - 1) - 1).toNat = m by omega]
    ring
  all_goals omega

/-- `2 C(k,2) + k = k²`. -/
private lemma choose_two_mul_two_add (k : ℕ) : k.choose 2 * 2 + k = k * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith

/-- Splitting a product over `range m` with one index `k` removed. -/
private lemma prod_erase_range_eq (f : ℕ → ℂ) {k m : ℕ} (hk : k < m) :
    ∏ j ∈ (range m).erase k, f j = (∏ j ∈ range k, f j) * ∏ i ∈ range (m-1-k), f (k+1+i) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = k + 1 + r := ⟨m - 1 - k, by omega⟩
  have h1 : (range (k+1+r)).erase k = range k ∪ (Finset.Ico (k+1) (k+1+r)) := by
    ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  rw [h1, prod_union (by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega),
    prod_Ico_eq_prod_range, show k + 1 + r - (k + 1) = k + 1 + r - 1 - k by omega]

/-- A factor of a nonzero finite shifted factorial is nonzero. -/
private lemma one_sub_mul_pow_ne_zero {x r : ℂ} {n i : ℕ} (h : qPochhammer x r n ≠ 0)
    (hi : i < n) : 1 - x * r^i ≠ 0 := by
  rw [qPochhammer_eq_prod, prod_ne_zero_iff] at h
  exact h i (Finset.mem_range.2 hi)

/-- `∏_{j<k} (p^k - p^j) = (-1)^k p^{C(k,2)} (p;p)_k`. -/
private lemma prod_range_pow_sub_pow {p : ℂ} (k : ℕ) :
    ∏ j ∈ range k, (p^k - p^j) = (-1)^k * p^(k.choose 2) * qPochhammer p p k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ', pow_zero]
    have h1 : ∀ j ∈ range k, p^(k+1) - p^(j+1) = p * (p^k - p^j) := fun j _ => by ring
    rw [prod_congr rfl h1, prod_mul_distrib, prod_const, card_range, ih, qPochhammer_succ,
      Nat.choose_succ_succ, Nat.choose_one_right]
    ring


open Polynomial in
/-- Gasper1995(4.1.23), with p and q swapped, gives both corrected denominator entries. -/
@[dlmf 17.7.E23]
theorem bibasic_difference_corrected {a b p q : ℂ} (hb : b≠0) (hp : p≠0) (hq : q≠0) (n : ℕ)
    (h0 : n=0 → a≠q ∧ b≠q)
    (hP : qPochhammer p p n≠0)
    (hD : ∀ k≤n, qPochhammer (a*p^k/b) p (n+1)≠0) :
    (1-a/q)*(1-b/q)*(∑ k∈range (n+1), qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q ((n:ℤ)-1)*
      (1-a*p^(2*k)/b)/(qPochhammer p p k*qPochhammer p p (n-k)*qPochhammer (a*p^k/b) p (n+1))*
      (-1:ℂ)^k*p^(k.choose 2))=(if n=0 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨haq, hbq⟩ := h0 rfl
    have hab := hD 0 le_rfl
    simp only [zero_add, qPochhammer_one, pow_zero, mul_one] at hab
    have e1 : 1 - a/q ≠ 0 := fun h => haq (by field_simp at h; linear_combination -h)
    have e2 : 1 - b/q ≠ 0 := fun h => hbq (by field_simp at h; linear_combination -h)
    have hm : ∀ x, qPochhammerInt x q (-1) = (1 - x/q)⁻¹ := fun x => by
      rw [show (-1:ℤ) = Int.negSucc 0 from rfl, qPochhammerInt_negSucc]
      simp [qPochhammer_one, div_eq_mul_inv]
    have e3 : b - a ≠ 0 := fun h => hab (by
      rw [show a = b by linear_combination -h, div_self hb, sub_self])
    simp [qPochhammerListInt, zpow_neg, hm, qPochhammer_one]
    field_simp
  · obtain ⟨N, rfl⟩ : ∃ N, n = N+1 := ⟨n-1, by omega⟩
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    refine mul_eq_zero_of_right _ ?_
    set y : ℕ → ℂ := fun k => a*p^k + b*(p^k)⁻¹ with hy
    set P : ℂ[X] := ∏ j ∈ range N, (C (1 + a*b*q^(2*j)) - C (q^j) * X) with hPdef
    have hdeg : P.natDegree ≤ N := by
      refine (natDegree_prod_le _ _).trans ?_
      refine (sum_le_card_nsmul _ _ 1 fun j _ => ?_).trans (by simp)
      refine (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_C]; exact zero_le_one) ?_)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    have hpj : ∀ j, j ≤ N+1 → 0 < j → p^j ≠ 1 := by
      intro j hj hj0 h
      apply hP
      rw [qPochhammer_eq_prod]
      exact prod_eq_zero (i := j-1) (by simp; omega) (by
        rw [← pow_succ', Nat.sub_add_cancel hj0, h, sub_self])
    have hinj : Set.InjOn y ↑(Finset.range (N+2)) := by
      intro k hk j hj hkj
      simp only [Finset.coe_range, Set.mem_Iio] at hk hj
      by_contra hne
      have h1 : p^k - p^j ≠ 0 := by
        rcases lt_or_gt_of_ne hne with h | h
        · obtain ⟨t, rfl⟩ : ∃ t, j = k + t := ⟨j - k, by omega⟩
          rw [pow_add, show p^k - p^k*p^t = p^k*(1-p^t) by ring]
          exact mul_ne_zero (pow_ne_zero _ hp) (sub_ne_zero.2 (hpj t (by omega) (by omega)).symm)
        · obtain ⟨t, rfl⟩ : ∃ t, k = j + t := ⟨k - j, by omega⟩
          rw [pow_add, show p^j*p^t - p^j = p^j*(p^t-1) by ring]
          exact mul_ne_zero (pow_ne_zero _ hp) (sub_ne_zero.2 (hpj t (by omega) (by omega)))
      have h2 : a*p^k*p^j - b ≠ 0 := by
        have := one_sub_mul_pow_ne_zero (hD k (by omega)) (show j < N+1+1 by omega)
        intro h; apply this; field_simp; linear_combination -h
      have h3 : (y k - y j) * (p^k*p^j) = (p^k - p^j) * (a*p^k*p^j - b) := by
        simp only [hy]; field_simp; ring
      rw [hkj, sub_self, zero_mul] at h3
      exact mul_ne_zero h1 h2 h3.symm
    have hL := Lagrange.coeff_eq_sum hinj (P := P) (by
      rw [card_range]
      exact (degree_le_natDegree).trans_lt (by exact_mod_cast (by omega : P.natDegree < N+2)))
    rw [card_range, show N+2-1 = N+1 by omega,
      coeff_eq_zero_of_natDegree_lt (by omega)] at hL
    set S : ℂ := ∏ j ∈ range (N+2), p^j with hS
    have hS0 : S ≠ 0 := prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ hp
    have hterm : ∀ k ∈ range (N+1+1),
        qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q (((N+1:ℕ):ℤ)-1)*(1-a*p^(2*k)/b)/
          (qPochhammer p p k*qPochhammer p p (N+1-k)*qPochhammer (a*p^k/b) p (N+1+1))*
          (-1:ℂ)^k*p^(k.choose 2) =
        (-b)^(N+1)/S * (P.eval (y k) / ∏ j ∈ (range (N+2)).erase k, (y k - y j)) := by
      intro k hk
      have hk' : k < N+2 := Finset.mem_range.1 hk
      obtain ⟨r, hr⟩ : ∃ r, N+1 = k + r := ⟨N+1-k, by omega⟩
      have hpk : p^k ≠ 0 := pow_ne_zero _ hp
      -- the polynomial value
      have hE : P.eval (y k) = qPochhammer (a*p^k) q N * qPochhammer (b*(p^k)⁻¹) q N := by
        simp only [hPdef, eval_prod, eval_sub, eval_C, eval_mul, eval_X, qPochhammer_eq_prod,
          ← prod_mul_distrib, hy]
        refine prod_congr rfl fun j _ => ?_
        field_simp
        ring
      have hlhs : qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q (((N+1:ℕ):ℤ)-1) =
          qPochhammer (a*p^k) q N * qPochhammer (b*(p^k)⁻¹) q N := by
        rw [show (((N+1:ℕ):ℤ)-1) = ((N:ℕ):ℤ) by push_cast; ring]
        simp [qPochhammerListInt, zpow_neg]
      -- the nodal product
      set Pi := ∏ j ∈ (range (N+2)).erase k, (y k - y j) with hPi
      set Cp := ∏ j ∈ (range (N+2)).erase k, (p^k*p^j) with hCp
      set B := ∏ j ∈ (range (N+2)).erase k, (a*p^k*p^j - b) with hB
      have hPiC : Pi * Cp = (∏ j ∈ (range (N+2)).erase k, (p^k - p^j)) * B := by
        rw [hPi, hCp, hB, ← prod_mul_distrib, ← prod_mul_distrib]
        refine prod_congr rfl fun j _ => ?_
        simp only [hy]; field_simp; ring
      have hA : ∏ j ∈ (range (N+2)).erase k, (p^k - p^j) =
          (-1)^k * p^(k.choose 2) * qPochhammer p p k * ((p^k)^r * qPochhammer p p r) := by
        rw [prod_erase_range_eq _ hk', prod_range_pow_sub_pow, show N+2-1-k = r by omega,
          qPochhammer_eq_prod p p r, show (p^k)^r = ∏ _i ∈ range r, p^k by simp,
          ← prod_mul_distrib]
        congr 1
        refine prod_congr rfl fun i _ => ?_
        ring
      have hBe : B * (a*p^k*p^k - b) = (-b)^(N+2) * qPochhammer (a*p^k/b) p (N+1+1) := by
        rw [hB, mul_comm, mul_prod_erase _ (fun j => a*p^k*p^j - b) hk, qPochhammer_eq_prod,
          show (-b)^(N+2) = ∏ _i ∈ range (N+1+1), (-b) by simp, ← prod_mul_distrib]
        refine prod_congr rfl fun j _ => ?_
        field_simp
        ring
      have hCe : Cp * (p^k*p^k) = (p^k)^(N+2) * S := by
        rw [hCp, mul_comm, mul_prod_erase _ (fun j => p^k*p^j) hk, prod_mul_distrib, prod_const,
          card_range]
      have hlast : a*p^k*p^k - b ≠ 0 := by
        have := one_sub_mul_pow_ne_zero (hD k (by omega)) (show k < N+1+1 by omega)
        intro h; apply this; field_simp; linear_combination -h
      have hpk1 : qPochhammer p p k ≠ 0 := qPochhammer_ne_zero_of_le hP (by omega)
      have hpr : qPochhammer p p r ≠ 0 := qPochhammer_ne_zero_of_le hP (by omega)
      have hDk := hD k (by omega)
      have hCp0 : Cp ≠ 0 := prod_ne_zero_iff.2 fun j _ => mul_ne_zero hpk (pow_ne_zero _ hp)
      have hCpv := eq_div_of_mul_eq (mul_ne_zero hpk hpk) hCe
      have hBv := eq_div_of_mul_eq hlast hBe
      have hPiv := eq_div_of_mul_eq hCp0 hPiC
      rw [hA, hBv, hCpv] at hPiv
      rw [hlhs, ← hE, show N+1-k = r by omega, hPiv]
      have hexp : (p^k)^(N+2) = p^(k.choose 2)*p^(k.choose 2)*p^k*(p^k)^r*p^k := by
        have hkk : k*k = k.choose 2 * 2 + k := (choose_two_mul_two_add k).symm
        rw [show N+2 = k+r+1 by omega, pow_add, pow_add, ← pow_mul, hkk, pow_add, pow_mul]
        ring
      rw [hexp, show p^(2*k) = p^k*p^k by ring]
      generalize eval (y k) P = E at *
      generalize qPochhammer (a*p^k/b) p (N+1+1) = D at *
      generalize qPochhammer p p k = Q1 at *
      generalize qPochhammer p p r = Q2 at *
      have hC0 : p^(k.choose 2) ≠ 0 := pow_ne_zero _ hp
      generalize p^(k.choose 2) = Ck at *
      generalize p^k = X at *
      have hb2 : a*X*X - b ≠ 0 := hlast
      have hσ : ((-1:ℂ)^k)*(-1)^k = 1 := by rw [← mul_pow]; simp
      generalize (-1:ℂ)^k = σ at *
      rw [show (-b)^(N+2) = (-b)^(N+1)*(-b) from pow_succ _ _]
      have hBn : (-b)^(N+1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 hb)
      generalize (-b)^(N+1) = Bn at *
      have hσ0 : σ ≠ 0 := left_ne_zero_of_mul_eq_one hσ
      field_simp
      linear_combination E*(b - a*X^2)*hσ
    rw [sum_congr rfl hterm, ← mul_sum, show N+1+1 = N+2 from rfl, ← hL, mul_zero]

/-- The printed argument in 17.7.19 gives a nonzero terminating series. -/
@[dlmf 17.7.E19]
theorem karlsson_printed_counter : qPhi [2] [] (1/2) (1/4)=(1/2:ℂ) := by
  have hzero (k : ℕ) (hk : 2≤k) : qPochhammer (2:ℂ) (1/2) k=0 := by
    have h := qPochhammer_recip_pow_eq_zero (q := (1/2:ℂ)) (by norm_num) (n := 1)
        (k := k) (by omega)
    norm_num at h
    exact h
  rw [qPhi_eq_basicHypergeometric (by simp)]
  unfold basicHypergeometric
  rw [tsum_eq_sum (s := range 2) (fun k hk => by
    have h := hzero k (by simp only [Finset.mem_range, not_lt] at hk; exact hk)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h,
        zero_div, zero_mul])]
  norm_num [sum_range_succ, qPochhammer]

/-- The expression printed in 17.7.23, before the primary-source corrections. -/
def bibasicDifferencePrinted (p q a b : ℂ) (n : ℕ) : ℂ :=
  (1-a/q)*(1-b/q)*∑ k∈range (n+1),
    qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q ((n:ℤ)-1)*(1-a*p^(2*k)/b)/
      (qPochhammer p p n*qPochhammer p p (n-k)*qPochhammer (a*p^k/b) q (n+1))*
      (-1:ℂ)^k*p^(k.choose 2)

/-- An exact nonzero value disproving the printed n=1 delta identity. -/
@[dlmf 17.7.E23]
theorem bibasic_printed_counter :
    bibasicDifferencePrinted (1/2) (1/3) (1/4) 1 1= -(1884/1771:ℂ) := by
  norm_num [bibasicDifferencePrinted, sum_range_succ, qPochhammerListInt,
    qPochhammerInt, qPochhammer]

end DLMF.QHypergeometric
