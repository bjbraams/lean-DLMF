/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Convergence
public import DLMF.QHypergeometric.SearsTransformation
public import DLMF.QHypergeometric.SearsLimit
public import DLMF.QSeries.RamanujanPsi
public import DLMF.QSeries.Saalschutz
public import DLMFMathlib.Analysis.SpecificLimits.PowMulPowChoose

/-!
# Further basic hypergeometric transformations (DLMF §17.9)

This file proves the transformation formulas of DLMF §17.9 for `₂φ₁`, `₃φ₂` and `₄φ₃`
series, including Sears' transformations, the nonterminating Watson transformation, quadratic
transformations and mixed-base formulas.

## Main definitions

* `qProductRatio`, `qProductRatioInf`: quotients of finite and infinite `q`-products.

## Main results

* `qPhi2_to_qPhi2_2`, `qPhi2_terminating_to_qPhi3_1`, `qPhi2_two_qPhi3_2`,
  `qPhi2_two_qPhi3_2_alternative`: DLMF 17.9.1–17.9.3.
* `qPhi2_terminating_reverse`, `qPhi2_terminating_sears`: DLMF 17.9.4–17.9.5.
* `qPhi3_sears_first`, `qPhi3_sears_second`: Sears' transformations (DLMF 17.9.6–17.9.7).
* `qPhi3_terminating_first`, `qPhi3_terminating_second`, `qPhi3_terminating_third`,
  `qPhi3_terminating_fourth`: DLMF 17.9.8–17.9.11.
* `qPhi3_three_term`, `qPhi3_connection`: DLMF 17.9.12–17.9.13.
* `qPhi4_balanced_transformations`: DLMF 17.9.14.
* `nonterminating_watson`: DLMF 17.9.16.
* `qPhi3_terminating_quadratic`, `qPhi4_square`: DLMF 17.9.17–17.9.18.
* `mixed_base_even_odd`, `mixed_base_general`: DLMF 17.9.19–17.9.20.
* `qPhi2_to_qPhi2_2'`, `mixed_base_even_odd'`, `mixed_base_general'`: stronger forms of
  17.9.1, 17.9.19 and 17.9.20 without the hypothesis `q ≠ 0`.

## Implementation notes

The functions are actual series, with their common convergence regions stated. Terminating
transformations retain the full natural truncation parameter; no condition on its size is
imposed. Lower parameters and denominator products are excluded from the `q`-lattice where the
printed quotients have poles. The general phase factor is the integer exponent of
`DLMF.QHypergeometric.Basic`, including the `₃φ₁` case. Watson's terminating transformation is
in `DLMF.Bailey`.
-/

@[expose] public noncomputable section
open Complex Finset
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- Quotient of finite q-products, retaining all parameter repetitions. -/
def qProductRatio (N : ℕ) (a b : List ℂ) (q : ℂ) : ℂ :=
  qPochhammerList a q N / qPochhammerList b q N

/-- Quotient of convergent infinite q-products. -/
def qProductRatioInf (a b : List ℂ) (q : ℂ) : ℂ :=
  qPochhammerListInf a q / qPochhammerListInf b q


/-- The weight `∏_{j<k} (c q^j - b) q^{k(k-1)/2}` of the polynomial `q`-Chu–Vandermonde sum. -/
private def chuWeight (q b : ℂ) (k : ℕ) (c : ℂ) : ℂ :=
  (∏ j ∈ range k, (c*q^j-b))*q^(k.choose 2)

/-- The recursion of `chuWeight` in `k`. -/
private lemma chuWeight_succ (q b : ℂ) (k : ℕ) (c : ℂ) :
    chuWeight q b (k+1) c = (c-b)*q^k*chuWeight q b k (c*q) := by
  simp only [chuWeight, prod_range_succ', pow_zero, mul_one]
  rw [show (k+1).choose 2 = k.choose 2 + k by
    rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]]
  rw [show ∏ j ∈ range k, (c*q^(j+1)-b) = ∏ j ∈ range k, (c*q*q^j-b) from
    prod_congr rfl fun j _ => by ring]
  ring

/-- A polynomial form of the `q`-Chu–Vandermonde sum, valid for all `b`, `c`, `q`. -/
private lemma sum_qBinom_chuWeight (q b : ℂ) (n : ℕ) : ∀ c : ℂ,
    ∑ k ∈ range (n+1), qBinom q n k*chuWeight q b k c*qPochhammer (c*q^k) q (n-k) =
      qPochhammer b q n := by
  induction n with
  | zero => intro c; simp [chuWeight, qPochhammer_zero]
  | succ n ih =>
    intro c
    rw [sum_range_succ']
    simp only [qBinom_succ_succ', add_mul, sum_add_distrib]
    have hS2 : ∑ k ∈ range (n+1), q^(n-k)*qBinom q n k*chuWeight q b (k+1) c*
        qPochhammer (c*q^(k+1)) q (n+1-(k+1)) = (c-b)*q^n*qPochhammer b q n := by
      rw [← ih (c*q), mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [chuWeight_succ, show n+1-(k+1) = n-k by omega, show c*q^(k+1) = c*q*q^k by ring,
        show q^n = q^(n-k)*q^k by rw [← pow_add, Nat.sub_add_cancel hkn]]
      ring
    have hS1 : ∑ k ∈ range (n+1), qBinom q n (k+1)*chuWeight q b (k+1) c*
        qPochhammer (c*q^(k+1)) q (n+1-(k+1)) + qBinom q (n+1) 0*chuWeight q b 0 c*
        qPochhammer (c*q^0) q (n+1-0) = (1-c*q^n)*qPochhammer b q n := by
      rw [← ih c, sum_range_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n), sum_range_succ',
        mul_add, mul_sum]
      simp only [zero_mul, add_zero, qBinom_zero_right, Nat.sub_zero, pow_zero, mul_one]
      congr 1
      · refine sum_congr rfl fun k hk => ?_
        have hkn : k < n := mem_range.mp hk
        rw [show n+1-(k+1) = (n-(k+1))+1 by omega, qPochhammer_succ,
          show c*q^(k+1)*q^(n-(k+1)) = c*q^n by
            rw [mul_assoc, ← pow_add, show k+1+(n-(k+1)) = n by omega]]
        ring
      · rw [qPochhammer_succ]; ring
    rw [show ∀ x y z : ℂ, x + y + z = (x + z) + y from fun x y z => by ring]
    rw [show (∑ k ∈ range (n+1), qBinom q n (k+1)*chuWeight q b (k+1) c*
        qPochhammer (c*q^(k+1)) q (n+1-(k+1))) +
        qBinom q (n+1) 0*chuWeight q b 0 c*qPochhammer (c*q^0) q (n+1-0) = _ from hS1]
    rw [show (∑ k ∈ range (n+1), q^(n-k)*qBinom q n k*chuWeight q b (k+1) c*
        qPochhammer (c*q^(k+1)) q (n+1-(k+1))) = _ from hS2, qPochhammer_succ]
    ring


/-- Rearranging an absolutely summable double series along antidiagonals. -/
private lemma tsum_prod_eq_tsum_sum_antidiagonal {T : ℕ × ℕ → ℂ} (h : Summable T) :
    ∑' p, T p = ∑' n, ∑ kl ∈ antidiagonal n, T kl := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq T]
  exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr h).tsum_sigma'
    (fun n ↦ (hasSum_fintype _).summable)

/-- `(q;q)_∞ ≠ 0` for `|q| < 1`. -/
private lemma qPochhammerInf_self_ne_zero'' {q : ℂ} (hq : ‖q‖<1) : qPochhammerInf q q≠0 :=
  qPochhammerInf_ne_zero hq fun n => by
    simpa [pow_succ, mul_comm] using qPochhammerInf_pow_succ_ne_zero hq n

/-- DLMF 17.9.E1 (Jackson's transformation); stronger than DLMF, which assumes `q ≠ 0`. -/
@[dlmf 17.9.E1]
theorem qPhi2_to_qPhi2_2' (a b c q z : ℂ)
    (hq : ‖q‖<1)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c,a*z,z] q)
    (hz : ‖z‖<1) :
    qPhi [a,b] [c] q (z) =
      qProductRatioInf [z*a] [z] q * qPhi [a,c/b] [c,a*z] q (b*z) := by
  have hb0 : b≠0 := hpar b (by simp)
  have hcn : ∀ n, qPochhammer c q n≠0 := fun n =>
    qPochhammer_ne_zero_of_factors hq (fun j h => hden c (by simp) j (sub_eq_zero.mp h).symm) n
  have hazn : ∀ n, qPochhammer (a*z) q n≠0 := fun n =>
    qPochhammer_ne_zero_of_factors hq (fun j h => hden (a*z) (by simp) j (sub_eq_zero.mp h).symm) n
  have hqn := qPochhammer_self_ne_zero hq
  have hzI : qPochhammerInf z q≠0 := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  set Y : ℕ → ℂ := fun k => qPochhammer a q k*chuWeight q b k c/
    (qPochhammer c q k*qPochhammer q q k)*z^k
  set T : ℕ × ℕ → ℂ := fun p =>
    Y p.1*(qPochhammer (a*q^p.1) q p.2/qPochhammer q q p.2*z^p.2)
  -- the right side, row by row
  have hrow (k : ℕ) : qProductRatioInf [z*a] [z] q*qPhiTerm [a,c/b] [c,a*z] q (b*z) k =
      ∑' m, T (k,m) := by
    simp only [T]
    rw [tsum_mul_left, ← q_binomial_theorem hq hz]
    have htri : DLMF.QSeries.TripleProduct.tri (k:ℤ) = ((k.choose 2 : ℕ) : ℤ) := by
      simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast k 0).symm
    have hW : chuWeight q b k c = qPochhammer (c/b) q k*(-1)^k*q^(k.choose 2)*b^k := by
      simp only [chuWeight, qPochhammer_eq_prod]
      rw [mul_comm (_ * _) (b^k), ← mul_assoc, ← mul_assoc, show b^k*∏ i ∈ range k,
        (1-c/b*q^i) = ∏ i ∈ range k, (b*(1-c/b*q^i)) by rw [prod_mul_distrib, prod_const,
        card_range], show (-1:ℂ)^k = ∏ _i ∈ range k, (-1:ℂ) by rw [prod_const, card_range],
        ← prod_mul_distrib]
      congr 1
      exact prod_congr rfl fun i _ => by field_simp; ring
    simp only [qProductRatioInf, qPhiTerm, qPhiExponent, qPochhammerListInf, qPochhammerList,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.length_cons,
      List.length_nil, htri, Y, hW]
    rw [qPochhammerInf_mul_qPochhammer (a := z*a) hq k, show z*a = a*z by ring,
      show a*q^k*z = a*z*q^k by ring]
    norm_num
    have := hcn k; have := hazn k; have := hqn k
    field_simp
    ring
  -- summability of the double series
  obtain ⟨C1,hC1⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero hq fun n h => hden c (by simp) n (sub_eq_zero.mp h).symm)
  obtain ⟨C2,hC2⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_self_ne_zero'' hq)
  set Ea := Real.exp (‖a‖/(1-‖q‖))
  have hC1' : 0 ≤ C1 := (norm_nonneg _).trans (hC1 0)
  have hC2' : 0 ≤ C2 := (norm_nonneg _).trans (hC2 0)
  have hYb (k : ℕ) : ‖Y k‖ ≤ Ea*C1*C2*((‖c‖+‖b‖)*‖z‖)^k*‖q‖^(k.choose 2) := by
    simp only [Y, chuWeight, div_eq_mul_inv, mul_inv, norm_mul, norm_pow, norm_prod]
    have h1 := norm_qPochhammer_le_exp (w := a) hq k
    have h2 : ∏ j ∈ range k, ‖c*q^j-b‖ ≤ (‖c‖+‖b‖)^k := by
      calc ∏ j ∈ range k, ‖c*q^j-b‖ ≤ ∏ _j ∈ range k, (‖c‖+‖b‖) := by
            gcongr with j hj
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_pow]
            gcongr
            exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
        _ = (‖c‖+‖b‖)^k := by rw [prod_const, card_range]
    have h3 := hC1 k
    have h4 := hC2 k
    rw [mul_pow]
    calc _ = ‖qPochhammer a q k‖*‖(qPochhammer c q k)⁻¹‖*‖(qPochhammer q q k)⁻¹‖*
          (∏ j ∈ range k, ‖c*q^j-b‖)*‖z‖^k*‖q‖^(k.choose 2) := by ring
      _ ≤ Ea*C1*C2*(‖c‖+‖b‖)^k*‖z‖^k*‖q‖^(k.choose 2) := by gcongr
      _ = _ := by ring
  have hYs : Summable fun k => ‖Y k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hYb
      (((summable_pow_mul_pow_choose_two (R := (‖c‖+‖b‖)*‖z‖) (by positivity) (norm_nonneg q)
        hq).mul_left (Ea*C1*C2)).congr fun k => by ring)
  have hGb (k m : ℕ) : ‖qPochhammer (a*q^k) q m/qPochhammer q q m*z^m‖ ≤ Ea*C2*‖z‖^m := by
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_pow]
    have hak : ‖a*q^k‖ ≤ ‖a‖ := by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
    have h1 : ‖qPochhammer (a*q^k) q m‖ ≤ Ea := (norm_qPochhammer_le_exp hq m).trans
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hak (by linarith [norm_nonneg q])))
    have h2 := hC2 m
    gcongr
  have hT : Summable T := by
    refine Summable.of_norm_bounded ((hYs.mul_of_nonneg
      ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (Ea*C2))
      (fun _ => norm_nonneg _) (fun _ => by positivity))) fun p => ?_
    simp only [T, norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [norm_mul] using hGb p.1 p.2) (norm_nonneg _)
  -- assemble
  have hrhs : qProductRatioInf [z*a] [z] q*qPhi [a,c/b] [c,a*z] q (b*z) = ∑' p, T p := by
    rw [qPhi, ← tsum_mul_left, hT.tsum_prod]
    exact tsum_congr hrow
  rw [hrhs, tsum_prod_eq_tsum_sum_antidiagonal hT, qPhi_eq_basicHypergeometric (by simp)]
  simp only [basicHypergeometric, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k m => T (k,m)) n]
  have hS := sum_qBinom_chuWeight q b n c
  have hS' : ∑ k ∈ range (n+1), chuWeight q b k c/(qPochhammer c q k*qPochhammer q q k*
      qPochhammer q q (n-k)) = qPochhammer b q n/(qPochhammer c q n*qPochhammer q q n) := by
    rw [← hS, sum_div]
    refine sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hB := qBinom_mul_qPochhammer q k (n-k)
    have hC := qPochhammer_add c q k (n-k)
    rw [Nat.add_sub_cancel' hkn] at hB hC
    rw [← hB, hC]
    have := hcn k; have := hcn n; have := hqn k; have := hqn (n-k)
    have hcc : qPochhammer (c*q^k) q (n-k) ≠ 0 := by
      intro h; apply hcn n; rw [hC, h, mul_zero]
    have hqb : qBinom q n k ≠ 0 := by intro h; apply hqn n; rw [← hB, h]; ring
    field_simp
  rw [show qPochhammer a q n*qPochhammer b q n/(qPochhammer c q n*qPochhammer q q n)*z^n =
    qPochhammer a q n*z^n*(qPochhammer b q n/(qPochhammer c q n*qPochhammer q q n)) by ring,
    ← hS', mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hA := qPochhammer_add a q k (n-k)
  rw [Nat.add_sub_cancel' hkn] at hA
  have hz' : z^n = z^k*z^(n-k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  simp only [T, Y]
  rw [hA, hz']
  have := hcn k; have := hqn k; have := hqn (n-k)
  field_simp

/-- DLMF 17.9.E1: qPhi2 to qPhi2 2. -/
@[dlmf 17.9.E1]
theorem qPhi2_to_qPhi2_2 (a b c q z : ℂ)
    (hq : ‖q‖<1) (_hq0 : q≠0)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c,a*z,z] q)
    (hz : ‖z‖<1) :
    qPhi [a,b] [c] q (z) =
      qProductRatioInf [z*a] [z] q * qPhi [a,c/b] [c,a*z] q (b*z) :=
  qPhi2_to_qPhi2_2' a b c q z hq hpar hden hz

/-- DLMF 17.9.E2: qPhi2 terminating to qPhi3 1. -/
@[dlmf 17.9.E2]
theorem qPhi2_terminating_to_qPhi3_1 (n : ℕ) (b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [c,b*q^(1-(n:ℤ))/c] q) :
    qPhi [q^(-(n:ℤ)),b] [c] q (z) =
      qProductRatio n [c/b] [c] q * b^n * qPhi [q^(-(n:ℤ)),b,q/z] [b*q^(1-(n:ℤ))/c] q (z/c) := by
  have hreg : ∀ x ∈ [c,b*q^(1-(n:ℤ))/c], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have hz' : ∀ x : ℂ, x*q^(1-(n:ℤ)) = x*q*q⁻¹^n := fun x => by
    rw [SearsTransformation.zpow_one_sub_natCast hq0]; ring
  have hC := hreg c (by simp)
  have h₁ := hreg (b*q^(1-(n:ℤ))/c) (by simp)
  rw [hz'] at h₁
  have H := phiSum_two_one_three_one n hq0 hq (hpar b (by simp)) (hpar c (by simp))
    (hpar z (by simp)) hC h₁
  rw [qPhi_three_one_eq_sum hq0, qPhi_two_one_eq_phiSum hq0, hz']
  simp only [qProductRatio, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hC]
  linear_combination H

/-- DLMF 17.9.E3: qPhi2 two qPhi3 2. -/
@[dlmf 17.9.E3]
theorem qPhi2_two_qPhi3_2 (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [c,b*z/c,z,c/(b*z),b*z,b*z*q/c,c*q/(b*z)] q)
    (hz : ‖z‖<1) :
    qPhi [a,b] [c] q (z) =
      qProductRatioInf [a*b*z/c] [b*z/c] q * qPhi [a, c/b, 0] [c, c*q/(b*z)] q (q) +
          qProductRatioInf [a, b*z, c/b] [c, z, c/(b*z)] q *
          qPhi [z, a*b*z/c, 0] [b*z, b*z*q/c] q (q) := by
  sorry

/-- DLMF 17.9.E3_5: qPhi2 two qPhi3 2 alternative. -/
@[dlmf 17.9.E3_5]
theorem qPhi2_two_qPhi3_2_alternative (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c], x≠0)
    (hden : QDenominatorRegular [c,c/(a*b),a*b/c,z,q*a*b/c,q*c/(a*b),0] q)
    (hz : ‖z‖<1) :
    qPhi [a,b] [c] q (z) =
      qProductRatioInf [c/a, c/b] [c, c/(a*b)] q * qPhi [a, b, a*b*z/c] [q*a*b/c, 0] q (q) +
          qProductRatioInf [a, b, a*b*z/c] [c, a*b/c, z] q *
          qPhi [c/a, c/b, z] [q*c/(a*b), 0] q (q) := by
  sorry

/-- DLMF 17.9.E4: qPhi2 terminating reverse. -/
@[dlmf 17.9.E4]
theorem qPhi2_terminating_reverse (n : ℕ) (b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [c,b*q^(1-(n:ℤ))/c,0] q) :
    qPhi [q^(-(n:ℤ)),b] [c] q (z) =
      qProductRatio n [c/b] [c] q * (b*z/q)^n *
          qPhi [q^(-(n:ℤ)), q/z, q^(1-(n:ℤ))/c] [b*q^(1-(n:ℤ))/c, 0] q (q) := by
  have hreg : ∀ x ∈ [c,b*q^(1-(n:ℤ))/c,0], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have hz' : ∀ x : ℂ, x*q^(1-(n:ℤ)) = x*q*q⁻¹^n := fun x => by
    rw [SearsTransformation.zpow_one_sub_natCast hq0]; ring
  have hz1 : q^(1-(n:ℤ)) = q*q⁻¹^n := SearsTransformation.zpow_one_sub_natCast hq0 n
  have hb := hpar b (by simp)
  have hc := hpar c (by simp)
  have hz := hpar z (by simp)
  have hQ0 : q⁻¹^n ≠ 0 := pow_ne_zero _ (inv_ne_zero hq0)
  have hC := hreg c (by simp)
  have h₁ := hreg (b*q^(1-(n:ℤ))/c) (by simp)
  rw [hz'] at h₁
  have H5 := phiSum_two_one_sears z n hq0 hq hb hc hC h₁
  have H8 := searsSum_three_two_first (c := b*z*q⁻¹^n/c) (d := b*q*q⁻¹^n/c) (e := 0) n hq0 hq
    hb (div_ne_zero (by simp [*]) hc)
    (div_ne_zero (by simp [*]) hc) h₁ (by simp [qPochhammer_zero_param])
    (by simp [qPochhammer_zero_param])
  simp only [mul_zero, zero_div, qPochhammer_zero_param, one_mul, mul_one] at H8
  rw [show b * q * q⁻¹ ^ n / c / b = q * q⁻¹ ^ n / c by field_simp,
    show b * q * q⁻¹ ^ n / c / (b * z * q⁻¹ ^ n / c) = q / z by field_simp,
    show b * (b * z * q⁻¹ ^ n / c) / (b * q * q⁻¹ ^ n / c) = b * z / q by field_simp] at H8
  have hs : searsSum q n (q * q⁻¹ ^ n / c) (q / z) 0 (b * q * q⁻¹ ^ n / c) 0 0 =
      searsSum q n (q / z) (q * q⁻¹ ^ n / c) 0 (b * q * q⁻¹ ^ n / c) 0 0 := by
    unfold searsSum; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hs] at H8
  rw [qPhi_three_two_eq_searsSum hq0, qPhi_two_one_eq_phiSum hq0, hz', hz1]
  simp only [qProductRatio, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hC, mul_assoc, ← H8]
  linear_combination H5

/-- DLMF 17.9.E5: qPhi2 terminating sears. -/
@[dlmf 17.9.E5]
theorem qPhi2_terminating_sears (n : ℕ) (b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c], x≠0)
    (hden : QDenominatorRegular [c,b*q^(1-(n:ℤ))/c,0] q) :
    qPhi [q^(-(n:ℤ)),b] [c] q (z) =
      qProductRatio n [c/b] [c] q *
          qPhi [q^(-(n:ℤ)), b, b*z*q^(-(n:ℤ))/c] [b*q^(1-(n:ℤ))/c, 0] q (q) := by
  have hreg : ∀ x ∈ [c,b*q^(1-(n:ℤ))/c,0], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have hz' : ∀ x : ℂ, x*q^(1-(n:ℤ)) = x*q*q⁻¹^n := fun x => by
    rw [SearsTransformation.zpow_one_sub_natCast hq0]; ring
  have hzn : q^(-(n:ℤ)) = q⁻¹^n := by rw [zpow_neg, zpow_natCast, inv_pow]
  have hC := hreg c (by simp)
  have h₁ := hreg (b*q^(1-(n:ℤ))/c) (by simp)
  rw [hz'] at h₁
  have H := phiSum_two_one_sears z n hq0 hq (hpar b (by simp)) (hpar c (by simp)) hC h₁
  rw [qPhi_three_two_eq_searsSum hq0, qPhi_two_one_eq_phiSum hq0, hzn, hz']
  simp only [qProductRatio, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [div_mul_eq_mul_div, eq_div_iff hC]
  linear_combination H

/-- DLMF 17.9.E6: qPhi3 sears first. -/
@[dlmf 17.9.E6]
theorem qPhi3_sears_first (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c], x≠0)
    (hden : QDenominatorRegular [d,e,d*e/(a*b*c),d*e/(b*c)] q)
    (hz : ‖d*e/(a*b*c)‖<1)
    (he : ‖e/a‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [e/a, d*e/(b*c)] [e, d*e/(a*b*c)] q *
          qPhi [a, d/b, d/c] [d, d*e/(b*c)] q (e/a) := by
  have ha0 : a ≠ 0 := hpar a (by simp)
  have hb0 : b ≠ 0 := hpar b (by simp)
  have hc0 : c ≠ 0 := hpar c (by simp)
  have hI0 : qPochhammerInf (0 : ℂ) q = 1 := by simp [qPochhammerInf]
  by_cases he0 : e = 0
  · subst e
    simp [qProductRatioInf, qPochhammerListInf, hI0]
  by_cases hd0 : d = 0
  · subst d
    have hEI : qPochhammerInf e q ≠ 0 := qPochhammerInf_ne_zero hq
      fun j h => hden e (by simp) j (sub_eq_zero.mp h).symm
    have hWI := qPochhammerInf_ne_zero_of_norm_lt_one he hq
    have hG := one_phi_zero (a := a) hq he
    rw [show a * (e / a) = e by field_simp] at hG
    simp only [zero_mul, zero_div, qPhi_zero, qProductRatioInf, qPochhammerListInf,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hI0, mul_one]
    rw [SearsLimit.qPhi_three_two_zero_parameters, hG]
    field_simp
  have hz0 : d * e / (a * b * c) ≠ 0 :=
    div_ne_zero (mul_ne_zero hd0 he0) (mul_ne_zero (mul_ne_zero ha0 hb0) hc0)
  have hbal : d * e = a * b * c * (d * e / (a * b * c)) := by field_simp
  have hv : a * (d * e / (a * b * c)) = d * e / (b * c) := by field_simp
  have hreg : QDenominatorRegular [d, e, a * (d * e / (a * b * c))] q := by
    intro x hx j
    rw [hv] at hx
    exact hden x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) j
  have H := SearsLimit.first_transformation hq0 hq ha0 hb0 hc0 hd0 he0 hz0 hz he hbal hreg
  simpa only [hv, qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one] using H

/-- DLMF 17.9.E7: qPhi3 sears second. -/
@[dlmf 17.9.E7]
theorem qPhi3_sears_second (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c], x≠0)
    (hden : QDenominatorRegular [d,e,d*e/(a*b*c),d*e/(a*b),d*e/(b*c)] q)
    (hz : ‖d*e/(a*b*c)‖<1)
    (hb : ‖b‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [b, d*e/(a*b), d*e/(b*c)] [d, e, d*e/(a*b*c)] q *
          qPhi [d/b, e/b, d*e/(a*b*c)] [d*e/(a*b), d*e/(b*c)] q (b) := by
  have ha0 : a ≠ 0 := hpar a (by simp)
  have hb0 : b ≠ 0 := hpar b (by simp)
  have hc0 : c ≠ 0 := hpar c (by simp)
  have hI0 : qPochhammerInf (0 : ℂ) q = 1 := by simp [qPochhammerInf]
  have hBI := qPochhammerInf_ne_zero_of_norm_lt_one hb hq
  by_cases he0 : e = 0
  · subst e
    have hDI : qPochhammerInf d q ≠ 0 := qPochhammerInf_ne_zero hq
      fun j h => hden d (by simp) j (sub_eq_zero.mp h).symm
    have hG := one_phi_zero (a := d / b) hq hb
    rw [show d / b * b = d by field_simp] at hG
    simp only [mul_zero, zero_div, qPhi_zero, qProductRatioInf, qPochhammerListInf,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hI0, mul_one]
    rw [SearsLimit.qPhi_three_two_zero_parameters, hG]
    field_simp
  by_cases hd0 : d = 0
  · subst d
    have hEI : qPochhammerInf e q ≠ 0 := qPochhammerInf_ne_zero hq
      fun j h => hden e (by simp) j (sub_eq_zero.mp h).symm
    have hG := one_phi_zero (a := e / b) hq hb
    rw [show e / b * b = e by field_simp] at hG
    simp only [zero_mul, zero_div, qPhi_zero, qProductRatioInf, qPochhammerListInf,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hI0, mul_one, one_mul]
    rw [SearsLimit.qPhi_three_two_zero_parameters_middle, hG]
    field_simp
  have hz0 : d * e / (a * b * c) ≠ 0 :=
    div_ne_zero (mul_ne_zero hd0 he0) (mul_ne_zero (mul_ne_zero ha0 hb0) hc0)
  have hbal : d * e = a * b * c * (d * e / (a * b * c)) := by field_simp
  have H := SearsLimit.second_transformation hq0 hq ha0 hb0 hc0 hd0 he0 hz0 hz hb hbal hden
  simpa only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc] using H

/-- DLMF 17.9.E8: qPhi3 terminating first. -/
@[dlmf 17.9.E8]
theorem qPhi3_terminating_first (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,d], x≠0)
    (hden : QDenominatorRegular [d,e,d*e/(b*c)] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (q) =
      qProductRatio n [d*e/(b*c)] [e] q * (b*c/d)^n *
          qPhi [q^(-(n:ℤ)), d/b, d/c] [d, d*e/(b*c)] q (q) := by
  have hreg : ∀ x ∈ [d,e,d*e/(b*c)], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have hE := hreg e (by simp)
  have H := searsSum_three_two_first n hq0 hq (hpar b (by simp)) (hpar c (by simp))
    (hpar d (by simp)) (hreg d (by simp)) hE (hreg (d*e/(b*c)) (by simp))
  simp only [qPhi_three_two_eq_searsSum hq0, qProductRatio, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hE]
  linear_combination H

/-- DLMF 17.9.E9: qPhi3 terminating second. -/
@[dlmf 17.9.E9]
theorem qPhi3_terminating_second (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q^(1-(n:ℤ))/e] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (q) =
      qProductRatio n [e/c] [e] q * c^n *
          qPhi [q^(-(n:ℤ)), c, d/b] [d, c*q^(1-(n:ℤ))/e] q (b*q/e) := by
  have hreg : ∀ x ∈ [d,e,c*q^(1-(n:ℤ))/e], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have hz' : ∀ x : ℂ, x*q^(1-(n:ℤ)) = x*q*q⁻¹^n := fun x => by
    rw [SearsTransformation.zpow_one_sub_natCast hq0]; ring
  have hE := hreg e (by simp)
  have h₁ := hreg (c*q^(1-(n:ℤ))/e) (by simp)
  rw [hz'] at h₁
  have H := phiSum_three_two_second n hq0 hq (hpar b (by simp)) (hpar c (by simp))
    (hpar e (by simp)) (hreg d (by simp)) hE h₁
  simp only [qPhi_three_two_eq_searsSum hq0, qPhi_three_two_eq_phiSum hq0, qProductRatio,
    qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hz']
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hE]
  linear_combination H

/-- DLMF 17.9.E10: qPhi3 terminating third. -/
@[dlmf 17.9.E10]
theorem qPhi3_terminating_third (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q^(1-(n:ℤ))/e] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (d*e*q^n/(b*c)) =
      qProductRatio n [e/c] [e] q * qPhi [q^(-(n:ℤ)),c,d/b] [d,c*q^(1-(n:ℤ))/e] q (q) := by
  have hreg : ∀ x ∈ [d,e,c*q^(1-(n:ℤ))/e], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have hz' : ∀ x : ℂ, x*q^(1-(n:ℤ)) = x*q*q⁻¹^n := fun x => by
    rw [SearsTransformation.zpow_one_sub_natCast hq0]; ring
  have hE := hreg e (by simp)
  have h₁ := hreg (c*q^(1-(n:ℤ))/e) (by simp)
  rw [hz'] at h₁
  have H := phiSum_three_two_third n hq0 hq (hpar b (by simp)) (hpar c (by simp))
    (hpar e (by simp)) (hreg d (by simp)) hE h₁
  simp only [qPhi_three_two_eq_searsSum hq0, qPhi_three_two_eq_phiSum hq0, qProductRatio,
    qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hz']
  rw [div_mul_eq_mul_div, eq_div_iff hE]
  linear_combination H

/-- DLMF 17.9.E11: qPhi3 terminating fourth. -/
@[dlmf 17.9.E11]
theorem qPhi3_terminating_fourth (n : ℕ) (b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [c,d,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q^(1-(n:ℤ))/e,c*q^(1-(n:ℤ))/d] q) :
    qPhi [q^(-(n:ℤ)),b,c] [d,e] q (q) =
      qProductRatio n [e/c, d/c] [e, d] q * c^n *
          qPhi [q^(-(n:ℤ)), c, c*b*q^(1-(n:ℤ))/(d*e)] [c*q^(1-(n:ℤ))/e, c*q^(1-(n:ℤ))/d] q (q) := by
  have hreg : ∀ x ∈ [d,e,c*q^(1-(n:ℤ))/e,c*q^(1-(n:ℤ))/d], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have hz' : ∀ x : ℂ, x*q^(1-(n:ℤ)) = x*q*q⁻¹^n := fun x => by
    rw [SearsTransformation.zpow_one_sub_natCast hq0]; ring
  have hD := hreg d (by simp)
  have hE := hreg e (by simp)
  have h₁ := hreg (c*q^(1-(n:ℤ))/e) (by simp)
  have h₂ := hreg (c*q^(1-(n:ℤ))/d) (by simp)
  rw [hz'] at h₁ h₂
  have H := searsSum_three_two_fourth (b := b) n hq0 hq (hpar c (by simp)) (hpar d (by simp))
    (hpar e (by simp)) hD hE h₁ h₂
  simp only [qPhi_three_two_eq_searsSum hq0, qProductRatio, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, hz']
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hE hD)]
  linear_combination H

/-- DLMF 17.9.E12: qPhi3 three term. -/
@[dlmf 17.9.E12]
theorem qPhi3_three_term (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,d,e], x≠0)
    (hden : QDenominatorRegular [d,e,c*q/d,q/a,e/(b*c),b*c*q/e,d/q,b*q/d,q^2/d,e*q/d,c*q/a] q)
    (hz : ‖d*e/(a*b*c)‖<1)
    (hb : ‖b*q/d‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [e/b, e/c, c*q/a, q/d] [e, c*q/d, q/a, e/(b*c)] q *
          qPhi [c, d/a, c*q/e] [c*q/a, b*c*q/e] q (b*q/d) -
          qProductRatioInf [q/d, e*q/d, b, c, d/a, d*e/(b*c*q), b*c*q^2/(d*e)]
          [d/q, e, b*q/d, c*q/d, q/a, e/(b*c), b*c*q/e] q *
          qPhi [a*q/d, b*q/d, c*q/d] [q^2/d, e*q/d] q (d*e/(a*b*c)) := by
  sorry

/-- DLMF 17.9.E13: qPhi3 connection. -/
@[dlmf 17.9.E13]
theorem qPhi3_connection (a b c d e q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,e], x≠0)
    (hden : QDenominatorRegular [d,e,e/(b*c),b*c/e,d*e/(a*b*c),b*c*q/e,d*e/(b*c),e*q/(b*c)] q)
    (hz : ‖d*e/(a*b*c)‖<1) :
    qPhi [a,b,c] [d,e] q (d*e/(a*b*c)) =
      qProductRatioInf [e/b, e/c] [e, e/(b*c)] q * qPhi [d/a, b, c] [d, b*c*q/e] q (q) +
          qProductRatioInf [d/a, b, c, d*e/(b*c)] [d, e, b*c/e, d*e/(a*b*c)] q *
          qPhi [e/b, e/c, d*e/(a*b*c)] [d*e/(b*c), e*q/(b*c)] q (q) := by
  sorry

/-- DLMF 17.9.E14: qPhi4 balanced transformations. -/
@[dlmf 17.9.E14]
theorem qPhi4_balanced_transformations (n : ℕ) (a b c d e f q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,d,e,f], x≠0)
    (hden : QDenominatorRegular
        [d, e, f, a*q^(1-(n:ℤ))/e, a*q^(1-(n:ℤ))/f, e*f/(a*b), e*f/(a*c), e*f/(a*b*c),
        q^(1-(n:ℤ))/a] q)
    (hbal : d*e*f=a*b*c*q^(1-(n:ℤ))) :
    (qPhi [q^(-(n:ℤ)), a, b, c] [d, e, f] q (q)) = qProductRatio n [e/a, f/a] [e, f] q * a^n *
        qPhi [q^(-(n:ℤ)), a, d/b, d/c] [d, a*q^(1-(n:ℤ))/e, a*q^(1-(n:ℤ))/f] q (q) ∧
    (qPhi [q^(-(n:ℤ)), a, b, c] [d, e, f] q (q)) =
        qProductRatio n [a, e*f/(a*b), e*f/(a*c)] [e, f, e*f/(a*b*c)] q *
        qPhi [q^(-(n:ℤ)), e/a, f/a, e*f/(a*b*c)] [e*f/(a*b), e*f/(a*c), q^(1-(n:ℤ))/a] q (q) := by
  have hreg : ∀ x ∈ [d, e, f, a*q^(1-(n:ℤ))/e, a*q^(1-(n:ℤ))/f, e*f/(a*b), e*f/(a*c),
      e*f/(a*b*c), q^(1-(n:ℤ))/a], qPochhammer x q n ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hden hx n
  have ha : a≠0 := hpar a (by simp)
  have hb : b≠0 := hpar b (by simp)
  have hc : c≠0 := hpar c (by simp)
  have hd : d≠0 := hpar d (by simp)
  have he : e≠0 := hpar e (by simp)
  have hf : f≠0 := hpar f (by simp)
  have hz : q^(1-(n:ℤ)) = q*q⁻¹^n := SearsTransformation.zpow_one_sub_natCast hq0 n
  have hz' : ∀ x : ℂ, x*q^(1-(n:ℤ)) = x*q*q⁻¹^n := fun x => by rw [hz]; ring
  have hbal' : d*e*f = a*b*c*q*q⁻¹^n := by rw [hbal, hz']
  have hD := hreg d (by simp)
  have hE := hreg e (by simp)
  have hF := hreg f (by simp)
  have h₁ := hreg (a*q^(1-(n:ℤ))/e) (by simp)
  have h₂ := hreg (a*q^(1-(n:ℤ))/f) (by simp)
  have h₃ := hreg (e*f/(a*b)) (by simp)
  have h₄ := hreg (e*f/(a*c)) (by simp)
  have h₅ := hreg (e*f/(a*b*c)) (by simp)
  have h₆ := hreg (q^(1-(n:ℤ))/a) (by simp)
  rw [hz'] at h₁ h₂
  rw [hz] at h₆
  simp only [qPhi_four_three_eq_searsSum hq0, qProductRatio, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, hz]
  constructor
  · have H := searsSum_transformation_first n hq0 hq ha hb hc hd he hf hbal' hD hE hF h₁ h₂
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hE hF)]
    rw [show a*(q*q⁻¹^n) = a*q*q⁻¹^n by ring]
    linear_combination H
  · have H := searsSum_transformation_second n hq0 hq ha hb hc hd he hf hbal' hD hE hF h₃ h₄ h₆
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hE (mul_ne_zero hF h₅))]
    linear_combination H

/-- DLMF 17.9.E16: nonterminating watson. -/
@[dlmf 17.9.E16]
theorem nonterminating_watson (a b c d e f q : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [a,b,c,d,e,f], x≠0)
    (hden : QDenominatorRegular
        [a^(1/2:ℂ), -a^(1/2:ℂ), a*q/b, a*q/c, a*q/d, a*q/e, a*q/f, a*q/(d*e*f), d*e*f/a,
        a^2*q^2/(b*c*d*e*f), d*e*f/(a*q), a^2*q^2/(b*d*e*f), a^2*q^2/(c*d*e*f), a*q^2/(d*e*f)] q)
    (hz : ‖a^2*q^2/(b*c*d*e*f)‖<1) :
    qPhi [a, q*a^(1/2:ℂ), -q*a^(1/2:ℂ), b, c, d, e, f]
        [a^(1/2:ℂ), -a^(1/2:ℂ), a*q/b, a*q/c, a*q/d, a*q/e, a*q/f] q (a^2*q^2/(b*c*d*e*f)) =
      qProductRatioInf [a*q, a*q/(d*e), a*q/(d*f), a*q/(e*f)] [a*q/d, a*q/e, a*q/f, a*q/(d*e*f)] q *
          qPhi [a*q/(b*c), d, e, f] [a*q/b, a*q/c, d*e*f/a] q (q) +
          qProductRatioInf [a*q, a*q/(b*c), d, e, f, a^2*q^2/(b*d*e*f), a^2*q^2/(c*d*e*f)]
          [a*q/b, a*q/c, a*q/d, a*q/e, a*q/f, a^2*q^2/(b*c*d*e*f), d*e*f/(a*q)] q *
          qPhi [a*q/(d*e), a*q/(d*f), a*q/(e*f), a^2*q^2/(b*c*d*e*f)]
          [a^2*q^2/(b*d*e*f), a^2*q^2/(c*d*e*f), a*q^2/(d*e*f)] q (q) := by
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

/-- The `q`-binomial sum along a shifted argument `w Q^j`. -/
private lemma tsum_qBinomial_shift {a w Q : ℂ} (hQ : ‖Q‖<1) (hw : ‖w‖<1)
    (hreg : ∀ j : ℕ, 1-a*w*Q^j≠0) (j : ℕ) :
    (∑' n : ℕ, qPochhammer a Q n/qPochhammer Q Q n*(w*Q^j)^n) =
      qPochhammerInf (a*w) Q/qPochhammerInf w Q*qPochhammer w Q j/qPochhammer (a*w) Q j := by
  have hwf := one_sub_mul_pow_ne_zero_of_norm hw hQ
  rw [← q_binomial_theorem hQ (norm_mul_pow_lt_one hw hQ j), ← mul_assoc,
    qPochhammerInf_mul_qPochhammer (a := a * w) hQ j, qPochhammerInf_mul_qPochhammer (a := w) hQ j]
  field [qPochhammer_ne_zero_of_factors hQ hreg j, qPochhammer_ne_zero_of_factors hQ hwf j,
    qPochhammerInf_shift_ne_zero hQ hwf j]

/-- DLMF 17.9.E19: mixed base even odd; stronger than DLMF, which assumes `q ≠ 0`. -/
@[dlmf 17.9.E19]
theorem mixed_base_even_odd' (a b c q z : ℂ)
    (hq : ‖q‖<1)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c,a*z] q)
    (hb : ‖b‖<1)
    (hz : ‖z‖<1) :
    (∑' n : ℕ, qPochhammer a (q^2) n * qPochhammer b q n * z^n /
        (qPochhammer (q^2) (q^2) n * qPochhammer c q n)) =
      qPochhammerInf b q * qPochhammerInf (a*z) (q^2) /
          (qPochhammerInf c q * qPochhammerInf z (q^2)) *
          (∑' n : ℕ, qPochhammer (c/b) q (2*n) * qPochhammer z (q^2) n * b^(2*n) /
          (qPochhammer q q (2*n) * qPochhammer (a*z) (q^2) n)) + qPochhammerInf b q *
          qPochhammerInf (a*z*q) (q^2) / (qPochhammerInf c q * qPochhammerInf (z*q) (q^2)) *
          (∑' n : ℕ, qPochhammer (c/b) q (2*n+1) * qPochhammer (z*q) (q^2) n * b^(2*n+1) /
          (qPochhammer q q (2*n+1) * qPochhammer (a*z*q) (q^2) n)) := by
  have hb0 : b≠0 := hpar b (by simp)
  set Q := q^2 with hQdef
  have hQ : ‖Q‖<1 := by rw [hQdef, norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  let A (n : ℕ) := qPochhammer a Q n / qPochhammer Q Q n
  let B (m : ℕ) := qPochhammer (c / b) q m / qPochhammer q q m
  let K := qPochhammerInf b q / qPochhammerInf c q
  let D (n m : ℕ) := (A n * z ^ n) * (B m * b ^ m) * q ^ (n * m)
  have hcf : ∀ j : ℕ, 1 - c * q ^ j ≠ 0 := fun j => sub_ne_zero.mpr (hden c (by simp) j).symm
  have hazf : ∀ j : ℕ, 1 - a * z * q ^ j ≠ 0 :=
    fun j => sub_ne_zero.mpr (hden (a*z) (by simp) j).symm
  have hbf := one_sub_mul_pow_ne_zero_of_norm hb hq
  have hzq : ‖z*q‖<1 := by
    rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg z) hq.le).trans_lt hz
  have hleft (n : ℕ) : qPochhammer b q n / qPochhammer c q n =
      K * ∑' m : ℕ, B m * (b * q ^ n) ^ m := by
    dsimp only [B]
    rw [← q_binomial_theorem hq (norm_mul_pow_lt_one hb hq n)]
    have he : c / b * (b * q ^ n) = c * q ^ n := by field [hb0]
    rw [he]
    dsimp only [K]
    rw [qPochhammerInf_mul_qPochhammer (a := b) hq n,
      qPochhammerInf_mul_qPochhammer (a := c) hq n]
    field [qPochhammer_ne_zero_of_factors hq hcf n,
      qPochhammerInf_shift_ne_zero hq hbf n, qPochhammerInf_shift_ne_zero hq hcf n]
  have heven (j : ℕ) : (∑' n : ℕ, A n * (z * q ^ (2*j)) ^ n) =
      qPochhammerInf (a*z) Q/qPochhammerInf z Q*qPochhammer z Q j/qPochhammer (a*z) Q j := by
    rw [pow_mul, ← hQdef]
    exact tsum_qBinomial_shift hQ hz (fun i => by
      rw [hQdef, ← pow_mul]; exact hazf (2*i)) j
  have hodd (j : ℕ) : (∑' n : ℕ, A n * (z * q ^ (2*j+1)) ^ n) =
      qPochhammerInf (a*z*q) Q/qPochhammerInf (z*q) Q*qPochhammer (z*q) Q j/
        qPochhammer (a*z*q) Q j := by
    rw [show z*q^(2*j+1) = z*q*Q^j by rw [hQdef, ← pow_mul]; ring]
    have := tsum_qBinomial_shift (a := a) hQ hzq (fun i => by
      rw [hQdef, ← pow_mul, show a*(z*q)*q^(2*i) = a*z*q^(2*i+1) by ring]
      exact hazf (2*i+1)) j
    rw [show a*(z*q) = a*z*q by ring] at this
    exact this
  have hsumA : Summable (fun n : ℕ => ‖A n * z ^ n‖) :=
    (summable_q_binomial_series (a := a) hQ hz).norm
  have hsumB : Summable (fun m : ℕ => ‖B m * b ^ m‖) :=
    (summable_q_binomial_series (a := c / b) hq hb).norm
  have hs : Summable (Function.uncurry D) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun nm => ?_) (hsumA.mul_norm hsumB)
    dsimp only [Function.uncurry, D]
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg q) hq.le)
  have hrow (n : ℕ) : (∑' m : ℕ, D n m) =
      A n * z ^ n * ∑' m : ℕ, B m * (b * q ^ n) ^ m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp only [D]
    rw [mul_pow, ← pow_mul]
    ring
  let G (m : ℕ) := B m * b ^ m * ∑' n : ℕ, A n * (z * q ^ m) ^ n
  have hcol (m : ℕ) : (∑' n : ℕ, D n m) = G m := by
    simp only [G]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [D]
    rw [mul_pow, ← pow_mul, Nat.mul_comm m n]
    ring
  have hG : Summable G := (hs.prod_symm.prod).congr fun m => hcol m
  have hlhs : (∑' n : ℕ, qPochhammer a Q n * qPochhammer b q n * z^n /
        (qPochhammer Q Q n * qPochhammer c q n)) = K * ∑' m : ℕ, G m := by
    rw [← tsum_congr hcol, hs.tsum_comm]
    calc
      _ = ∑' n : ℕ, A n * z ^ n * (qPochhammer b q n / qPochhammer c q n) := by
        apply tsum_congr
        intro n
        dsimp only [A]
        ring
      _ = _ := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [hleft, hrow]
        ring
  rw [hlhs, ← tsum_even_add_odd (hG.comp_injective (mul_right_injective₀ two_ne_zero))
    (hG.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero))),
    mul_add, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  · refine tsum_congr fun j => ?_
    simp only [G, heven, B]
    dsimp only [K]
    ring
  · refine tsum_congr fun j => ?_
    simp only [G, B, hodd]
    dsimp only [K]
    ring

/-- DLMF 17.9.E19: mixed base even odd. -/
@[dlmf 17.9.E19]
theorem mixed_base_even_odd (a b c q z : ℂ)
    (hq : ‖q‖<1) (_hq0 : q≠0)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c,a*z] q)
    (hb : ‖b‖<1)
    (hz : ‖z‖<1) :
    (∑' n : ℕ, qPochhammer a (q^2) n * qPochhammer b q n * z^n /
        (qPochhammer (q^2) (q^2) n * qPochhammer c q n)) =
      qPochhammerInf b q * qPochhammerInf (a*z) (q^2) /
          (qPochhammerInf c q * qPochhammerInf z (q^2)) *
          (∑' n : ℕ, qPochhammer (c/b) q (2*n) * qPochhammer z (q^2) n * b^(2*n) /
          (qPochhammer q q (2*n) * qPochhammer (a*z) (q^2) n)) + qPochhammerInf b q *
          qPochhammerInf (a*z*q) (q^2) / (qPochhammerInf c q * qPochhammerInf (z*q) (q^2)) *
          (∑' n : ℕ, qPochhammer (c/b) q (2*n+1) * qPochhammer (z*q) (q^2) n * b^(2*n+1) /
          (qPochhammer q q (2*n+1) * qPochhammer (a*z*q) (q^2) n)) :=
  mixed_base_even_odd' a b c q z hq hpar hden hb hz

/-- DLMF 17.9.E20: mixed base general; stronger than DLMF, which assumes `q ≠ 0`. -/
@[dlmf 17.9.E20]
theorem mixed_base_general' (a b c q z : ℂ)
    (hq : ‖q‖<1)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c] q)
    (k : ℕ)
    (hk : 0<k)
    (hb : ‖b‖<1)
    (hz : ‖z‖<1)
    (hbase : QDenominatorRegular [a*z] (q^k)) :
    (∑' n : ℕ, qPochhammer a (q^k) n * qPochhammer b q (k*n) * z^n /
        (qPochhammer (q^k) (q^k) n * qPochhammer c q (k*n))) =
      qPochhammerInf b q * qPochhammerInf (a*z) (q^k) /
          (qPochhammerInf c q * qPochhammerInf z (q^k)) *
          (∑' n : ℕ, qPochhammer (c/b) q n * qPochhammer z (q^k) n * b^n /
          (qPochhammer q q n * qPochhammer (a*z) (q^k) n)) := by
  have hb0 : b≠0 := hpar b (by simp)
  set Q := q^k with hQdef
  have hQ : ‖Q‖<1 := by rw [hQdef, norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hk.ne'
  let A (n : ℕ) := qPochhammer a Q n / qPochhammer Q Q n
  let B (m : ℕ) := qPochhammer (c / b) q m / qPochhammer q q m
  let K := qPochhammerInf b q / qPochhammerInf c q
  let L := qPochhammerInf (a * z) Q / qPochhammerInf z Q
  let D (n m : ℕ) := (A n * z ^ n) * (B m * b ^ m) * Q ^ (n * m)
  have hcf : ∀ j : ℕ, 1 - c * q ^ j ≠ 0 := fun j => sub_ne_zero.mpr (hden c (by simp) j).symm
  have haf : ∀ j : ℕ, 1 - (a * z) * Q ^ j ≠ 0 :=
    fun j => sub_ne_zero.mpr (hbase (a*z) (by simp) j).symm
  have hbf := one_sub_mul_pow_ne_zero_of_norm hb hq
  have hzf := one_sub_mul_pow_ne_zero_of_norm hz hQ
  have hleft (n : ℕ) : qPochhammer b q (k*n) / qPochhammer c q (k*n) =
      K * ∑' m : ℕ, B m * (b * Q ^ n) ^ m := by
    dsimp only [B]
    rw [hQdef, ← pow_mul, ← q_binomial_theorem hq (norm_mul_pow_lt_one hb hq (k*n))]
    have he : c / b * (b * q ^ (k*n)) = c * q ^ (k*n) := by field [hb0]
    rw [he]
    dsimp only [K]
    rw [qPochhammerInf_mul_qPochhammer (a := b) hq (k*n),
      qPochhammerInf_mul_qPochhammer (a := c) hq (k*n)]
    field [qPochhammer_ne_zero_of_factors hq hcf (k*n),
      qPochhammerInf_shift_ne_zero hq hbf (k*n), qPochhammerInf_shift_ne_zero hq hcf (k*n)]
  have hright (m : ℕ) : (∑' n : ℕ, A n * (z * Q ^ m) ^ n) =
      L * qPochhammer z Q m / qPochhammer (a * z) Q m := by
    dsimp only [A]
    rw [← q_binomial_theorem hQ (norm_mul_pow_lt_one hz hQ m), ← mul_assoc]
    dsimp only [L]
    rw [qPochhammerInf_mul_qPochhammer (a := a * z) hQ m,
      qPochhammerInf_mul_qPochhammer (a := z) hQ m]
    field [qPochhammer_ne_zero_of_factors hQ haf m,
      qPochhammer_ne_zero_of_factors hQ hzf m,
      qPochhammerInf_shift_ne_zero hQ hzf m]
  have hsumA : Summable (fun n : ℕ => ‖A n * z ^ n‖) :=
    (summable_q_binomial_series (a := a) hQ hz).norm
  have hsumB : Summable (fun m : ℕ => ‖B m * b ^ m‖) :=
    (summable_q_binomial_series (a := c / b) hq hb).norm
  have hs : Summable (Function.uncurry D) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun nm => ?_) (hsumA.mul_norm hsumB)
    dsimp only [Function.uncurry, D]
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg Q) hQ.le)
  have hrow (n : ℕ) : (∑' m : ℕ, D n m) =
      A n * z ^ n * ∑' m : ℕ, B m * (b * Q ^ n) ^ m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp only [D]
    rw [mul_pow, ← pow_mul Q n m]
    ring
  have hcol (m : ℕ) : (∑' n : ℕ, D n m) =
      B m * b ^ m * ∑' n : ℕ, A n * (z * Q ^ m) ^ n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [D]
    rw [mul_pow, ← pow_mul Q m n, Nat.mul_comm m n]
    ring
  have hlhs : (∑' n : ℕ, qPochhammer a Q n * qPochhammer b q (k*n) * z^n /
        (qPochhammer Q Q n * qPochhammer c q (k*n))) = K * ∑' n : ℕ, ∑' m : ℕ, D n m := by
    calc
      _ = ∑' n : ℕ, A n * z ^ n * (qPochhammer b q (k*n) / qPochhammer c q (k*n)) := by
        apply tsum_congr
        intro n
        dsimp only [A]
        ring
      _ = _ := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [hleft, hrow]
        ring
  have hrhs : (∑' n : ℕ, qPochhammer (c/b) q n * qPochhammer z Q n * b^n /
          (qPochhammer q q n * qPochhammer (a*z) Q n)) =
      ∑' m : ℕ, B m * b ^ m * qPochhammer z Q m / qPochhammer (a * z) Q m := by
    apply tsum_congr
    intro m
    dsimp only [B]
    ring
  rw [hlhs, ← hs.tsum_comm, hrhs, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [hcol, hright]
  dsimp only [K, L]
  ring

/-- DLMF 17.9.E20: mixed base general. -/
@[dlmf 17.9.E20]
theorem mixed_base_general (a b c q z : ℂ)
    (hq : ‖q‖<1) (_hq0 : q≠0)
    (hpar : ∀ x ∈ [b], x≠0)
    (hden : QDenominatorRegular [c] q)
    (k : ℕ)
    (hk : 0<k)
    (hb : ‖b‖<1)
    (hz : ‖z‖<1)
    (hbase : QDenominatorRegular [a*z] (q^k)) :
    (∑' n : ℕ, qPochhammer a (q^k) n * qPochhammer b q (k*n) * z^n /
        (qPochhammer (q^k) (q^k) n * qPochhammer c q (k*n))) =
      qPochhammerInf b q * qPochhammerInf (a*z) (q^k) /
          (qPochhammerInf c q * qPochhammerInf z (q^k)) *
          (∑' n : ℕ, qPochhammer (c/b) q n * qPochhammer z (q^k) n * b^n /
          (qPochhammer q q n * qPochhammer (a*z) (q^k) n)) :=
  mixed_base_general' a b c q z hq hpar hden k hk hb hz hbase

end DLMF.QHypergeometric
