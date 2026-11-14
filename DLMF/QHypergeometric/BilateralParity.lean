/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.QHypergeometric.Convergence
import DLMF.QHypergeometric.BasicSummations.Heine
import DLMF.QHypergeometric.Ramanujan
import DLMF.QHypergeometric.BilateralFirstTransformation
import DLMF.QHypergeometric.BilateralParameterContinuity
import Mathlib.Tactic
/-!
# Even parts of bilateral basic hypergeometric series

Pairing adjacent upper and lower parameters expresses an even base-q bilateral series
as a base-q² two-psi-two series. Bailey’s transformation then gives the even summation
of DLMF 17.8.8 on the common annulus of the two Ramanujan one-psi-one series.

The proof reuses `BilateralFirstTransformation.transformation_one` and
`ramanujan_one_psi_one`; the even/odd decomposition is a summable reindexing by
`Fin 2 × ℤ`.
-/

public noncomputable section
open Complex
open DLMF.QSeries
namespace DLMF.QHypergeometric.BilateralParity
 /-- Splitting even and odd factors of an integer - index q - shifted factorial. -/
lemma qPochhammerInt_double (a q : ℂ) (n : ℤ) :
    qPochhammerInt a q (2 * n) =
      qPochhammerInt a (q ^ 2) n * qPochhammerInt (a * q) (q ^ 2) n := by
  cases n with
  | ofNat k =>
    rw [show Int.ofNat k=(k: ℤ) from rfl,
      show (2: ℤ) * (k: ℤ)=((2 * k: ℕ): ℤ) by push_cast;ring]
    simp only [qPochhammerInt_natCast]
    simpa [qPochhammerList] using qPochhammer_even a q k
  | negSucc k =>
    rw [show (2: ℤ) * Int.negSucc k=Int.negSucc (2 * k + 1) by omega]
    simp only [qPochhammerInt_negSucc]
    rw [show 2 * k + 1 + 1=2 * (k + 1) by omega]
    have he : (q ^ 2) ^ (-((k + 1: ℕ): ℤ))=q ^ (-((2 * (k + 1): ℕ): ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at he ⊢
    rw [he]
    have H := qPochhammer_even (a * q ^ (-((2 * (k + 1): ℕ): ℤ))) q (k + 1)
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at H
    have Hinv := congrArg Inv.inv H
    simp only [mul_inv] at Hinv
    have h₁ : -((2: ℤ) * k + 1 + 1)= -((2 * (k + 1): ℕ): ℤ) := by push_cast;ring
    have h₂ : -((2: ℤ) * ((k: ℤ) + 1))= -((2 * (k + 1): ℕ): ℤ) := by push_cast;ring
    norm_num only [Nat.cast_ofNat] at *
    rw [h₁, h₂]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using Hinv

 /-- The even part of a summable one-psi-one series. -/
lemma qPsi_even {a b q t : ℂ} (hf : Summable (fun k : ℤ => qPsiTerm [a] [b] q t k))
    (hg : Summable (fun k : ℤ => qPsiTerm [a] [b] q (-t) k)) :
    (qPsi [a] [b] q t + qPsi [a] [b] q (-t)) / 2 =
      ∑' n : ℤ, qPsiTerm [a] [b] q t (2 * n) := by
  let E : Fin 2 × ℤ ≃ ℤ :=
    {toFun := fun p => 2 * p.2 + (p.1.val: ℤ)
     invFun := fun n => (⟨(n%2).toNat, by omega⟩, n / 2)
     left_inv := by
       rintro ⟨i, n⟩
       apply Prod.ext
       · apply Fin.ext
         dsimp
         have hi := i.isLt
         omega
       · dsimp
         have hi := i.isLt
         omega
     right_inv := by intro n;dsimp;omega}
  have hs (f : ℤ → ℂ) (h : Summable f) :
      ∑' k, f k = (∑' n, f (2 * n)) + (∑' n, f (2 * n + 1)) := by
    have hcomp : Summable (fun p : Fin 2 × ℤ => f (E p)) := h.comp_injective E.injective
    rw [← E.tsum_eq f, hcomp.tsum_prod, tsum_fintype, Fin.sum_univ_two]
    simp [E]
  have hp (n : ℤ) : qPsiTerm [a] [b] q (-t) (2 * n)=qPsiTerm [a] [b] q t (2 * n) := by
    have hev : Even (2 * n) := ⟨n, by ring⟩
    simp only [qPsiTerm, hev.neg_zpow t]
  have hn (n : ℤ) : qPsiTerm [a] [b] q (-t) (2 * n + 1)= -qPsiTerm [a] [b] q t (2 * n + 1) := by
    have ho : Odd (2 * n + 1) := ⟨n, rfl⟩
    simp only [qPsiTerm, ho.neg_zpow t]
    ring
  rw [qPsi, qPsi, hs _ hf, hs _ hg, tsum_congr hp, tsum_congr hn, tsum_neg]
  ring
 /-- Pairing adjacent parameters gives the even part of the base-q series. -/
lemma qPsi_paired_eq_even_part {a b q t : ℂ} (hf : Summable (fun k : ℤ => qPsiTerm [a] [b] q t k))
    (hg : Summable (fun k : ℤ => qPsiTerm [a] [b] q (-t) k)) :
    qPsi [a, a * q] [b, b * q] (q ^ 2) (t ^ 2) = (qPsi [a] [b] q t + qPsi [a] [b] q (-t)) / 2 := by
  rw [qPsi_even hf hg, qPsi]
  apply tsum_congr
  intro n
  simp only [qPsiTerm, qPsiExponent, List.length_cons, List.length_nil]
  norm_num only [zpow_zero, mul_one]
  simp only [qPochhammerListInt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [← qPochhammerInt_double a q n, ← qPochhammerInt_double b q n,
    ← zpow_natCast, ← zpow_mul]
  norm_num only [Nat.cast_ofNat]

 /-- The even bilateral sum on the annulus of the two Ramanujan series. -/
lemma qPsi_even_eq_of_ramanujan_annulus {b c q r : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hb : b≠0) (hc : c≠0)
    (hr : r ^ 2=q) (hz : ‖c / b ^ 2‖<1)
    (hB : QBilateralRegular [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2))
    (hR : QBilateralRegular [b ^ 2] [c * q] q)
    (ht : ‖r / b‖<1) (hct : ‖c * q / b ^ 2‖<‖r / b‖) :
    qPsi [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2) (c * q ^ 2 / b ^ 2) =
      qPochhammerListInf [q ^ 2, q / b ^ 2, c * q / b ^ 2] (q ^ 2) /
        (2 * qPochhammerListInf [c * q, c * q ^ 2 / b ^ 2, q ^ 2 / b ^ 2, c / b ^ 2] (q ^ 2)) *
        (qPochhammerInf (-b * r) q * qPochhammerInf (c * r / b) q +
         qPochhammerInf (b * r) q * qPochhammerInf (-c * r / b) q) := by
  have hr0 : r≠0 := by intro h0;rw [h0, zero_pow two_ne_zero] at hr;exact hq0 hr.symm
  have hQ0 := pow_ne_zero 2 hq0
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have ht2 : (r / b) ^ 2=q / b ^ 2 := by rw [div_pow, hr]
  have ht0 := div_ne_zero hr0 hb
  have hden : QDenominatorRegular
      [c * q ^ 2 / b ^ 2, q, q ^ 2 / (b ^ 2 / c),
        (c * q) * q / (b ^ 2 * (b ^ 2 / c) * (c * q ^ 2 / b ^ 2))] (q ^ 2) := by
    have hzq : ‖c * q ^ 2 / b ^ 2‖<1 := by
      rw [show c * q ^ 2 / b ^ 2=(c / b ^ 2) * q ^ 2 by ring, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hQ.le).trans_lt hz
    have hw : (c * q) * q / (b ^ 2 * (b ^ 2 / c) * (c * q ^ 2 / b ^ 2))=c / b ^ 2 := by field_simp
    have he : q ^ 2 / (b ^ 2 / c)=c * q ^ 2 / b ^ 2 := by field_simp
    rw [he, hw]
    intro u hu n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl
    · exact one_sub_mul_pow_ne_zero_of_norm hzq hQ n ∘ (fun h => by rw [h];ring)
    · exact one_sub_mul_pow_ne_zero_of_norm hq hQ n ∘ (fun h => by rw [h];ring)
    · exact one_sub_mul_pow_ne_zero_of_norm hzq hQ n ∘ (fun h => by rw [h];ring)
    · exact one_sub_mul_pow_ne_zero_of_norm hz hQ n ∘ (fun h => by rw [h];ring)
  have hnew : QBilateralRegular [b ^ 2, b ^ 2 * q] [c * q ^ 2, c * q] (q ^ 2) := by
    constructor
    · intro u hu n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl|rfl
      · have H := hR.1 (c * q) (by simp) (2 * n + 1)
        rw [pow_succ, pow_mul] at H
        convert H using 1; ring
      · have H := hR.1 (c * q) (by simp) (2 * n)
        rw [pow_mul] at H
        exact H
    · intro u hu n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl|rfl
      · apply hR.2 (b ^ 2) (by simp) (2 * n + 1)
        rw [hn, ← pow_mul]
        congr 1
      · apply hR.2 (b ^ 2) (by simp) (2 * n)
        apply (mul_right_cancel₀ hq0)
        calc b ^ 2 * q=(q ^ 2) ^ (n + 1) := hn
          _=q ^ (2 * n + 1) * q := by
            rw [← pow_mul, ← pow_succ]
            congr 1
  have hBswap : QBilateralRegular [b ^ 2, b ^ 2 / c] [c * q, q] (q ^ 2) :=
    ⟨fun u hu => hB.1 u (by simpa [List.mem_cons, or_comm, or_left_comm, or_assoc] using hu), hB.2⟩
  have hArg : b ^ 2 * (b ^ 2 / c) * (c * q ^ 2 / b ^ 2) / q=b ^ 2 * q := by field_simp
  have hAz : b ^ 2 * (c * q ^ 2 / b ^ 2)=c * q ^ 2 := by field_simp
  have hprod : (c * q) * q / (b ^ 2 * (b ^ 2 / c))=(c * q / b ^ 2) ^ 2 := by field_simp
  have hArgOrig : ‖(c * q) * q / (b ^ 2 * (b ^ 2 / c))‖<‖c * q ^ 2 / b ^ 2‖ := by
    rw [show (c * q) * q / (b ^ 2 * (b ^ 2 / c))=(c / b ^ 2) * (c * q ^ 2 / b ^ 2) by field_simp,
      norm_mul]
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr
      (div_ne_zero (mul_ne_zero hc hQ0) (pow_ne_zero 2 hb))) hz
  have hArg1 : ‖c * q ^ 2 / b ^ 2‖<1 := by
    rw [show c * q ^ 2 / b ^ 2=(c / b ^ 2) * q ^ 2 by ring, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hQ.le).trans_lt hz
  have hnewarg : ‖(c * q) * q / (b ^ 2 * (b ^ 2 / c))‖<‖q / b ^ 2‖ ∧ ‖q / b ^ 2‖<1 := by
    rw [hprod, ← ht2, norm_pow, norm_pow]
    constructor
    · nlinarith [norm_nonneg (c * q / b ^ 2), norm_nonneg (r / b)]
    · exact pow_lt_one₀ (norm_nonneg _) ht two_ne_zero
  have H := BilateralFirstTransformation.transformation_one (b ^ 2) (b ^ 2 / c)
    (c * q) q (q ^ 2) (c * q ^ 2 / b ^ 2)
    hQ hQ0 (by simp [hb, hc, hq0]) hden
    ⟨hBswap, by simpa only [hArg, hAz] using hnew⟩ ⟨hArgOrig, hArg1⟩ hnewarg
  rw [FiniteBilateral.qPsi_perm (List.Perm.refl _)
    (List.Perm.swap q (c * q) [])] at H
  rw [hArg, hAz] at H
  have hsum (t : ℂ) (ht0 : t≠0) (ht1 : ‖t‖<1) (hct1 : ‖c * q / b ^ 2‖<‖t‖) :
      Summable (fun k : ℤ => qPsiTerm [b ^ 2] [c * q] q t k) := by
    have hi : ‖(c * q) / (b ^ 2 * t)‖<1 := by
      rw [← div_div, norm_div, div_lt_one (norm_pos_iff.mpr ht0)]
      exact hct1
    exact (qPsi_hasSum hq0 hq hR (by simp [hb]) ht0 (by simp)
      (by simpa only [List.prod_cons, List.prod_nil, mul_one] using hi) (fun _ => ht1)).summable
  have hp := hsum (r / b) ht0 ht hct
  have hm := hsum (-(r / b)) (neg_ne_zero.mpr ht0) (by rwa [norm_neg]) (by rwa [norm_neg])
  have hpair := qPsi_paired_eq_even_part hp hm
  rw [show c * q * q=c * q ^ 2 by ring,
    FiniteBilateral.qPsi_perm (List.Perm.refl _) (List.Perm.swap (c * q ^ 2) (c * q) [])] at hpair
  rw [← ht2, hpair] at H
  have hRp := ramanujan_one_psi_one hq0 hq (pow_ne_zero 2 hb) hR ⟨hct, ht⟩
  have hRm := ramanujan_one_psi_one (z := -(r / b)) hq0 hq (pow_ne_zero 2 hb) hR
    ⟨by simpa only [norm_neg] using hct, by simpa only [norm_neg] using ht⟩
  rw [hRp, hRm] at H
  have hval (v : ℂ) (hv : v ^ 2=q) (hv0 : v≠0) (hvt : ‖v / b‖<1) :
      qRamanujanValue (b ^ 2) (c * q) q (v / b) =
        (qPochhammerInf q q * qPochhammerInf (c * q / b ^ 2) q /
          (qPochhammerInf (c * q) q * qPochhammerInf (q / b ^ 2) q)) *
          qPochhammerInf (b * v) q / qPochhammerInf (c * v / b) q := by
    have h₁ : b ^ 2 * (v / b)=b * v := by field_simp
    have h₂ : q / (b * v)=v / b := by rw [← hv];field_simp
    have h₃ : c * q / (b * v)=c * v / b := by rw [← hv];field_simp
    have hT := qPochhammerInf_ne_zero_of_norm_lt_one hvt hq
    have hAlg (A B C D E F T : ℂ) (hT : T≠0) :
        A * (B * (C * T)) / (D * (E * (T * F)))=(A * B / (D * E)) * C / F := by
      field_simp
    simp only [qRamanujanValue, h₁, h₂, h₃, qPochhammerListInf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    exact hAlg _ _ _ _ _ _ _ hT
  rw [← neg_div] at H
  rw [hval r hr hr0 ht, hval (-r) (by simpa only [neg_sq] using hr)
    (neg_ne_zero.mpr hr0) (by simpa only [neg_div, norm_neg] using ht)] at H
  rw [ht2, show c * q / (b ^ 2 / c)=c ^ 2 * q / b ^ 2 by field_simp,
    show q * q ^ 2 / (b ^ 2 * (b ^ 2 / c) * (c * q ^ 2 / b ^ 2))=q / b ^ 2 by field_simp,
    show q ^ 2 / (b ^ 2 / c)=c * q ^ 2 / b ^ 2 by field_simp,
    show c * q * q / (b ^ 2 * (b ^ 2 / c) * (c * q ^ 2 / b ^ 2))=c / b ^ 2 by field_simp] at H
  have hX : ‖c * r / b‖<1 := by
    have he : c * r / b=(c * q / b ^ 2) / (r / b) := by rw [← hr];field_simp
    rw [he, norm_div, div_lt_one (norm_pos_iff.mpr ht0)]
    exact hct
  have hXP := qPochhammerInf_ne_zero_of_norm_lt_one hX hq
  have hXN := qPochhammerInf_ne_zero_of_norm_lt_one
    (by simpa only [mul_neg, neg_div, norm_neg] using hX : ‖c * (-r) / b‖<1) hq
  have hpairX : qPochhammerInf (c * r / b) q * qPochhammerInf (c * (-r) / b) q =
      qPochhammerInf (c ^ 2 * q / b ^ 2) (q ^ 2) := by
    rw [show c * (-r) / b= -(c * r / b) by ring, qPochhammerInf_mul_qPochhammerInf_neg hq]
    congr 1
    rw [div_pow, mul_pow, hr]
  rw [show b * (-r)= -b * r by ring, show c * (-r) / b= -(c * r / b) by ring] at H
  have hQq := qPochhammerInf_ne_zero_of_norm_lt_one hq hQ
  have hQz : qPochhammerInf (c * q ^ 2 / b ^ 2) (q ^ 2)≠0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one hArg1 hQ
  have hQw := qPochhammerInf_ne_zero_of_norm_lt_one hz hQ
  have hQb : qPochhammerInf (q ^ 2 / b ^ 2) (q ^ 2)≠0 :=
    RamanujanPsi.qPochhammerInf_q_div_ne_zero hQ (pow_ne_zero 2 hb) (hB.2 (b ^ 2) (by simp))
  have hQcq : qPochhammerInf (c * q) (q ^ 2)≠0 :=
    qPochhammerInf_ne_zero hQ (fun n hn => hB.1 (c * q) (by simp) n (sub_eq_zero.mp hn).symm)
  have hQcq2 : qPochhammerInf (c * q ^ 2) (q ^ 2)≠0 :=
    qPochhammerInf_ne_zero hQ (fun n hn => hnew.1 (c * q ^ 2) (by simp) n (sub_eq_zero.mp hn).symm)
  have htq : ‖q / b ^ 2‖ < 1 := by
    rw [← ht2, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) ht two_ne_zero
  have hqb := qPochhammerInf_ne_zero_of_norm_lt_one htq hQ
  have hAlg (P K X XN Y YN : ℂ) (hX : X≠0) (hXN : XN≠0) :
      P * ((K * Y / X + K * YN / XN) / 2)=P * K * (YN * X + Y * XN) /
        (2 * (X * XN)) := by field_simp;ring
  rw [H]
  rw [hAlg _ _ _ _ _ _ hXP (by simpa only [mul_neg, neg_div] using hXN)]
  rw [← show c * (-r) / b= -(c * r / b) by ring, hpairX]
  rw [qPochhammerInf_split_sq (a := q) hq,
    qPochhammerInf_split_sq (a := c * q / b ^ 2) hq,
    qPochhammerInf_split_sq (a := c * q) hq,
    qPochhammerInf_split_sq (a := q / b ^ 2) hq]
  simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil,
    mul_one]
  rw [show q * q=q ^ 2 by ring, show c * q / b ^ 2 * q=c * q ^ 2 / b ^ 2 by ring,
    show c * q * q=c * q ^ 2 by ring, show q / b ^ 2 * q=q ^ 2 / b ^ 2 by ring]
  generalize qPochhammerInf (c ^ 2 * q / b ^ 2) (q ^ 2)=PX at hpairX ⊢
  have hPX : PX≠0 := by rw [← hpairX];exact mul_ne_zero hXP hXN
  field_simp

end DLMF.QHypergeometric.BilateralParity
