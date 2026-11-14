/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.QHypergeometric.BilateralParity
public import DLMF.QHypergeometric.BilateralParameterContinuity
import Mathlib.Tactic
/-!
# The even bilateral summation

The product identity of DLMF 17.8.8 holds on the full bilateral annulus. Clearing both the
forward and backward denominator products makes the series analytic in its square-root
upper parameter. The identity follows first on the common Ramanujan annulus by
`BilateralParity.qPsi_even_eq_of_ramanujan_annulus`, then everywhere by analytic continuation
on a rotated half-plane and continuity in the second parameter.

* `BilateralEvenSummation.qPsi_even_eq`: the full even two-psi-two sum.

Mathlib’s identity principle and the denominator-cleared normal convergence API of
`DLMF.QHypergeometric.BilateralParameterContinuity` provide the continuation steps.
-/

public noncomputable section
open Complex Filter Set Finset
open scoped Topology Real
open DLMF.QSeries
namespace DLMF.QHypergeometric.BilateralEvenSummation
open BilateralContinuity BilateralParity

 /-- The bilateral series after clearing its forward and backward denominator products. -/
def clearedSeries (c q b : ℂ) : ℂ :=
  qPochhammerListInf [q ^ 2 / b ^ 2, c * q ^ 2 / b ^ 2] (q ^ 2) *
    (∑' k, clearedListTerm [fun b => b ^ 2, fun b => b ^ 2 / c]
      [fun _ => q, fun _ => c * q] (fun b => c * q ^ 2 / b ^ 2) (q ^ 2) b k) +
  qPochhammerListInf [q, c * q] (q ^ 2) *
    (∑' k, clearedListTerm [fun _ => q, fun _ => q / c]
      [fun b => q ^ 2 / b ^ 2, fun b => c * q ^ 2 / b ^ 2] (fun b => c / b ^ 2) (q ^ 2) b (k + 1))

 /-- The defining denominator-cleared expression. -/
lemma clearedSeries_def (c q b : ℂ) :
    clearedSeries c q b =
  qPochhammerListInf [q ^ 2 / b ^ 2, c * q ^ 2 / b ^ 2] (q ^ 2) *
    (∑' k, clearedListTerm [fun b => b ^ 2, fun b => b ^ 2 / c]
      [fun _ => q, fun _ => c * q] (fun b => c * q ^ 2 / b ^ 2) (q ^ 2) b k) +
  qPochhammerListInf [q, c * q] (q ^ 2) *
    (∑' k, clearedListTerm [fun _ => q, fun _ => q / c]
      [fun b => q ^ 2 / b ^ 2, fun b => c * q ^ 2 / b ^ 2]
        (fun b => c / b ^ 2) (q ^ 2) b (k + 1)) := by
  rfl

 /-- The corresponding denominator-cleared even product expression. -/
def clearedValue (c q r b : ℂ) : ℂ :=
  qPochhammerInf q (q ^ 2) * qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (q / b ^ 2) (q ^ 2) *
    qPochhammerInf (c * q / b ^ 2) (q ^ 2) /
    (2 * qPochhammerInf (c / b ^ 2) (q ^ 2)) *
    (qPochhammerInf (-b * r) q * qPochhammerInf (c * r / b) q +
      qPochhammerInf (b * r) q * qPochhammerInf (-c * r / b) q)

 /-- The defining denominator-cleared expression. -/
lemma clearedValue_def (c q r b : ℂ) :
    clearedValue c q r b =
  qPochhammerInf q (q ^ 2) * qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (q / b ^ 2) (q ^ 2) *
    qPochhammerInf (c * q / b ^ 2) (q ^ 2) /
    (2 * qPochhammerInf (c / b ^ 2) (q ^ 2)) *
    (qPochhammerInf (-b * r) q * qPochhammerInf (c * r / b) q +
      qPochhammerInf (b * r) q * qPochhammerInf (-c * r / b) q) := by rfl

 /-- The cleared series is analytic in the square-root upper parameter on its annulus. -/
lemma analyticAt_clearedSeries {b c q : ℂ} (hq : ‖q‖<1) (hc : c≠0)
    (hz : ‖c‖<‖b ^ 2‖) : AnalyticAt ℂ (clearedSeries c q) b := by
  have hb : b ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, norm_zero] at hz
    exact (norm_nonneg c).not_gt hz
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hw : ‖c / b ^ 2‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]
    exact hz
  have hzr : ‖c * q ^ 2 / b ^ 2‖<1 := by
    rw [show c * q ^ 2 / b ^ 2=(c / b ^ 2) * q ^ 2 by ring, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hQ.le).trans_lt hw
  have hrat : AnalyticAt ℂ (fun x : ℂ => c / x ^ 2) b :=
    analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hb)
  have hratQ : AnalyticAt ℂ (fun x : ℂ => c * q ^ 2 / x ^ 2) b :=
    analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hb)
  have ha : ∀ f∈[fun x : ℂ => x ^ 2, fun x => x ^ 2 / c], AnalyticAt ℂ f b := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl
    · exact analyticAt_id.pow 2
    · exact (analyticAt_id.pow 2).div analyticAt_const hc
  have hbp : ∀ f∈[fun _ : ℂ => q, fun _ => c * q], AnalyticAt ℂ f b := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl <;> exact analyticAt_const
  have hbn : ∀ f∈[fun x : ℂ => q ^ 2 / x ^ 2, fun x => c * q ^ 2 / x ^ 2], AnalyticAt ℂ f b := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl
    · exact analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hb)
    · exact hratQ
  have han : ∀ f∈[fun _ : ℂ => q, fun _ => q / c], AnalyticAt ℂ f b := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl <;> exact analyticAt_const
  have hp := analyticAt_tsum_clearedListTerm hQ ha hbp hratQ hzr 0
  have hn := analyticAt_tsum_clearedListTerm hQ han hbn hrat hw 1
  have hB := analyticAt_qPochhammerListInf hQ hbn
  unfold clearedSeries
  simpa [List.map_cons, List.map_nil, Pi.mul_def, Pi.add_def] using
    (hB.mul hp).add (analyticAt_const.mul hn)

 /-- The cleared product is analytic in the square-root upper parameter. -/
lemma analyticAt_clearedValue {b c q r : ℂ} (hq : ‖q‖<1) (hz : ‖c‖<‖b ^ 2‖) :
    AnalyticAt ℂ (clearedValue c q r) b := by
  have hb : b ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, norm_zero] at hz
    exact (norm_nonneg c).not_gt hz
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hw : ‖c / b ^ 2‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]
    exact hz
  have hi (Q : ℂ) (hQ : ‖Q‖<1) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f b) :
      AnalyticAt ℂ (fun x => qPochhammerInf (f x) Q) b :=
    ((qPochhammerInf_analytic hQ) _ (mem_univ _)).comp hf
  have hn := hi (q ^ 2) hQ (fun x => q / x ^ 2)
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hb))
  have hn₂ := hi (q ^ 2) hQ (fun x => c * q / x ^ 2)
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hb))
  have hd := hi (q ^ 2) hQ (fun x => c / x ^ 2)
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hb))
  have hp₁ := hi q hq (fun x => -x * r) (analyticAt_id.neg.mul analyticAt_const)
  have hp₂ := hi q hq (fun x => c * r / x) (analyticAt_const.div analyticAt_id hb)
  have hp₃ := hi q hq (fun x => x * r) (analyticAt_id.mul analyticAt_const)
  have hp₄ := hi q hq (fun x => -c * r / x) (analyticAt_const.div analyticAt_id hb)
  have hd0 : (2: ℂ) * qPochhammerInf (c / b ^ 2) (q ^ 2)≠0 :=
    mul_ne_zero (by norm_num) (qPochhammerInf_ne_zero_of_norm_lt_one hw hQ)
  unfold clearedValue
  simpa [Pi.mul_def, Pi.add_def, Pi.div_def] using
    (((((analyticAt_const (v := qPochhammerInf q (q ^ 2) *
      qPochhammerInf (q ^ 2) (q ^ 2))).mul hn).mul hn₂).div
        (analyticAt_const.mul hd) hd0).mul
      ((hp₁.mul hp₂).add (hp₃.mul hp₄)))

 /-- Clearing the two denominator blocks commutes with the bilateral sum. -/
lemma clearedSeries_eq_mul {b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hb : b≠0) (hc : c≠0)
    (hz : ‖c / b ^ 2‖<1) (hB : QBilateralRegular [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2)) :
    clearedSeries c q b = qPochhammerListInf [q, c * q] (q ^ 2) *
      qPochhammerListInf [q ^ 2 / b ^ 2, c * q ^ 2 / b ^ 2] (q ^ 2) *
        qPsi [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2) (c * q ^ 2 / b ^ 2) := by
  have hQ0 := pow_ne_zero 2 hq0
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hreg : QDenominatorRegular [q ^ 2 / b ^ 2, c * q ^ 2 / b ^ 2] (q ^ 2) := by
    have H := FiniteBilateral.qDenominatorRegular_reciprocal
      (by simp [hb, hc] : ∀ u∈[b ^ 2, b ^ 2 / c], u≠0) hB.2
    simpa only [List.map_cons, List.map_nil,
      show q ^ 2 / (b ^ 2 / c)=c * q ^ 2 / b ^ 2 by field_simp] using H
  have hz1 : ‖c * q ^ 2 / b ^ 2‖<1 := by
    rw [show c * q ^ 2 / b ^ 2=(c / b ^ 2) * q ^ 2 by ring, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hQ.le).trans_lt hz
  have hsplit := qPsi_split hQ0 hQ hB (by simp [hb, hc]) (by simp [hq0, hc])
    (div_ne_zero (mul_ne_zero hc hQ0) (pow_ne_zero 2 hb)) (by simp)
    (by simpa only [List.prod_cons, List.prod_nil, mul_one,
      show q * (c * q) / (b ^ 2 * (b ^ 2 / c) *
        (c * q ^ 2 / b ^ 2))=c / b ^ 2 by field_simp] using hz)
    (fun _ => hz1)
  have hpos (k : ℕ) : qPsiTerm [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2) (c * q ^ 2 / b ^ 2) (k: ℤ)=
      qPochhammerList [b ^ 2, b ^ 2 / c] (q ^ 2) k / qPochhammerList [q, c * q] (q ^ 2) k *
        (c * q ^ 2 / b ^ 2) ^ k := by
    simp [qPsiTerm, qPsiExponent, qPochhammerListInt_natCast]
  rw [tsum_congr hpos] at hsplit
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    show q ^ 2 / q=q by field_simp, show q ^ 2 / (c * q)=q / c by field_simp,
    show q ^ 2 / (b ^ 2 / c)=c * q ^ 2 / b ^ 2 by field_simp,
    show q * (c * q) / (b ^ 2 * (b ^ 2 / c) *
      (c * q ^ 2 / b ^ 2))=c / b ^ 2 by field_simp] at hsplit
  have hp := tsum_clearedListTerm_eq_mul
    (a := [fun b : ℂ => b ^ 2, fun b => b ^ 2 / c])
    (b := [fun _ : ℂ => q, fun _ => c * q])
    (z := fun b : ℂ => c * q ^ 2 / b ^ 2) (x := b) hQ (by simpa using hB.1) 0
  have hn := tsum_clearedListTerm_eq_mul
    (a := [fun _ : ℂ => q, fun _ => q / c])
    (b := [fun b : ℂ => q ^ 2 / b ^ 2, fun b => c * q ^ 2 / b ^ 2])
    (z := fun b : ℂ => c / b ^ 2) (x := b) hQ (by simpa using hreg) 1
  simp only [List.map_cons, List.map_nil, Nat.add_zero] at hp hn
  unfold clearedSeries
  rw [hp, hn, hsplit]
  ring

 /-- Clearing the product denominator retains every removable upper-parameter case. -/
lemma clearedValue_eq_mul {b c q r : ℂ} (hq : ‖q‖<1) (hb : b≠0)
    (hz : ‖c / b ^ 2‖<1) (hB : QBilateralRegular [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2)) :
    clearedValue c q r b = qPochhammerListInf [q, c * q] (q ^ 2) *
      qPochhammerListInf [q ^ 2 / b ^ 2, c * q ^ 2 / b ^ 2] (q ^ 2) *
      (qPochhammerListInf [q ^ 2, q / b ^ 2, c * q / b ^ 2] (q ^ 2) /
        (2 * qPochhammerListInf [c * q, c * q ^ 2 / b ^ 2, q ^ 2 / b ^ 2, c / b ^ 2] (q ^ 2)) *
        (qPochhammerInf (-b * r) q * qPochhammerInf (c * r / b) q +
         qPochhammerInf (b * r) q * qPochhammerInf (-c * r / b) q)) := by
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hqC := qPochhammerInf_ne_zero hQ
    (fun n hn => hB.1 (c * q) (by simp) n (sub_eq_zero.mp hn).symm)
  have hqb := RamanujanPsi.qPochhammerInf_q_div_ne_zero hQ (pow_ne_zero 2 hb)
    (hB.2 (b ^ 2) (by simp))
  have hqz : qPochhammerInf (c * q ^ 2 / b ^ 2) (q ^ 2)≠0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one (by
      rw [show c * q ^ 2 / b ^ 2=(c / b ^ 2) * q ^ 2 by ring, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hQ.le).trans_lt hz) hQ
  unfold clearedValue
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  generalize qPochhammerInf (c * q) (q ^ 2)=C at hqC ⊢
  generalize qPochhammerInf (c * q ^ 2 / b ^ 2) (q ^ 2)=Z at hqz ⊢
  field_simp

 /-- The cleared identity follows directly from Ramanujan summation for large upper parameters. -/
lemma clearedSeries_eq_clearedValue_of_large {b c q r : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : c≠0) (hr : r ^ 2=q) (hz : ‖c‖<‖b ^ 2‖)
    (hcreg : ∀ n : ℕ, c * q * q ^ n≠1) (hb1 : 1<‖b‖) (hbr : ‖r‖<‖b‖)
    (hbc : ‖c * q‖<‖r‖ * ‖b‖) : clearedSeries c q b=clearedValue c q r b := by
  have hb : b≠0 := norm_pos_iff.mp (lt_trans zero_lt_one hb1)
  have hbn := norm_pos_iff.mpr hb
  have hzb : ‖c / b ^ 2‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]
    exact hz
  have hbb : 1<‖b ^ 2‖ := by rw [norm_pow];nlinarith
  have hR : QBilateralRegular [b ^ 2] [c * q] q := by
    constructor
    · intro u hu n
      simp only [List.mem_singleton] at hu
      rcases hu with rfl
      exact hcreg n
    · intro u hu n hn
      simp only [List.mem_singleton] at hu
      rcases hu with rfl
      have hp : ‖q ^ (n + 1)‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
      rw [← hn] at hp
      exact (not_lt_of_ge hbb.le) hp
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hB : QBilateralRegular [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2) := by
    constructor
    · intro u hu n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl|rfl
      · intro hn
        exact (one_sub_mul_pow_ne_zero_of_norm hq hQ n) (by rw [hn];ring)
      · have H := hcreg (2 * n)
        rwa [pow_mul] at H
    · intro u hu n hn
      have hu1 : 1<‖u‖ := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl|rfl
        · exact hbb
        · rw [norm_div, one_lt_div (norm_pos_iff.mpr hc)]
          exact hz
      rw [hn, norm_pow] at hu1
      have H := pow_lt_one₀ (norm_nonneg (q ^ 2)) hQ (by omega : n + 1≠0)
      linarith
  have ht : ‖r / b‖<1 := by rw [norm_div, div_lt_one hbn];exact hbr
  have hct : ‖c * q / b ^ 2‖<‖r / b‖ := by
    rw [norm_div, norm_pow, norm_div, div_lt_div_iff₀ (sq_pos_of_pos hbn) hbn]
    nlinarith [mul_lt_mul_of_pos_right hbc hbn]
  rw [clearedSeries_eq_mul hq0 hq hb hc hzb hB, clearedValue_eq_mul hq hb hzb hB,
    qPsi_even_eq_of_ramanujan_annulus hq0 hq hb hc hr hzb hB hR ht hct]

 /-- Continuation in the square-root upper parameter removes its auxiliary annular restrictions. -/
lemma clearedSeries_eq_clearedValue_of_regular {b c q r : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : c≠0) (hr : r ^ 2=q) (hz : ‖c‖<‖b ^ 2‖)
    (hcreg : ∀ n : ℕ, c * q * q ^ n≠1) : clearedSeries c q b=clearedValue c q r b := by
  have hb : b ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, norm_zero] at hz
    exact (norm_nonneg c).not_gt hz
  have hbn := norm_pos_iff.mpr hb
  have hr0 : r≠0 := by intro h;rw [h, zero_pow two_ne_zero] at hr;exact hq0 hr.symm
  have hrn := norm_pos_iff.mpr hr0
  let s := Real.sqrt ‖c‖ / ‖b‖
  let V : Set ℂ := (fun w : ℂ => w * b) '' {w | s<w.re}
  have hVo : IsOpen V :=
    (Homeomorph.mulRight₀ b hb).isOpenMap _ (isOpen_lt continuous_const continuous_re)
  have hVc : IsPreconnected V := (convex_halfSpace_re_gt s).isPreconnected.image _
    (continuous_id.mul continuous_const).continuousOn
  have hVU {z : ℂ} (hzV : z∈V) : ‖c‖<‖z ^ 2‖ := by
    rcases hzV with ⟨w, hw, rfl⟩
    have hrad : Real.sqrt ‖c‖<‖w‖ * ‖b‖ := by
      calc Real.sqrt ‖c‖ = s * ‖b‖ := by dsimp [s];field_simp
        _ < w.re * ‖b‖ := mul_lt_mul_of_pos_right hw hbn
        _ ≤ ‖w‖ * ‖b‖ := mul_le_mul_of_nonneg_right (re_le_norm w) hbn.le
    rw [norm_pow, norm_mul]
    exact (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) hrad)).mp hrad
  have hbV : b∈V := by
    refine ⟨1, ?_, one_mul b⟩
    dsimp [s]
    rw [div_lt_one hbn]
    exact (Real.sqrt_lt' hbn).mpr (by rwa [← norm_pow])
  let M := 1 + ‖b‖ + Real.sqrt ‖c‖ + ‖r‖ + ‖c * q‖ / ‖r‖
  have hN := div_nonneg (norm_nonneg (c * q)) hrn.le
  have hS := Real.sqrt_nonneg ‖c‖
  have hM1 : 1<M := by dsimp [M];linarith
  have hMr : ‖r‖<M := by dsimp [M];linarith
  have hMc : Real.sqrt ‖c‖<M := by dsimp [M];linarith
  have hMcr : ‖c * q‖<‖r‖ * M := by
    have H : ‖c * q‖ / ‖r‖<M := by dsimp [M];linarith
    simpa only [mul_comm] using (div_lt_iff₀ hrn).mp H
  have hM0 := lt_trans zero_lt_one hM1
  let z₀ : ℂ := ((M / ‖b‖: ℝ): ℂ) * b
  have hz₀n : ‖z₀‖=M := by
    dsimp [z₀]
    rw [norm_mul, norm_real, Real.norm_of_nonneg (div_nonneg hM0.le hbn.le)]
    field_simp
  have hz₀V : z₀∈V := by
    refine ⟨((M / ‖b‖: ℝ): ℂ), ?_, rfl⟩
    dsimp [s]
    rw [div_lt_div_iff_of_pos_right hbn]
    exact hMc
  have hF : AnalyticOnNhd ℂ (clearedSeries c q) V := fun z hzV =>
    analyticAt_clearedSeries hq hc (hVU hzV)
  have hG : AnalyticOnNhd ℂ (clearedValue c q r) V := fun z hzV =>
    analyticAt_clearedValue hq (hVU hzV)
  have heq : (clearedSeries c q)=ᶠ[𝓝 z₀](clearedValue c q r) := by
    have h₁ : ∀ᶠ z : ℂ in 𝓝 z₀, 1<‖z‖ :=
      continuous_norm.continuousAt.eventually (Ioi_mem_nhds (by dsimp only;rw [hz₀n];exact hM1))
    have h₂ : ∀ᶠ z : ℂ in 𝓝 z₀, ‖r‖<‖z‖ :=
      continuous_norm.continuousAt.eventually (Ioi_mem_nhds (by dsimp only;rw [hz₀n];exact hMr))
    have h₃ : ∀ᶠ z : ℂ in 𝓝 z₀, ‖c * q‖<‖r‖ * ‖z‖ :=
      (continuous_const.mul continuous_norm).continuousAt.eventually
        (Ioi_mem_nhds (by simp only [Pi.mul_apply];rw [hz₀n];exact hMcr))
    filter_upwards [h₁, h₂, h₃, hVo.mem_nhds hz₀V] with z hz₁ hz₂ hz₃ hzV
    exact clearedSeries_eq_clearedValue_of_large hq0 hq hc hr (hVU hzV) hcreg hz₁ hz₂ hz₃
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hVc hz₀V heq hbV

 /-- The cleared series depends continuously on its second upper parameter. -/
lemma continuousAt_clearedSeries_right {b c q : ℂ} (hq : ‖q‖<1) (hb : b≠0) (hc : c≠0)
    (hz : ‖c‖<‖b ^ 2‖) : ContinuousAt (fun t => clearedSeries t q b) c := by
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hw : ‖c / b ^ 2‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]
    exact hz
  have hzr : ‖c * q ^ 2 / b ^ 2‖<1 := by
    rw [show c * q ^ 2 / b ^ 2=(c / b ^ 2) * q ^ 2 by ring, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hQ.le).trans_lt hw
  have ha : ∀ f∈[fun _ : ℂ => b ^ 2, fun t => b ^ 2 / t], ContinuousAt f c := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl
    · exact continuousAt_const
    · exact continuousAt_const.div₀ continuousAt_id hc
  have hbp : ∀ f∈[fun _ : ℂ => q, fun t => t * q], ContinuousAt f c := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl
    · exact continuousAt_const
    · exact continuousAt_id.mul_const _
  have hbn : ∀ f∈[fun _ : ℂ => q ^ 2 / b ^ 2, fun t => t * q ^ 2 / b ^ 2], ContinuousAt f c := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl
    · exact continuousAt_const
    · fun_prop
  have han : ∀ f∈[fun _ : ℂ => q, fun t => q / t], ContinuousAt f c := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl
    · exact continuousAt_const
    · exact continuousAt_const.div₀ continuousAt_id hc
  have hp := continuousAt_tsum_clearedListTerm (z := fun t : ℂ => t * q ^ 2 / b ^ 2)
    (x := c) hQ ha hbp (by fun_prop) hzr 0
  have hn := continuousAt_tsum_clearedListTerm (z := fun t : ℂ => t / b ^ 2)
    (x := c) hQ han hbn (by fun_prop) hw 1
  have hB := continuousAt_qPochhammerListInf hQ hbn
  have hC := continuousAt_qPochhammerListInf hQ hbp
  simpa [clearedSeries, clearedListTerm_def, List.map_cons, List.map_nil, Pi.mul_def,
    Pi.add_def] using (hB.mul hp).add (hC.mul hn)

 /-- The cleared even product depends continuously on its second upper parameter. -/
lemma continuousAt_clearedValue_right {b c q r : ℂ} (hq : ‖q‖<1) (hb : b≠0)
    (hz : ‖c‖<‖b ^ 2‖) : ContinuousAt (fun t => clearedValue t q r b) c := by
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hw : ‖c / b ^ 2‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))]
    exact hz
  have hi (Q : ℂ) (hQ : ‖Q‖<1) (f : ℂ → ℂ) (hf : ContinuousAt f c) :
      ContinuousAt (fun t => qPochhammerInf (f t) Q) c :=
    ((differentiable_qPochhammerInf_left hQ).continuous.continuousAt).comp hf
  have hn := hi (q ^ 2) hQ (fun t => t * q / b ^ 2) (by fun_prop)
  have hd := hi (q ^ 2) hQ (fun t => t / b ^ 2) (by fun_prop)
  have hp := hi q hq (fun t => t * r / b) (by fun_prop)
  have hm := hi q hq (fun t => -t * r / b) (by fun_prop)
  have hd0 : (2: ℂ) * qPochhammerInf (c / b ^ 2) (q ^ 2)≠0 :=
    mul_ne_zero (by norm_num) (qPochhammerInf_ne_zero_of_norm_lt_one hw hQ)
  simpa only [clearedValue, Pi.mul_def, Pi.add_def, Pi.div_def] using
    ((continuousAt_const.mul hn).div₀ (continuousAt_const.mul hd) hd0).mul
      ((continuousAt_const.mul hp).add (continuousAt_const.mul hm))

 /-- The cleared identity holds throughout the full bilateral convergence annulus. -/
lemma clearedSeries_eq_clearedValue {b c q r : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : c≠0) (hr : r ^ 2=q) (hz : ‖c‖<‖b ^ 2‖) :
    clearedSeries c q b=clearedValue c q r b := by
  have hb : b ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, norm_zero] at hz
    exact (norm_nonneg c).not_gt hz
  have hF := continuousAt_clearedSeries_right hq hb hc hz
  have hG := continuousAt_clearedValue_right (r := r) hq hb hz
  have heq : (fun t => clearedSeries t q b)=ᶠ[𝓝[≠] c](fun t => clearedValue t q r b) := by
    have hreg := BilateralContinuity.eventually_regular_mul q q c hq
    have hnorm : ∀ᶠ t : ℂ in 𝓝 c, ‖t‖<‖b ^ 2‖ := continuous_norm.continuousAt.eventually_lt_const hz
    have hne : ∀ᶠ t : ℂ in 𝓝 c, t≠0 := continuousAt_id.eventually_ne hc
    filter_upwards [hreg, nhdsWithin_le_nhds hnorm, nhdsWithin_le_nhds hne] with t ht htn hte
    exact clearedSeries_eq_clearedValue_of_regular hq0 hq hte hr htn
      (by simpa only [mul_comm q t] using ht)
  exact tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
    ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)

 /-- The even two-psi-two summation on its full bilateral annulus, with every upper exception. -/
lemma qPsi_even_eq {b c q r : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hb : b≠0) (hc : c≠0)
    (hr : r ^ 2=q) (hz : ‖c / b ^ 2‖<1)
    (hB : QBilateralRegular [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2)) :
    qPsi [b ^ 2, b ^ 2 / c] [q, c * q] (q ^ 2) (c * q ^ 2 / b ^ 2) =
      qPochhammerListInf [q ^ 2, q / b ^ 2, c * q / b ^ 2] (q ^ 2) /
        (2 * qPochhammerListInf [c * q, c * q ^ 2 / b ^ 2, q ^ 2 / b ^ 2, c / b ^ 2] (q ^ 2)) *
        (qPochhammerInf (-b * r) q * qPochhammerInf (c * r / b) q +
         qPochhammerInf (b * r) q * qPochhammerInf (-c * r / b) q) := by
  have hzn : ‖c‖<‖b ^ 2‖ := by
    rwa [norm_div, div_lt_one (norm_pos_iff.mpr (pow_ne_zero 2 hb))] at hz
  have H := clearedSeries_eq_clearedValue (r := r) hq0 hq hc hr hzn
  rw [clearedSeries_eq_mul hq0 hq hb hc hz hB, clearedValue_eq_mul hq hb hz hB] at H
  have hQ : ‖q ^ 2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hP := FiniteBilateral.qPochhammerListInf_ne_zero hQ hB.1
  have hreg : QDenominatorRegular [q ^ 2 / b ^ 2, c * q ^ 2 / b ^ 2] (q ^ 2) := by
    have H := FiniteBilateral.qDenominatorRegular_reciprocal
      (by simp [hb, hc] : ∀ u∈[b ^ 2, b ^ 2 / c], u≠0) hB.2
    simpa only [List.map_cons, List.map_nil,
      show q ^ 2 / (b ^ 2 / c)=c * q ^ 2 / b ^ 2 by field_simp] using H
  exact mul_left_cancel₀ (mul_ne_zero hP (FiniteBilateral.qPochhammerListInf_ne_zero hQ hreg)) H

end DLMF.QHypergeometric.BilateralEvenSummation
