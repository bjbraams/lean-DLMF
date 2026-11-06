/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BilateralContinuity
public import DLMFMathlib.Analysis.Normed.Group.TanneryRatio

/-!
# Bilateral continuity at a zero lower parameter

A two-psi-two remains continuous when a lower parameter tends to zero. Its negative
successive-term ratio tends jointly to zero as the parameter tends to zero and the
index tends to infinity, giving a uniform geometric majorant by Tannery's theorem.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralZeroLowerContinuity

/-- Negative terms of a two-psi-two are quotients of ordinary shifted products, including
zero lower parameters. -/
lemma qPsiTerm_neg_natCast_eq (a b c d q z : ℂ) (k : ℕ) :
    qPsiTerm [a, b] [c, d] q z (-(k : ℤ)) =
      qPochhammer (c / q ^ k) q k * qPochhammer (d / q ^ k) q k /
        (qPochhammer (a / q ^ k) q k * qPochhammer (b / q ^ k) q k) * z ^ (-(k : ℤ)) := by
  simp only [qPsiTerm, qPsiExponent, List.length_cons, List.length_nil]
  norm_num only
  simp only [zpow_zero, mul_one, FiniteBilateral.qPochhammerListInt_neg_natCast,
    qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    zpow_neg, zpow_natCast, div_eq_mul_inv, inv_inv, mul_inv_rev]
  ring

/-- Consecutive negative terms have a rational ratio whose numerator is polynomial in the
lower parameters; no lower parameter is required to be nonzero. -/
lemma qPsiTerm_neg_succ {a b c d q z : ℂ} (hq0 : q ≠ 0) (hz0 : z ≠ 0)
    (hA : ∀ u ∈ [a, b], ∀ j : ℕ, u ≠ q ^ (j + 1)) (k : ℕ) :
    qPsiTerm [a, b] [c, d] q z (-((k + 1 : ℕ) : ℤ)) =
      ((q ^ (k + 1) - c) * (q ^ (k + 1) - d) /
        ((q ^ (k + 1) - a) * (q ^ (k + 1) - b) * z)) *
          qPsiTerm [a, b] [c, d] q z (-(k : ℤ)) := by
  have hqk := pow_ne_zero k hq0
  have hqk1 := pow_ne_zero (k + 1) hq0
  have hAk := FiniteBilateral.qPochhammer_div_pow_ne_zero hq0 (hA a (by simp)) k
  have hBk := FiniteBilateral.qPochhammer_div_pow_ne_zero hq0 (hA b (by simp)) k
  have hA1 : q ^ (k + 1) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hA a (by simp) k))
  have hB1 : q ^ (k + 1) - b ≠ 0 := sub_ne_zero.mpr (Ne.symm (hA b (by simp) k))
  have harg (u : ℂ) : u / q ^ (k + 1) * q = u / q ^ k := by rw [pow_succ]; field_simp
  have hstep (u : ℂ) : qPochhammer (u / q ^ (k + 1)) q (k + 1) =
      (1 - u / q ^ (k + 1)) * qPochhammer (u / q ^ k) q k := by
    rw [qPochhammer_succ', harg]
  have hzstep : z ^ (-((k + 1 : ℕ) : ℤ)) = z ^ (-(k : ℤ)) / z := by
    rw [show -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 by omega, zpow_sub_one₀ hz0]
    rfl
  rw [qPsiTerm_neg_natCast_eq, qPsiTerm_neg_natCast_eq, hstep, hstep, hstep, hstep, hzstep]
  generalize qPochhammer (a / q ^ k) q k = A at hAk ⊢
  generalize qPochhammer (b / q ^ k) q k = B at hBk ⊢
  generalize qPochhammer (c / q ^ k) q k = C
  generalize qPochhammer (d / q ^ k) q k = D
  field_simp

/-- The negative-index two-psi-two half is continuous as a lower parameter tends to zero.
-/
lemma continuousAt_tsum_negative {a b d q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hz0 : z ≠ 0)
    (hD : ∀ j : ℕ, d * q ^ j ≠ 1)
    (hA : ∀ u ∈ [a, b], ∀ j : ℕ, u ≠ q ^ (j + 1)) :
    ContinuousAt (fun c : ℂ => ∑' k : ℕ, qPsiTerm [a, b] [c, d] q z (-(k : ℤ))) 0 := by
  have hB : QBilateralRegular [a, b] [0, d] q := by
    refine ⟨?_, hA⟩
    intro u hu j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · simp
    · exact hD j
  have hterm (k : ℕ) : ContinuousAt
      (fun c : ℂ => qPsiTerm [a, b] [c, d] q z (-(k : ℤ))) 0 := by
    have hU : ∀ g ∈ [(fun _ : ℂ => a), (fun _ : ℂ => b)], ContinuousAt g 0 := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> exact continuousAt_const
    have hL : ∀ g ∈ [(fun u : ℂ => u), (fun _ : ℂ => d)], ContinuousAt g 0 := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact continuousAt_id
      · exact continuousAt_const
    simpa only [List.map_cons, List.map_nil] using
      FiniteBilateral.continuousAt_qPsiTerm hq0 hq hU hL continuousAt_const hz0
        (by simpa only [List.map_cons, List.map_nil] using hB) (-(k : ℤ))
  let R := fun p : ℂ × ℕ => (q ^ (p.2 + 1) - p.1) * (q ^ (p.2 + 1) - d) /
    ((q ^ (p.2 + 1) - a) * (q ^ (p.2 + 1) - b) * z)
  have hp : Tendsto (fun p : ℂ × ℕ => q ^ (p.2 + 1))
      ((𝓝 (0 : ℂ)) ×ˢ atTop) (𝓝 (0 : ℂ)) := by
    have H : Tendsto (fun k : ℕ => q ^ (k + 1)) atTop (𝓝 (0 : ℂ)) := by
      simpa only [pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const q
    exact H.comp tendsto_snd
  have ht : Tendsto (fun p : ℂ × ℕ => p.1) ((𝓝 (0 : ℂ)) ×ˢ atTop) (𝓝 (0 : ℂ)) :=
    tendsto_fst
  have hR : Tendsto R ((𝓝 (0 : ℂ)) ×ˢ atTop) (𝓝 (0 : ℂ)) := by
    have H := ((hp.sub ht).mul (hp.sub_const d)).div
      (((hp.sub_const a).mul (hp.sub_const b)).mul_const z)
      (by simpa only [zero_sub] using
        mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha0) (neg_ne_zero.mpr hb0)) hz0)
    simp only [sub_self, zero_mul, zero_div] at H
    convert H using 1
  apply tendsto_tsum_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) hterm
  filter_upwards [hR.norm.eventually_lt_const (by norm_num : ‖(0 : ℂ)‖ < (1 / 2 : ℝ))]
    with p hpR
  rw [qPsiTerm_neg_succ hq0 hz0 hA, norm_mul]
  exact mul_le_mul_of_nonneg_right hpR.le (norm_nonneg _)

/-- The full two-psi-two is continuous when one lower parameter tends to zero, with the
other lower parameter regular and the upper parameters away from the positive q-lattice. -/
lemma continuousAt_qPsi_lower_zero {a b d q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1)
    (hD : ∀ j : ℕ, d * q ^ j ≠ 1)
    (hA : ∀ u ∈ [a, b], ∀ j : ℕ, u ≠ q ^ (j + 1)) :
    ContinuousAt (fun c : ℂ => qPsi [a, b] [c, d] q z) 0 := by
  have hB : QBilateralRegular [a, b] [0, d] q := by
    refine ⟨?_, hA⟩
    intro u hu j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · simp
    · exact hD j
  have hpos (c : ℂ) : qPhi [a, b, q] [c, d] q z =
      ∑' k : ℕ, qPsiTerm [a, b] [c, d] q z (k : ℤ) := by
    rw [SearsLimit.qPhi_eq_tsum]
    exact tsum_congr fun k => (BilateralGaussian.qPsiTerm_two_natCast_eq hq a b c d z k).symm
  have hp := BilateralContinuity.continuousAt_qPhi_three
    (a := fun _ => a) (b := fun _ => b) hq continuousAt_const
    continuousAt_const continuousAt_id continuousAt_const continuousAt_const hz1 hB.1
  have hn := continuousAt_tsum_negative hq0 hq ha0 hb0 hz0 hD hA
  have H := (hp.fun_add hn).sub (continuousAt_const (y := (1 : ℂ)))
  have hw : ContinuousAt (fun c : ℂ => c * d / (a * b * z)) 0 := by fun_prop
  apply ContinuousAt.congr H
  filter_upwards [BilateralContinuity.eventually_qDenominatorRegular hq
    continuousAt_id continuousAt_const hB.1,
    hw.norm.eventually (Iio_mem_nhds (by simp : ‖(0 : ℂ) * d / (a * b * z)‖ < 1))]
    with c hc hwc
  simp only [id_eq] at hc
  simp only [Pi.sub_apply, id_eq]
  have hS := qPsi_hasSum hq0 hq (And.intro hc hA) (by simp [ha0, hb0]) hz0
    (by simp) (by simpa only [List.prod_cons, List.prod_nil, mul_one, id_eq] using hwc)
    (fun _ => hz1)
  have hnat : Summable (fun k : ℕ => qPsiTerm [a, b] [c, d] q z (k : ℤ)) :=
    hS.summable.comp_injective Nat.cast_injective
  have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := by
    intro i j he
    exact_mod_cast neg_injective he
  have hneg : Summable (fun k : ℕ => qPsiTerm [a, b] [c, d] q z (-(k : ℤ))) :=
    hS.summable.comp_injective hinj
  have hzero : qPsiTerm [a, b] [c, d] q z 0 = 1 := by
    simp [qPsiTerm, qPsiExponent, qPochhammerListInt, qPochhammerInt]
  rw [hpos]
  simpa only [hzero, qPsi] using
    (tsum_int_eq_tsum_natCast_add_tsum_neg_natCast_sub hnat hneg).symm

end DLMF.QHypergeometric.BilateralZeroLowerContinuity
