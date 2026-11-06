/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BilateralGaussianTransformation

/-!
# Continuity of bilateral basic hypergeometric series

Clearing the two lower infinite products gives locally uniform geometric bounds
for the natural-index halves of a two-psi-two. This proves joint parameter continuity
throughout its convergence annulus, including terminating upper parameters.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralContinuity

/-- The natural-index balanced term with both lower infinite products cleared. -/
def clearedPositiveTerm (a b c d z q : ℂ) (k : ℕ) : ℂ :=
  qPochhammer a q k * qPochhammer b q k *
    qPochhammerInf (c * q ^ k) q * qPochhammerInf (d * q ^ k) q * z ^ k

/-- Clearing the lower infinite products expresses a balanced three-phi-two as an everywhere
regular coefficient series. -/
lemma qPhi_three_mul_inf {a b c d z q : ℂ} (hq : ‖q‖ < 1)
    (hcd : QDenominatorRegular [c, d] q) :
    qPhi [a, b, q] [c, d] q z * (qPochhammerInf c q * qPochhammerInf d q) =
      ∑' k, clearedPositiveTerm a b c d z q k := by
  rw [qPhi, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  have hC := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hcd (by simp : c ∈ [c, d]) k
  have hD := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hcd (by simp : d ∈ [c, d]) k
  have hQ := qPochhammer_self_ne_zero hq k
  rw [qPochhammerInf_mul_qPochhammer (a := c) hq k,
    qPochhammerInf_mul_qPochhammer (a := d) hq k]
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  norm_num only
  simp only [zpow_zero, mul_one, clearedPositiveTerm]
  field_simp

/-- Joint continuity of the cleared balanced series follows from a local geometric majorant.
-/
lemma continuousAt_tsum_clearedPositiveTerm {a b c d z : ℂ → ℂ} {x q : ℂ}
    (hq : ‖q‖ < 1) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hc : ContinuousAt c x) (hd : ContinuousAt d x) (hz : ContinuousAt z x)
    (hz1 : ‖z x‖ < 1) :
    ContinuousAt (fun t => ∑' k, clearedPositiveTerm (a t) (b t) (c t) (d t) (z t) q k) x := by
  obtain ⟨ρ, hρx, hρ1⟩ := exists_between hz1
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρx.le
  let R := ‖a x‖ + ‖b x‖ + ‖c x‖ + ‖d x‖ + 1
  have hRa : ‖a x‖ < R := by
    dsimp [R]
    nlinarith [norm_nonneg (a x), norm_nonneg (b x), norm_nonneg (c x), norm_nonneg (d x)]
  have hRb : ‖b x‖ < R := by
    dsimp [R]
    nlinarith [norm_nonneg (a x), norm_nonneg (b x), norm_nonneg (c x), norm_nonneg (d x)]
  have hRc : ‖c x‖ < R := by
    dsimp [R]
    nlinarith [norm_nonneg (a x), norm_nonneg (b x), norm_nonneg (c x), norm_nonneg (d x)]
  have hRd : ‖d x‖ < R := by
    dsimp [R]
    nlinarith [norm_nonneg (a x), norm_nonneg (b x), norm_nonneg (c x), norm_nonneg (d x)]
  have ea : ∀ᶠ t in 𝓝 x, ‖a t‖ ≤ R :=
    (ha.norm.eventually (Iio_mem_nhds hRa)).mono fun _ h => h.le
  have eb : ∀ᶠ t in 𝓝 x, ‖b t‖ ≤ R :=
    (hb.norm.eventually (Iio_mem_nhds hRb)).mono fun _ h => h.le
  have ec : ∀ᶠ t in 𝓝 x, ‖c t‖ ≤ R :=
    (hc.norm.eventually (Iio_mem_nhds hRc)).mono fun _ h => h.le
  have ed : ∀ᶠ t in 𝓝 x, ‖d t‖ ≤ R :=
    (hd.norm.eventually (Iio_mem_nhds hRd)).mono fun _ h => h.le
  have ez : ∀ᶠ t in 𝓝 x, ‖z t‖ ≤ ρ :=
    (hz.norm.eventually (Iio_mem_nhds hρx)).mono fun _ h => h.le
  let E := Real.exp (R / (1 - ‖q‖))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hInf : Continuous (fun u : ℂ => qPochhammerInf u q) :=
    (differentiable_qPochhammerInf_left hq).continuous
  have hterm (k : ℕ) : ContinuousAt
      (fun t => clearedPositiveTerm (a t) (b t) (c t) (d t) (z t) q k) x := by
    exact (((((continuous_qPochhammer q k).continuousAt.comp ha).mul
      ((continuous_qPochhammer q k).continuousAt.comp hb)).mul
      (hInf.continuousAt.comp (hc.mul_const _))).mul
      (hInf.continuousAt.comp (hd.mul_const _))).mul (hz.pow k)
  have hbound : ∀ᶠ t in 𝓝 x, ∀ k : ℕ,
      ‖clearedPositiveTerm (a t) (b t) (c t) (d t) (z t) q k‖ ≤ E ^ 4 * ρ ^ k := by
    filter_upwards [ea, eb, ec, ed, ez] with t hat hbt hct hdt hzt k
    have hfinite {u : ℂ} (hu : ‖u‖ ≤ R) : ‖qPochhammer u q k‖ ≤ E := by
      exact (norm_qPochhammer_le_exp hq k).trans (Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right hu (sub_nonneg.mpr hq.le)))
    have hinfinite {u : ℂ} (hu : ‖u‖ ≤ R) : ‖qPochhammerInf (u * q ^ k) q‖ ≤ E := by
      refine norm_qPochhammerInf_le_exp hq |>.trans (Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right ?_ (sub_nonneg.mpr hq.le)))
      rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg q) hq.le)).trans hu
    simp only [clearedPositiveTerm, norm_mul, norm_pow]
    calc
      _ ≤ E * E * E * E * ρ ^ k := by
        gcongr
        · exact hfinite hat
        · exact hfinite hbt
        · exact hinfinite hct
        · exact hinfinite hdt
      _ = _ := by ring
  exact tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (E ^ 4)) hterm hbound

/-- A nonzero infinite product excludes every zero factor. -/
lemma mul_pow_ne_one_of_qPochhammerInf_ne_zero {a q : ℂ} (hq : ‖q‖ < 1)
    (ha : qPochhammerInf a q ≠ 0) (j : ℕ) : a * q ^ j ≠ 1 := by
  intro he
  have H := qPochhammerInf_mul_qPochhammer (a := a) hq (j + 1)
  rw [qPochhammer_succ, he, sub_self, mul_zero, zero_mul] at H
  exact ha H

/-- A pair of nonzero infinite products gives lower-parameter regularity. -/
lemma qDenominatorRegular_of_inf_ne_zero {c d q : ℂ} (hq : ‖q‖ < 1)
    (hc : qPochhammerInf c q ≠ 0) (hd : qPochhammerInf d q ≠ 0) :
    QDenominatorRegular [c, d] q := by
  intro u hu j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact mul_pow_ne_one_of_qPochhammerInf_ne_zero hq hc j
  · exact mul_pow_ne_one_of_qPochhammerInf_ne_zero hq hd j

/-- Lower-parameter regularity is stable near a regular pair of continuously varying parameters.
-/
lemma eventually_qDenominatorRegular {c d : ℂ → ℂ} {x q : ℂ} (hq : ‖q‖ < 1)
    (hc : ContinuousAt c x) (hd : ContinuousAt d x)
    (hcd : QDenominatorRegular [c x, d x] q) :
    ∀ᶠ t in 𝓝 x, QDenominatorRegular [c t, d t] q := by
  have hInf : Continuous (fun u : ℂ => qPochhammerInf u q) :=
    (differentiable_qPochhammerInf_left hq).continuous
  have hC := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hcd (c x) (by simp) j)))
  have hD := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hcd (d x) (by simp) j)))
  filter_upwards [(hInf.continuousAt.comp hc).eventually_ne hC,
    (hInf.continuousAt.comp hd).eventually_ne hD] with t hCt hDt
  exact qDenominatorRegular_of_inf_ne_zero hq hCt hDt

/-- The balanced three-phi-two is jointly continuous at regular lower parameters and inside its
unit disk of convergence. -/
lemma continuousAt_qPhi_three {a b c d z : ℂ → ℂ} {x q : ℂ}
    (hq : ‖q‖ < 1) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hc : ContinuousAt c x) (hd : ContinuousAt d x) (hz : ContinuousAt z x)
    (hz1 : ‖z x‖ < 1) (hcd : QDenominatorRegular [c x, d x] q) :
    ContinuousAt (fun t => qPhi [a t, b t, q] [c t, d t] q (z t)) x := by
  have hInf : Continuous (fun u : ℂ => qPochhammerInf u q) :=
    (differentiable_qPochhammerInf_left hq).continuous
  have hC := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hcd (c x) (by simp) j)))
  have hD := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hcd (d x) (by simp) j)))
  have H := (continuousAt_tsum_clearedPositiveTerm hq ha hb hc hd hz hz1).div₀
    ((hInf.continuousAt.comp hc).mul (hInf.continuousAt.comp hd)) (mul_ne_zero hC hD)
  apply H.congr
  filter_upwards [(hInf.continuousAt.comp hc).eventually_ne hC,
    (hInf.continuousAt.comp hd).eventually_ne hD] with t hCt hDt
  exact ((eq_div_iff (mul_ne_zero hCt hDt)).mpr
    (qPhi_three_mul_inf hq (qDenominatorRegular_of_inf_ne_zero hq hCt hDt))).symm

/-- Regularity of the reciprocal lower parameters excludes the positive q-lattice for the
original upper parameters. -/
lemma upper_regular_of_reciprocal {a b q : ℂ} (hq0 : q ≠ 0)
    (hAB : QDenominatorRegular [q / a, q / b] q) :
    ∀ u ∈ [a, b], ∀ j : ℕ, u ≠ q ^ (j + 1) := by
  intro u hu j he
  have hmem : q / u ∈ [q / a, q / b] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
    rcases hu with rfl | rfl <;> simp
  apply hAB (q / u) hmem j
  rw [he, pow_succ]
  field_simp

/-- Two-psi-two is jointly continuous in all parameters throughout its annulus of convergence.
-/
lemma continuousAt_qPsi_two {a b c d z : ℂ → ℂ} {x q : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hc : ContinuousAt c x) (hd : ContinuousAt d x) (hz : ContinuousAt z x)
    (ha0 : a x ≠ 0) (hb0 : b x ≠ 0) (hc0 : c x ≠ 0) (hd0 : d x ≠ 0) (hz0 : z x ≠ 0)
    (hB : QBilateralRegular [a x, b x] [c x, d x] q)
    (hzw : ‖c x * d x / (a x * b x * z x)‖ < 1) (hz1 : ‖z x‖ < 1) :
    ContinuousAt (fun t => qPsi [a t, b t] [c t, d t] q (z t)) x := by
  let w := fun t => c t * d t / (a t * b t * z t)
  have hw : ContinuousAt w x := (hc.mul hd).div₀ ((ha.mul hb).mul hz)
    (mul_ne_zero (mul_ne_zero ha0 hb0) hz0)
  have hqa : ContinuousAt (fun t => q / a t) x := continuousAt_const.div₀ ha ha0
  have hqb : ContinuousAt (fun t => q / b t) x := continuousAt_const.div₀ hb hb0
  have hqc : ContinuousAt (fun t => q / c t) x := continuousAt_const.div₀ hc hc0
  have hqd : ContinuousAt (fun t => q / d t) x := continuousAt_const.div₀ hd hd0
  have hAB : QDenominatorRegular [q / a x, q / b x] q := by
    simpa only [List.map_cons, List.map_nil] using
      FiniteBilateral.qDenominatorRegular_reciprocal (by simp [ha0, hb0]) hB.2
  have H := ((continuousAt_qPhi_three hq ha hb hc hd hz hz1 hB.1).add
    (continuousAt_qPhi_three hq hqc hqd hqa hqb hw hzw hAB)).sub (continuousAt_const (y := (1 : ℂ)))
  apply H.congr
  filter_upwards [eventually_qDenominatorRegular hq hc hd hB.1,
    eventually_qDenominatorRegular hq hqa hqb hAB,
    ha.eventually_ne ha0, hb.eventually_ne hb0, hc.eventually_ne hc0, hd.eventually_ne hd0,
    hz.eventually_ne hz0, hw.norm.eventually (Iio_mem_nhds hzw),
    hz.norm.eventually (Iio_mem_nhds hz1)] with t hCDt hABt hat hbt hct hdt hzt hwt hzt1
  have hBt : QBilateralRegular [a t, b t] [c t, d t] q :=
    ⟨hCDt, upper_regular_of_reciprocal hq0 hABt⟩
  have hbal : c t * d t = a t * b t * w t * z t := by dsimp [w]; field_simp
  exact (BilateralGaussian.qPsi_two_eq_qPhi_halves hat hbt hct hdt hzt hq0 hq
    hwt hzt1 hbal hBt).symm

/-- Finite-prefix nonvanishing together with a locally bounded parameter gives full lower
regularity near a punctured point. -/
lemma eventually_regular_of_prefix {f : ℂ → ℂ} {x q : ℂ} (hq : ‖q‖ < 1)
    (hf : ContinuousAt f x)
    (hprefix : ∀ N : ℕ, ∀ᶠ t in 𝓝[≠] x, qPochhammer (f t) q N ≠ 0) :
    ∀ᶠ t in 𝓝[≠] x, ∀ j : ℕ, f t * q ^ j ≠ 1 := by
  let R := ‖f x‖ + 1
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hbound : ∀ᶠ t in 𝓝[≠] x, ‖f t‖ ≤ R :=
    nhdsWithin_le_nhds ((hf.norm.eventually (Iio_mem_nhds
      (by dsimp [R]; linarith))).mono fun _ h => h.le)
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).norm.const_mul R
  have he : ∀ᶠ N : ℕ in atTop, R * ‖q ^ N‖ < 1 :=
    hp.eventually (Iio_mem_nhds (by simp : R * ‖(0 : ℂ)‖ < 1))
  obtain ⟨N, hN⟩ := he.exists
  filter_upwards [hbound, hprefix N] with t hft hPt j
  by_cases hj : j < N
  · have hPj := qPochhammer_ne_zero_of_le hPt (Nat.succ_le_iff.mpr hj)
    intro hzero
    apply hPj
    rw [qPochhammer_succ, hzero, sub_self, mul_zero]
  · intro hzero
    have hpow : ‖q‖ ^ j ≤ ‖q‖ ^ N :=
      pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_of_not_gt hj)
    have H : ‖f t * q ^ j‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ R * ‖q‖ ^ N := mul_le_mul hft hpow (by positivity) hR0
        _ < 1 := by simpa only [norm_pow] using hN
    rw [hzero, norm_one] at H
    exact lt_irrefl _ H

/-- A linear parameter is regular near a point of the punctured plane. -/
lemma eventually_regular_mul (u q x : ℂ) (hq : ‖q‖ < 1) :
    ∀ᶠ t in 𝓝[≠] x, ∀ j : ℕ, (u * t) * q ^ j ≠ 1 := by
  apply eventually_regular_of_prefix hq (continuousAt_const.mul continuousAt_id)
  intro N
  simpa only [pow_one, Pi.mul_apply, id_eq] using
    FiniteBilateral.eventually_qPochhammer_mul_pow_ne_zero u q x 1 N (by omega)

/-- A reciprocal parameter is regular near a nonzero point of the punctured plane. -/
lemma eventually_regular_div {u q x : ℂ} (hu0 : u ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hx0 : x ≠ 0) :
    ∀ᶠ t in 𝓝[≠] x, ∀ j : ℕ, (u / t) * q ^ j ≠ 1 := by
  apply eventually_regular_of_prefix hq (continuousAt_const.div₀ continuousAt_id hx0)
  intro N
  simpa only [pow_one, id_eq] using
    FiniteBilateral.eventually_qPochhammer_div_pow_ne_zero hu0 hq0 x 1 N (by omega)

/-- Bilateral regularity of two parameter pairs persists under continuous parameter variation.
-/
lemma eventually_qBilateralRegular_two {a b c d : ℂ → ℂ} {x q : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hc : ContinuousAt c x) (hd : ContinuousAt d x) (ha0 : a x ≠ 0) (hb0 : b x ≠ 0)
    (hB : QBilateralRegular [a x, b x] [c x, d x] q) :
    ∀ᶠ t in 𝓝 x, QBilateralRegular [a t, b t] [c t, d t] q := by
  have hqa : ContinuousAt (fun t => q / a t) x := continuousAt_const.div₀ ha ha0
  have hqb : ContinuousAt (fun t => q / b t) x := continuousAt_const.div₀ hb hb0
  have hAB : QDenominatorRegular [q / a x, q / b x] q := by
    simpa only [List.map_cons, List.map_nil] using
      FiniteBilateral.qDenominatorRegular_reciprocal (by simp [ha0, hb0]) hB.2
  filter_upwards [eventually_qDenominatorRegular hq hc hd hB.1,
    eventually_qDenominatorRegular hq hqa hqb hAB] with t hCDt hABt
  exact ⟨hCDt, upper_regular_of_reciprocal hq0 hABt⟩

end DLMF.QHypergeometric.BilateralContinuity
