/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BilateralGaussianSymmetry

/-!
# Transposing free parameters in the bilateral Gaussian series

The Gaussian representation of a two-psi-two is symmetric in its four free parameters.
Transposing parameters from different pairs gives Bailey's first bilateral transformation,
DLMF 17.10.1. The convergence assumptions control the four resulting arguments.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralGaussianTransposition

/-- A free parameter transposition preserves the bilateral Gaussian summand. -/
lemma gaussianTerm_transpose (a c d e f q : ℂ) (k : ℤ) :
    BilateralGaussian.gaussianTerm a c d e f q k =
      BilateralGaussian.gaussianTerm a c f e d q k := by
  have hprod : c * f * e * d = c * d * e * f := by ring
  simp only [BilateralGaussian.gaussianTerm, hprod, qPochhammerListInt,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

/-- A parameter inside the unit disk avoids the denominator q-lattice. -/
lemma mul_pow_ne_one_of_norm_lt_one {u q : ℂ} (hu : ‖u‖ < 1) (hq : ‖q‖ < 1)
    (j : ℕ) : u * q ^ j ≠ 1 :=
  (sub_ne_zero.mp (one_sub_mul_pow_ne_zero_of_norm hu hq j)).symm

/-- Transposing free parameters in the Gaussian representation transforms a two-psi-two while
retaining the regularity of the two central products. -/
lemma transpose {a c d e f q : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hcentral : QDenominatorRegular [a * q, q / a] q)
    (hB : QBilateralRegular [c, d, e, f]
      [a * q / c, a * q / d, a * q / e, a * q / f] q)
    (hw : ‖a * q / (c * d)‖ < 1) (hz : ‖a * q / (e * f)‖ < 1)
    (hu : ‖a * q / (c * f)‖ < 1) (hv : ‖a * q / (e * d)‖ < 1) :
    qPsi [e, f] [a * q / c, a * q / d] q (a * q / (e * f)) =
      qProductRatioInf [q / d, a * q / f, a * q / (c * f), a * q / (e * d)]
        [q / f, a * q / d, a * q / (c * d), a * q / (e * f)] q *
          qPsi [e, d] [a * q / c, a * q / f] q (a * q / (e * d)) := by
  have hr : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by rw [← Complex.cpow_nat_mul]; norm_num
  have hBef : QBilateralRegular [e, f] [a * q / c, a * q / d] q := by
    constructor
    · intro x hx j
      apply hB.1 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
    · intro x hx j
      apply hB.2 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
  have hBed : QBilateralRegular [e, d] [a * q / c, a * q / f] q := by
    constructor
    · intro x hx j
      apply hB.1 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
    · intro x hx j
      apply hB.2 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
  have hBs : QBilateralRegular [c, f, e, d]
      [a * q / c, a * q / f, a * q / e, a * q / d] q := by
    constructor <;> intro x hx j
    · apply hB.1 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
    · apply hB.2 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
  have hden : QDenominatorRegular
      [a * q, q / a, a * q / (c * d), a * q / (e * f)] q := by
    intro x hx j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact hcentral _ (by simp) j
    · exact hcentral _ (by simp) j
    · exact mul_pow_ne_one_of_norm_lt_one hw hq j
    · exact mul_pow_ne_one_of_norm_lt_one hz hq j
  have hdens : QDenominatorRegular
      [a * q, q / a, a * q / (c * f), a * q / (e * d)] q := by
    intro x hx j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact hcentral _ (by simp) j
    · exact hcentral _ (by simp) j
    · exact mul_pow_ne_one_of_norm_lt_one hu hq j
    · exact mul_pow_ne_one_of_norm_lt_one hv hq j
  have H := BilateralGaussian.qPsi_two_eq_gaussian hr ha0 ha1 hc0 hd0 he0 hf0 hq0 hq
    hden hBef hB hw hz
  have Hs := BilateralGaussian.qPsi_two_eq_gaussian hr ha0 ha1 hc0 hf0 he0 hd0 hq0 hq
    hdens hBed hBs hu hv
  have hG : (∑' k : ℤ, BilateralGaussian.gaussianTerm a c d e f q k) =
      ∑' k : ℤ, BilateralGaussian.gaussianTerm a c f e d q k :=
    tsum_congr (gaussianTerm_transpose a c d e f q)
  rw [← hG] at Hs
  have hRec := FiniteBilateral.qDenominatorRegular_reciprocal
    (by simp [hc0, hd0, he0, hf0]) hB.2
  have hPc : qPochhammerInf (q / c) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hRec _ (by simp) j)))
  have hPf : qPochhammerInf (q / f) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hRec _ (by simp) j)))
  have hPd : qPochhammerInf (a * q / d) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hB.1 _ (by simp) j)))
  have hPe : qPochhammerInf (a * q / e) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hB.1 _ (by simp) j)))
  have hAq : qPochhammerInf (a * q) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hcentral _ (by simp) j)))
  have hQa : qPochhammerInf (q / a) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hcentral _ (by simp) j)))
  have hW := qPochhammerInf_ne_zero_of_norm_lt_one hw hq
  have hZ := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  have hU := qPochhammerInf_ne_zero_of_norm_lt_one hu hq
  have hV := qPochhammerInf_ne_zero_of_norm_lt_one hv hq
  rw [H, Hs]
  simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  generalize qPochhammerInf (q / c) q = Pc at hPc ⊢
  generalize qPochhammerInf (q / f) q = Pf at hPf ⊢
  generalize qPochhammerInf (a * q / d) q = Pd at hPd ⊢
  generalize qPochhammerInf (a * q / e) q = Pe at hPe ⊢
  generalize qPochhammerInf (a * q) q = Aq at hAq ⊢
  generalize qPochhammerInf (q / a) q = Qa at hQa ⊢
  generalize qPochhammerInf (a * q / (c * d)) q = W at hW ⊢
  generalize qPochhammerInf (a * q / (e * f)) q = Z at hZ ⊢
  generalize qPochhammerInf (a * q / (c * f)) q = U at hU ⊢
  generalize qPochhammerInf (a * q / (e * d)) q = V at hV ⊢
  generalize qPochhammerInf (q / d) q = D at ⊢
  generalize qPochhammerInf (a * q / f) q = F at ⊢
  field_simp

/-- Bailey's first two-psi-two transformation follows from a Gaussian transposition when the
intermediate central and reciprocal parameters are regular. -/
lemma transformation_one_of_generic (a b c d q z : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hpar : ∀ u ∈ [a, b, c, d, z], u ≠ 0)
    (hB : QBilateralRegular [a, b] [c, d] q ∧
      QBilateralRegular [a, a * b * z / d] [a * z, c] q)
    (hz : ‖c * d / (a * b)‖ < ‖z‖ ∧ ‖z‖ < 1)
    (hd : ‖c * d / (a * b)‖ < ‖d / a‖ ∧ ‖d / a‖ < 1)
    (hcentral : QDenominatorRegular [a * b * z, q ^ 2 / (a * b * z)] q)
    (hExtra : QDenominatorRegular [b * z, c * q / (a * b * z)] q)
    (ha1 : a * b * z / q ≠ 1) :
    qPsi [a, b] [c, d] q z =
      qProductRatioInf [a * z, d / a, c / b, d * q / (a * b * z)]
        [z, d, q / b, c * d / (a * b * z)] q *
          qPsi [a, a * b * z / d] [a * z, c] q (d / a) := by
  have ha0 := hpar a (by simp)
  have hb0 := hpar b (by simp)
  have hc0 := hpar c (by simp)
  have hd0 := hpar d (by simp)
  have hz0 := hpar z (by simp)
  let A := a * b * z / q
  let C := a * b * z / c
  let D := a * b * z / d
  have hA0 : A ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hz0) hq0
  have hC0 : C ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hz0) hc0
  have hD0 : D ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hz0) hd0
  have hAq : A * q = a * b * z := by dsimp [A]; field_simp
  have hAc : A * q / C = c := by dsimp [A, C]; field_simp
  have hAd : A * q / D = d := by dsimp [A, D]; field_simp
  have hAa : A * q / a = b * z := by dsimp [A]; field_simp
  have hAb : A * q / b = a * z := by dsimp [A]; field_simp
  have hqA : q / A = q ^ 2 / (a * b * z) := by dsimp [A]; field_simp
  have hwA : A * q / (C * D) = c * d / (a * b * z) := by
    dsimp [A, C, D]
    field_simp
  have hzA : A * q / (a * b) = z := by dsimp [A]; field_simp
  have huA : A * q / (C * b) = c / b := by dsimp [A, C]; field_simp
  have hvA : A * q / (a * D) = d / a := by dsimp [A, D]; field_simp
  have hqC : q / C = c * q / (a * b * z) := by dsimp [C]; field_simp
  have hqD : q / D = d * q / (a * b * z) := by dsimp [D]; field_simp
  have hCreg : ∀ j : ℕ, C ≠ q ^ (j + 1) := by
    intro j hEq
    have hRec := hExtra (c * q / (a * b * z)) (by simp) j
    rw [← hqC, hEq, pow_succ] at hRec
    apply hRec
    field_simp
  have hBfour : QBilateralRegular [C, D, a, b] [c, d, b * z, a * z] q := by
    constructor
    · intro u hu j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu | hu | hu <;> rw [hu]
      · exact hB.1.1 _ (by simp) j
      · exact hB.1.1 _ (by simp) j
      · exact hExtra _ (by simp) j
      · exact hB.2.1 _ (by simp) j
    · intro u hu j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu | hu | hu <;> rw [hu]
      · exact hCreg j
      · exact hB.2.2 _ (by simp [D]) j
      · exact hB.1.2 _ (by simp) j
      · exact hB.1.2 _ (by simp) j
  have hBfour' : QBilateralRegular [C, D, a, b]
      [A * q / C, A * q / D, A * q / a, A * q / b] q := by
    rwa [hAc, hAd, hAa, hAb]
  have hcentral' : QDenominatorRegular [A * q, q / A] q := by rwa [hAq, hqA]
  have hw : ‖c * d / (a * b * z)‖ < 1 := by
    rw [show c * d / (a * b * z) = (c * d / (a * b)) / z by field_simp,
      norm_div, div_lt_one (norm_pos_iff.mpr hz0)]
    exact hz.1
  have hcb : ‖c / b‖ < 1 := by
    have hpos := norm_pos_iff.mpr (div_ne_zero hd0 ha0)
    have hprod : ‖c / b‖ * ‖d / a‖ < ‖d / a‖ := by
      rw [← norm_mul, show c / b * (d / a) = c * d / (a * b) by field_simp]
      exact hd.1
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hpos.le
    simp only [one_mul] at hm
    exact (not_lt_of_ge hm) hprod
  have H := transpose hA0 ha1 hC0 hD0 ha0 hb0 hq0 hq hcentral' hBfour'
    (by rwa [hwA]) (by rw [hzA]; exact hz.2)
    (by rwa [huA]) (by rw [hvA]; exact hd.2)
  rw [hAc, hAd, hAb, hqD, hwA, hzA, huA, hvA,
    FiniteBilateral.qPsi_perm (List.Perm.refl [a, D]) (List.Perm.swap (a * z) c [])] at H
  rw [H]
  dsimp [D]
  simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_assoc, mul_left_comm, mul_comm]

/-- Bailey's first transformation extends through the intermediate Gaussian singularities
when the lower parameters are nonzero. -/
lemma transformation_one_nonzero_lower (a b c d q z : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hpar : ∀ u ∈ [a, b, c, d, z], u ≠ 0)
    (hden : QDenominatorRegular [z, d, q / b, c * d / (a * b * z)] q)
    (hB : QBilateralRegular [a, b] [c, d] q ∧
      QBilateralRegular [a, a * b * z / d] [a * z, c] q)
    (hz : ‖c * d / (a * b)‖ < ‖z‖ ∧ ‖z‖ < 1)
    (hd : ‖c * d / (a * b)‖ < ‖d / a‖ ∧ ‖d / a‖ < 1) :
    qPsi [a, b] [c, d] q z =
      qProductRatioInf [a * z, d / a, c / b, d * q / (a * b * z)]
        [z, d, q / b, c * d / (a * b * z)] q *
          qPsi [a, a * b * z / d] [a * z, c] q (d / a) := by
  have ha0 := hpar a (by simp)
  have hb0 := hpar b (by simp)
  have hc0 := hpar c (by simp)
  have hd0 := hpar d (by simp)
  have hz0 := hpar z (by simp)
  have hw : ‖c * d / (a * b * z)‖ < 1 := by
    rw [show c * d / (a * b * z) = (c * d / (a * b)) / z by field_simp,
      norm_div, div_lt_one (norm_pos_iff.mpr hz0)]
    exact hz.1
  have hcb : ‖c / b‖ < 1 := by
    have hpos := norm_pos_iff.mpr (div_ne_zero hd0 ha0)
    have hprod : ‖c / b‖ * ‖d / a‖ < ‖d / a‖ := by
      rw [← norm_mul, show c / b * (d / a) = c * d / (a * b) by field_simp]
      exact hd.1
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hpos.le
    simp only [one_mul] at hm
    exact (not_lt_of_ge hm) hprod
  have hleft := BilateralContinuity.continuousAt_qPsi_two hq0 hq continuousAt_const
    continuousAt_const continuousAt_const continuousAt_const continuousAt_id
    ha0 hb0 hc0 hd0 hz0 hB.1 hw hz.2
  have hE : ContinuousAt (fun t : ℂ => a * b * t / d) z := by fun_prop
  have hAz : ContinuousAt (fun t : ℂ => a * t) z := by fun_prop
  have hE0 : a * b * z / d ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hz0) hd0
  have hda0 : d / a ≠ 0 := div_ne_zero hd0 ha0
  have hinner : (a * z) * c / (a * (a * b * z / d) * (d / a)) = c / b := by field_simp
  have htrans := BilateralContinuity.continuousAt_qPsi_two hq0 hq continuousAt_const hE hAz
    continuousAt_const continuousAt_const ha0 hE0 (mul_ne_zero ha0 hz0) hc0 hda0 hB.2
    (by simpa only [hinner] using hcb) hd.2
  have hInf : Continuous (fun u : ℂ => qPochhammerInf u q) :=
    (differentiable_qPochhammerInf_left hq).continuous
  have hW : ContinuousAt (fun t : ℂ => c * d / (a * b * t)) z :=
    continuousAt_const.div₀ (continuousAt_const.fun_mul continuousAt_id)
      (mul_ne_zero (mul_ne_zero ha0 hb0) hz0)
  have hDQ : ContinuousAt (fun t : ℂ => d * q / (a * b * t)) z :=
    continuousAt_const.div₀ (continuousAt_const.fun_mul continuousAt_id)
      (mul_ne_zero (mul_ne_zero ha0 hb0) hz0)
  have hDen := FiniteBilateral.qPochhammerListInf_ne_zero hq hden
  have hpref : ContinuousAt (fun t => qProductRatioInf
      [a * t, d / a, c / b, d * q / (a * b * t)]
      [t, d, q / b, c * d / (a * b * t)] q) z := by
    simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    apply ContinuousAt.div₀
    · exact (hInf.continuousAt.comp hAz).fun_mul
        (continuousAt_const.fun_mul (continuousAt_const.fun_mul (hInf.continuousAt.comp hDQ)))
    · exact hInf.continuousAt.fun_mul
        (continuousAt_const.fun_mul (continuousAt_const.fun_mul (hInf.continuousAt.comp hW)))
    · simpa only [qPochhammerListInf, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one] using hDen
  have hright := hpref.fun_mul htrans
  have hregB := BilateralContinuity.eventually_qBilateralRegular_two hq0 hq
    continuousAt_const hE hAz continuousAt_const ha0 hE0 hB.2
  have hregA := BilateralContinuity.eventually_regular_mul (a * b) q z hq
  have hregAi := BilateralContinuity.eventually_regular_div
    (div_ne_zero (pow_ne_zero 2 hq0) (mul_ne_zero ha0 hb0)) hq0 hq hz0
  have hregBz := BilateralContinuity.eventually_regular_mul b q z hq
  have hregCi := BilateralContinuity.eventually_regular_div
    (div_ne_zero (mul_ne_zero hc0 hq0) (mul_ne_zero ha0 hb0)) hq0 hq hz0
  have hAvoid := FiniteBilateral.eventually_qPochhammer_mul_pow_ne_zero
    (a * b / q) q z 1 1 (by omega)
  have hEq : ∀ᶠ t in 𝓝[≠] z, qPsi [a, b] [c, d] q t =
      qProductRatioInf [a * t, d / a, c / b, d * q / (a * b * t)]
        [t, d, q / b, c * d / (a * b * t)] q *
          qPsi [a, a * b * t / d] [a * t, c] q (d / a) := by
    filter_upwards [nhdsWithin_le_nhds hregB, hregA, hregAi, hregBz, hregCi, hAvoid,
      nhdsWithin_le_nhds (continuousAt_id.eventually_ne hz0),
      nhdsWithin_le_nhds (continuousAt_id.norm.eventually (Ioi_mem_nhds hz.1)),
      nhdsWithin_le_nhds (continuousAt_id.norm.eventually (Iio_mem_nhds hz.2))]
      with t hBt hAt hAit hBzt hCit hAvoidt ht0 hzt hzt1
    have hcentral : QDenominatorRegular [a * b * t, q ^ 2 / (a * b * t)] q := by
      intro u hu j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu <;> rw [hu]
      · exact hAt j
      · simpa only [div_mul_eq_div_div] using hAit j
    have hExtra : QDenominatorRegular [b * t, c * q / (a * b * t)] q := by
      intro u hu j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu <;> rw [hu]
      · exact hBzt j
      · simpa only [div_mul_eq_div_div] using hCit j
    have hA1 : a * b * t / q ≠ 1 := by
      have hsub : 1 - a * b * t / q ≠ 0 := by
        simpa only [pow_one, qPochhammer_one,
          show a * b / q * t = a * b * t / q by ring] using hAvoidt
      exact (sub_ne_zero.mp hsub).symm
    have hpart : ∀ u ∈ [a, b, c, d, t], u ≠ 0 := by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption
    exact transformation_one_of_generic a b c d q t hq hq0 hpart ⟨hB.1, hBt⟩
      ⟨hzt, hzt1⟩ hd hcentral hExtra hA1
  exact tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' (hEq.mono fun _ h => h.symm))

end DLMF.QHypergeometric.BilateralGaussianTransposition
