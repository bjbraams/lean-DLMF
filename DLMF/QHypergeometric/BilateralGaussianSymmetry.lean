/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BilateralGaussianLimit
public import DLMF.QHypergeometric.BilateralContinuity

/-!
# Pair symmetry of the bilateral Gaussian transformation

Swapping the two pairs in the Gaussian bilateral series gives the second two-psi-two
transformation of DLMF 17.10.2. Joint annular continuity extends the identity through
the central q-lattice excluded by the intermediate Gaussian representation.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralGaussianSymmetry

/-- The Gaussian summand is unchanged when its two free parameter pairs are exchanged. -/
lemma gaussianTerm_pair_swap (a c d e f q : ℂ) (k : ℤ) :
    BilateralGaussian.gaussianTerm a c d e f q k =
      BilateralGaussian.gaussianTerm a e f c d q k := by
  have hprod : e * f * c * d = c * d * e * f := by ring
  simp only [BilateralGaussian.gaussianTerm, hprod, qPochhammerListInt,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

/-- Exchanging the parameter pairs in the Gaussian representation gives a cleared two-psi-two
transformation while retaining the central q-lattice assumptions. -/
lemma pair_swap {a c d e f q : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hden : QDenominatorRegular [a * q, q / a, a * q / (c * d), a * q / (e * f)] q)
    (hB : QBilateralRegular [c, d, e, f]
      [a * q / c, a * q / d, a * q / e, a * q / f] q)
    (hw : ‖a * q / (c * d)‖ < 1) (hz : ‖a * q / (e * f)‖ < 1) :
    qPsi [e, f] [a * q / c, a * q / d] q (a * q / (e * f)) *
        qPochhammerListInf [q / e, q / f, a * q / c, a * q / d] q =
      qPochhammerListInf [q / c, q / d, a * q / e, a * q / f] q *
        qPsi [c, d] [a * q / e, a * q / f] q (a * q / (c * d)) := by
  have hr : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by rw [← Complex.cpow_nat_mul]; norm_num
  have hBef : QBilateralRegular [e, f] [a * q / c, a * q / d] q := by
    constructor
    · intro x hx j
      apply hB.1 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      aesop
    · intro x hx j
      apply hB.2 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      aesop
  have hBcd : QBilateralRegular [c, d] [a * q / e, a * q / f] q := by
    constructor
    · intro x hx j
      apply hB.1 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      aesop
    · intro x hx j
      apply hB.2 x ?_ j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      aesop
  have hBs : QBilateralRegular [e, f, c, d]
      [a * q / e, a * q / f, a * q / c, a * q / d] q :=
    ⟨fun x hx j => hB.1 x (by simpa only [List.mem_cons, List.not_mem_nil, or_false,
        or_comm, or_left_comm, or_assoc] using hx) j,
      fun x hx j => hB.2 x (by simpa only [List.mem_cons, List.not_mem_nil, or_false,
        or_comm, or_left_comm, or_assoc] using hx) j⟩
  have hdens : QDenominatorRegular
      [a * q, q / a, a * q / (e * f), a * q / (c * d)] q := by
    intro x hx j
    exact hden x (by simpa only [List.mem_cons, List.not_mem_nil, or_false,
      or_comm, or_left_comm, or_assoc] using hx) j
  have H := BilateralGaussian.qPsi_two_eq_gaussian hr ha0 ha1 hc0 hd0 he0 hf0 hq0 hq
    hden hBef hB hw hz
  have Hs := BilateralGaussian.qPsi_two_eq_gaussian hr ha0 ha1 he0 hf0 hc0 hd0 hq0 hq
    hdens hBcd hBs hz hw
  have hG : (∑' k : ℤ, BilateralGaussian.gaussianTerm a c d e f q k) =
      ∑' k : ℤ, BilateralGaussian.gaussianTerm a e f c d q k :=
    tsum_congr (gaussianTerm_pair_swap a c d e f q)
  rw [← hG] at Hs
  rw [H, Hs]
  unfold qProductRatioInf
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The second two-psi-two transformation follows from Gaussian pair symmetry when the
intermediate central products are regular. -/
lemma transformation_two_of_central_regular (a b c d q z : ℂ) (hq : ‖q‖ < 1)
    (hq0 : q ≠ 0) (hpar : ∀ u ∈ [a, b, c, d, z], u ≠ 0)
    (hden : QDenominatorRegular [q / a, q / b, c, d] q)
    (hB : QBilateralRegular [a, b] [c, d] q ∧
      QBilateralRegular [a * b * z / c, a * b * z / d] [a * z, b * z] q)
    (hw : ‖c * d / (a * b * z)‖ < 1) (hz : ‖z‖ < 1)
    (hcentral : QDenominatorRegular [a * b * z, q ^ 2 / (a * b * z),
      c * d / (a * b * z), z] q) (ha1 : a * b * z / q ≠ 1) :
    qPsi [a, b] [c, d] q z =
      qProductRatioInf [a * z, b * z, c * q / (a * b * z), d * q / (a * b * z)]
        [q / a, q / b, c, d] q *
          qPsi [a * b * z / c, a * b * z / d] [a * z, b * z] q
            (c * d / (a * b * z)) := by
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
  have hBfour : QBilateralRegular [C, D, a, b] [c, d, b * z, a * z] q := by
    constructor
    · intro u hu j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu | hu | hu <;> rw [hu]
      · exact hB.1.1 _ (by simp) j
      · exact hB.1.1 _ (by simp) j
      · exact hB.2.1 _ (by simp) j
      · exact hB.2.1 _ (by simp) j
    · intro u hu j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu | hu | hu <;> rw [hu]
      · exact hB.2.2 _ (by simp [C]) j
      · exact hB.2.2 _ (by simp [D]) j
      · exact hB.1.2 _ (by simp) j
      · exact hB.1.2 _ (by simp) j
  have hBfour' : QBilateralRegular [C, D, a, b]
      [A * q / C, A * q / D, A * q / a, A * q / b] q := by
    rwa [hAc, hAd, hAa, hAb]
  have hcentral' : QDenominatorRegular [A * q, q / A, A * q / (C * D),
      A * q / (a * b)] q := by rwa [hwA, hzA, hAq, hqA]
  have H := pair_swap hA0 ha1 hC0 hD0 ha0 hb0 hq0 hq hcentral' hBfour'
    (by rwa [hwA]) (by rwa [hzA])
  rw [hAc, hAd, hAa, hAb, hwA, hzA] at H
  have hqC : q / C = c * q / (a * b * z) := by dsimp [C]; field_simp
  have hqD : q / D = d * q / (a * b * z) := by dsimp [D]; field_simp
  rw [hqC, hqD, FiniteBilateral.qPsi_perm (List.Perm.refl [C, D])
    (List.Perm.swap (a * z) (b * z) [])] at H
  have hI : qPochhammerListInf [c * q / (a * b * z), d * q / (a * b * z), b * z, a * z] q =
      qPochhammerListInf [a * z, b * z, c * q / (a * b * z), d * q / (a * b * z)] q := by
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_assoc, mul_left_comm, mul_comm]
  rw [hI] at H
  have hDen := FiniteBilateral.qPochhammerListInf_ne_zero hq hden
  unfold qProductRatioInf
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hDen).mpr H

/-- The second two-psi-two transformation holds throughout its full annulus by continuity,
including the central q-lattice excluded by the intermediate Gaussian formula. -/
lemma transformation_two (a b c d q z : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hpar : ∀ u ∈ [a, b, c, d, z], u ≠ 0)
    (hden : QDenominatorRegular [q / a, q / b, c, d] q)
    (hB : QBilateralRegular [a, b] [c, d] q ∧
      QBilateralRegular [a * b * z / c, a * b * z / d] [a * z, b * z] q)
    (hz : ‖c * d / (a * b)‖ < ‖z‖ ∧ ‖z‖ < 1) :
    qPsi [a, b] [c, d] q z =
      qProductRatioInf [a * z, b * z, c * q / (a * b * z), d * q / (a * b * z)]
        [q / a, q / b, c, d] q *
          qPsi [a * b * z / c, a * b * z / d] [a * z, b * z] q
            (c * d / (a * b * z)) := by
  have ha0 := hpar a (by simp)
  have hb0 := hpar b (by simp)
  have hc0 := hpar c (by simp)
  have hd0 := hpar d (by simp)
  have hz0 := hpar z (by simp)
  let w := fun t : ℂ => c * d / (a * b * t)
  have hw : ContinuousAt w z := continuousAt_const.div₀
    (continuousAt_const.fun_mul continuousAt_id) (mul_ne_zero (mul_ne_zero ha0 hb0) hz0)
  have hw1 : ‖w z‖ < 1 := by
    dsimp [w]
    rw [show c * d / (a * b * z) = (c * d / (a * b)) / z by field_simp,
      norm_div, div_lt_one (norm_pos_iff.mpr hz0)]
    exact hz.1
  have hleft := BilateralContinuity.continuousAt_qPsi_two hq0 hq continuousAt_const
    continuousAt_const continuousAt_const continuousAt_const continuousAt_id
    ha0 hb0 hc0 hd0 hz0 hB.1 hw1 hz.2
  have hC : ContinuousAt (fun t : ℂ => a * b * t / c) z := by fun_prop
  have hD : ContinuousAt (fun t : ℂ => a * b * t / d) z := by fun_prop
  have hAz : ContinuousAt (fun t : ℂ => a * t) z := by fun_prop
  have hBz : ContinuousAt (fun t : ℂ => b * t) z := by fun_prop
  have hC0 : a * b * z / c ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hz0) hc0
  have hD0 : a * b * z / d ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hz0) hd0
  have hW0 : w z ≠ 0 := div_ne_zero (mul_ne_zero hc0 hd0)
    (mul_ne_zero (mul_ne_zero ha0 hb0) hz0)
  have hinner : (a * z) * (b * z) / ((a * b * z / c) * (a * b * z / d) * w z) = z := by
    dsimp [w]
    field_simp
  have htrans := BilateralContinuity.continuousAt_qPsi_two hq0 hq hC hD hAz hBz hw
    hC0 hD0 (mul_ne_zero ha0 hz0) (mul_ne_zero hb0 hz0) hW0 hB.2
    (by simpa only [hinner] using hz.2) hw1
  have hInf : Continuous (fun u : ℂ => qPochhammerInf u q) :=
    (differentiable_qPochhammerInf_left hq).continuous
  have hCq : ContinuousAt (fun t : ℂ => c * q / (a * b * t)) z :=
    continuousAt_const.div₀ (continuousAt_const.fun_mul continuousAt_id)
      (mul_ne_zero (mul_ne_zero ha0 hb0) hz0)
  have hDq : ContinuousAt (fun t : ℂ => d * q / (a * b * t)) z :=
    continuousAt_const.div₀ (continuousAt_const.fun_mul continuousAt_id)
      (mul_ne_zero (mul_ne_zero ha0 hb0) hz0)
  have hpref : ContinuousAt (fun t =>
      qProductRatioInf [a * t, b * t, c * q / (a * b * t), d * q / (a * b * t)]
        [q / a, q / b, c, d] q) z := by
    simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    exact ((hInf.continuousAt.comp hAz).fun_mul
      ((hInf.continuousAt.comp hBz).fun_mul
      ((hInf.continuousAt.comp hCq).fun_mul (hInf.continuousAt.comp hDq)))).div_const _
  have hright := hpref.fun_mul htrans
  have hregB := BilateralContinuity.eventually_qBilateralRegular_two hq0 hq hC hD hAz hBz
    hC0 hD0 hB.2
  have hregMul := BilateralContinuity.eventually_regular_mul (a * b) q z hq
  have hregDiv := BilateralContinuity.eventually_regular_div
    (div_ne_zero (pow_ne_zero 2 hq0) (mul_ne_zero ha0 hb0)) hq0 hq hz0
  have hAvoid := FiniteBilateral.eventually_qPochhammer_mul_pow_ne_zero
    (a * b / q) q z 1 1 (by omega)
  have hEq : ∀ᶠ t in 𝓝[≠] z, qPsi [a, b] [c, d] q t =
      qProductRatioInf [a * t, b * t, c * q / (a * b * t), d * q / (a * b * t)]
        [q / a, q / b, c, d] q *
          qPsi [a * b * t / c, a * b * t / d] [a * t, b * t] q (w t) := by
    filter_upwards [nhdsWithin_le_nhds hregB, hregMul, hregDiv, hAvoid,
      nhdsWithin_le_nhds (continuousAt_id.eventually_ne hz0),
      nhdsWithin_le_nhds (hw.norm.eventually (Iio_mem_nhds hw1)),
      nhdsWithin_le_nhds (continuousAt_id.norm.eventually (Iio_mem_nhds hz.2))]
      with t hBt hMt hDt hAt ht0 hwt ht1
    have hcentral : QDenominatorRegular [a * b * t, q ^ 2 / (a * b * t), w t, t] q := by
      intro u hu j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu | hu | hu <;> rw [hu]
      · exact hMt j
      · simpa only [div_mul_eq_div_div] using hDt j
      · exact (sub_ne_zero.mp (one_sub_mul_pow_ne_zero_of_norm hwt hq j)).symm
      · exact (sub_ne_zero.mp (one_sub_mul_pow_ne_zero_of_norm ht1 hq j)).symm
    have hA1 : a * b * t / q ≠ 1 := by
      have hsub : 1 - a * b * t / q ≠ 0 := by
        simpa only [pow_one, qPochhammer_one,
          show a * b / q * t = a * b * t / q by ring] using hAt
      exact (sub_ne_zero.mp hsub).symm
    have hpart : ∀ u ∈ [a, b, c, d, t], u ≠ 0 := by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption
    exact transformation_two_of_central_regular a b c d q t hq hq0 hpart hden
      ⟨hB.1, hBt⟩ hwt ht1 hcentral hA1
  exact tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' (hEq.mono fun _ h => h.symm))

end DLMF.QHypergeometric.BilateralGaussianSymmetry
