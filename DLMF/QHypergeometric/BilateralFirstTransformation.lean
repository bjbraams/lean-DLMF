/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BilateralGaussianTransposition
public import DLMF.QHypergeometric.BilateralZeroLowerContinuity

/-!
# Bailey's first two-psi-two transformation

DLMF 17.10.1 follows from a Gaussian parameter transposition for nonzero lower
parameters. Continuity of the two bilateral tails extends it to a zero lower parameter.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralFirstTransformation

/-- Bailey's first two-psi-two transformation, including a zero first lower parameter. -/
lemma transformation_one (a b c d q z : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hpar : ∀ u ∈ [a, b, d, z], u ≠ 0)
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
  have hd0 := hpar d (by simp)
  have hz0 := hpar z (by simp)
  by_cases hc0 : c = 0
  · subst c
    have hE0 : a * b * z / d ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hz0) hd0
    have hda0 : d / a ≠ 0 := div_ne_zero hd0 ha0
    have hleft := BilateralZeroLowerContinuity.continuousAt_qPsi_lower_zero hq0 hq
      ha0 hb0 hz0 hz.2 (fun j => hB.1.1 d (by simp) j) hB.1.2
    have htemp := BilateralZeroLowerContinuity.continuousAt_qPsi_lower_zero hq0 hq
      ha0 hE0 hda0 hd.2 (fun j => hB.2.1 (a * z) (by simp) j) hB.2.2
    have htrans : ContinuousAt
        (fun t : ℂ => qPsi [a, a * b * z / d] [a * z, t] q (d / a)) 0 := by
      apply ContinuousAt.congr htemp
      exact Eventually.of_forall fun t => FiniteBilateral.qPsi_perm
        (List.Perm.refl [a, a * b * z / d]) (List.Perm.swap (a * z) t []) q (d / a)
    have hInf : Continuous (fun u : ℂ => qPochhammerInf u q) :=
      (differentiable_qPochhammerInf_left hq).continuous
    have hCB : ContinuousAt (fun t : ℂ => t / b) 0 := by fun_prop
    have hW : ContinuousAt (fun t : ℂ => t * d / (a * b * z)) 0 := by fun_prop
    have hDen := FiniteBilateral.qPochhammerListInf_ne_zero hq hden
    have hpref : ContinuousAt (fun t : ℂ =>
        qProductRatioInf [a * z, d / a, t / b, d * q / (a * b * z)]
          [z, d, q / b, t * d / (a * b * z)] q) 0 := by
      simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      apply ContinuousAt.div₀
      · exact continuousAt_const.fun_mul (continuousAt_const.fun_mul
          ((hInf.continuousAt.comp hCB).fun_mul continuousAt_const))
      · exact continuousAt_const.fun_mul (continuousAt_const.fun_mul
          (continuousAt_const.fun_mul (hInf.continuousAt.comp hW)))
      · simpa only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, zero_mul, zero_div] using hDen
    have hright := hpref.fun_mul htrans
    have hRegC := BilateralContinuity.eventually_qDenominatorRegular hq
      continuousAt_id continuousAt_const hB.1.1
    have hRegT := BilateralContinuity.eventually_qDenominatorRegular hq
      continuousAt_const continuousAt_id hB.2.1
    have hSmall : ContinuousAt (fun t : ℂ => ‖t * d / (a * b)‖) 0 := by fun_prop
    have hNz : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 :=
      le_cofinite_iff_eventually_ne.mp (nhdsNE_le_cofinite 0) 0
    have hEq : ∀ᶠ t in 𝓝[≠] (0 : ℂ), qPsi [a, b] [t, d] q z =
        qProductRatioInf [a * z, d / a, t / b, d * q / (a * b * z)]
          [z, d, q / b, t * d / (a * b * z)] q *
            qPsi [a, a * b * z / d] [a * z, t] q (d / a) := by
      filter_upwards [nhdsWithin_le_nhds hRegC, nhdsWithin_le_nhds hRegT, hNz,
        nhdsWithin_le_nhds (hSmall.eventually (Iio_mem_nhds
          (by simpa only [zero_mul, zero_div, norm_zero] using norm_pos_iff.mpr hz0))),
        nhdsWithin_le_nhds (hSmall.eventually (Iio_mem_nhds
          (by simpa only [zero_mul, zero_div, norm_zero] using norm_pos_iff.mpr hda0)))]
        with t hCt hTt ht0 hzt hdt
      have hwt : ‖t * d / (a * b * z)‖ < 1 := by
        rw [show t * d / (a * b * z) = (t * d / (a * b)) / z by field_simp,
          norm_div, div_lt_one (norm_pos_iff.mpr hz0)]
        exact hzt
      have hpart : ∀ u ∈ [a, b, t, d, z], u ≠ 0 := by
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hdent : QDenominatorRegular [z, d, q / b, t * d / (a * b * z)] q := by
        intro u hu j
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hu | hu | hu | hu <;> rw [hu]
        · exact hden _ (by simp) j
        · exact hden _ (by simp) j
        · exact hden _ (by simp) j
        · exact BilateralGaussianTransposition.mul_pow_ne_one_of_norm_lt_one hwt hq j
      exact BilateralGaussianTransposition.transformation_one_nonzero_lower
        a b t d q z hq hq0 hpart hdent ⟨⟨hCt, hB.1.2⟩, ⟨hTt, hB.2.2⟩⟩
        ⟨hzt, hz.2⟩ ⟨hdt, hd.2⟩
    exact tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
      ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' (hEq.mono fun _ h => h.symm))
  · apply BilateralGaussianTransposition.transformation_one_nonzero_lower a b c d q z
      hq hq0 ?_ hden hB hz hd
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption

end DLMF.QHypergeometric.BilateralFirstTransformation
