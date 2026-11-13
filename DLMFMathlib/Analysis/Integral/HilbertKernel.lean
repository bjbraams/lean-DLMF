/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Symmetric truncations of the Hilbert kernel

Young's inequality gives absolute integrability of `f(t)/t` on `(ε,∞)` for every
finite `Lᵖ` exponent `p ≥ 1`. Translation and reflection then identify a symmetric
cutoff integral with a single half-line difference quotient.

## Main results

* `MeasureTheory.integrableOn_Ioi_div_of_memLp`: absolute integrability of the weighted tail.
* `MeasureTheory.integral_abs_sub_cut_eq_integral_Ioi`: the symmetric cutoff identity.
-/

public noncomputable section

open MeasureTheory Filter Set RCLike
open scoped Topology ENNReal

namespace MeasureTheory

variable {K : Type*} [RCLike K]

/-- An `Lᵖ` function divided by the coordinate is integrable away from the origin,
over `ℝ` or `ℂ`, for every finite exponent `p ≥ 1`. -/
lemma integrableOn_Ioi_div_of_memLp {f : ℝ → K} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hf : MemLp f p) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => f t / (t : K)) (Ioi ε) := by
  by_cases hp1 : p = 1
  · subst p
    have hi := memLp_one_iff_integrable.mp hf
    refine ((hi.norm.div_const ε).integrableOn).mono' ?_ ?_
    · simpa only [div_eq_mul_inv, Pi.mul_apply] using!
        hi.aestronglyMeasurable.restrict.mul
          (by fun_prop : Measurable (fun t : ℝ => (t : K)⁻¹)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_div, RCLike.norm_ofReal, abs_of_nonneg (hε.trans ht).le]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hε ht.le
  · have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
    have hpR : 1 < p.toReal := by
      simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal (by simp) hpt).mpr hpgt
    let q := Real.conjExponent p.toReal
    have hpq : p.toReal.HolderConjugate q := Real.HolderConjugate.conjExponent hpR
    have hq : 1 < q := hpq.symm.lt
    have hip := (hf.integrable_norm_rpow
      (by exact ne_of_gt (lt_of_lt_of_le (by simp) hp)) hpt).integrableOn (s := Ioi ε)
    have hiq : IntegrableOn (fun t : ℝ => t ^ (-q)) (Ioi ε) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hε
    refine ((hip.div_const p.toReal).add (hiq.div_const q)).mono' ?_ ?_
    · simpa only [div_eq_mul_inv, Pi.mul_apply] using!
        hf.aestronglyMeasurable.restrict.mul
          (by fun_prop : Measurable (fun t : ℝ => (t : K)⁻¹)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hε.trans ht
      rw [norm_div, RCLike.norm_ofReal, abs_of_nonneg ht0.le]
      have h := Real.young_inequality_of_nonneg (norm_nonneg (f t)) (inv_nonneg.mpr ht0.le) hpq
      simpa only [Pi.add_apply, div_eq_mul_inv, Real.inv_rpow ht0.le, Real.rpow_neg ht0.le] using h

/-- Pairing opposite sides of a symmetric cutoff gives a half-line difference quotient. -/
lemma integral_abs_sub_cut_eq_integral_Ioi {f : ℝ → K} {x ε : ℝ} (hε : 0 < ε)
    (hp : IntegrableOn (fun t : ℝ => f (x + t) / (t : K)) (Ioi ε))
    (hm : IntegrableOn (fun t : ℝ => f (x - t) / (t : K)) (Ioi ε)) :
    (∫ t : ℝ in {t : ℝ | ε < |t - x|}, f t / ((t : K) - x)) =
      ∫ t : ℝ in Ioi ε, (f (x + t) - f (x - t)) / (t : K) := by
  let H : ℝ → K := fun t => f (x + t) / (t : K)
  have hneg : IntegrableOn H (Iio (-ε)) := by
    have he : (fun t : ℝ => H (-t)) = fun t : ℝ => -(f (x - t) / (t : K)) := by
      funext t
      dsimp only [H]
      rw [ofReal_neg, div_neg, sub_eq_add_neg]
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (f := H) (s := Iio (-ε)) (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hs : Neg.neg ⁻¹' Iio (-ε) = Ioi ε := by ext t; simp
    simp only [Function.comp_def] at h
    rw [hs, he] at h
    exact h.mp (by simpa only [Pi.neg_def] using hm.neg)
  have htrans : (∫ t : ℝ in {t : ℝ | ε < |t - x|}, f t / ((t : K) - x)) =
      ∫ t : ℝ in {t : ℝ | ε < |t|}, H t := by
    rw [← integral_indicator (by measurability), ← integral_indicator (by measurability),
      ← integral_add_right_eq_self _ x]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      by_cases ht : ε < |t|
      · have ht' : ε < |t + x - x| := by simpa using ht
        rw [indicator_of_mem (show t + x ∈ {t : ℝ | ε < |t - x|} from ht'),
          indicator_of_mem (show t ∈ {t : ℝ | ε < |t|} from ht)]
        dsimp only [H]
        push_cast
        rw [add_sub_cancel_right, add_comm t x]
      · have ht' : ¬ε < |t + x - x| := by simpa using ht
        rw [indicator_of_notMem (show t + x ∉ {t : ℝ | ε < |t - x|} from ht'),
          indicator_of_notMem (show t ∉ {t : ℝ | ε < |t|} from ht)]
  have hs : {t : ℝ | ε < |t|} = Iio (-ε) ∪ Ioi ε := by
    ext t
    simp only [mem_ofPred_eq, lt_abs, mem_union, mem_Iio, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  rw [htrans, hs, setIntegral_union (by
    apply disjoint_left.mpr
    intro t ht ht'
    linarith [show t < -ε from ht, show ε < t from ht']) measurableSet_Ioi hneg hp]
  have hleft : (∫ t : ℝ in Iio (-ε), H t) =
      -(∫ t : ℝ in Ioi ε, f (x - t) / (t : K)) := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi ε H]
    have he : (fun t : ℝ => H (-t)) = fun t : ℝ => -(f (x - t) / (t : K)) := by
      funext t
      dsimp only [H]
      rw [ofReal_neg, div_neg, sub_eq_add_neg]
    rw [he, integral_neg]
  rw [hleft, neg_add_eq_sub, ← integral_sub hp hm]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [H]
  ring

end MeasureTheory
