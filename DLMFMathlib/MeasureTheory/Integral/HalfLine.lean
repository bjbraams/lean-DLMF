/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Reflection and integration on the positive half-line

Splitting the real line into its two halves identifies the integral of a function
with the positive-half integral of its reflected sum. Even extension also preserves
membership in every `Lᵖ` space, by writing it as two reflected indicators.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ENNReal

namespace MeasureTheory

/-- Splitting an integrable function into its positive and reflected negative halves. -/
theorem integral_eq_integral_Ioi_add_neg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) :
    (∫ t, f t) = ∫ t in Ioi (0 : ℝ), f t + f (-t) := by
  have hn : Integrable (fun t => f (-t)) :=
    (volume.measurePreserving_neg).integrable_comp_of_integrable hf
  rw [integral_add hf.integrableOn hn.integrableOn, integral_comp_neg_Ioi, neg_zero,
    add_comm, intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn]

/-- Even extension from the positive half-line preserves `Lᵖ` membership. The value
at zero is irrelevant for Lebesgue measure. -/
theorem MemLp.comp_abs {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {f : ℝ → E}
    (hf : MemLp f p (volume.restrict (Ioi 0))) : MemLp (fun t : ℝ => f |t|) p := by
  have hg : MemLp ((Ioi (0 : ℝ)).indicator f) p :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hf
  have hn := hg.comp_measurePreserving (volume.measurePreserving_neg)
  apply (memLp_congr_ae (g := fun t => (Ioi (0 : ℝ)).indicator f t +
    (Ioi (0 : ℝ)).indicator f (-t)) ?_).mpr (hg.add hn)
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  rcases lt_or_gt_of_ne ht with ht | ht
  · simp [abs_of_neg ht, ht.not_gt, neg_pos.mpr ht]
  · simp [abs_of_pos ht, ht, not_lt.mpr (neg_nonpos.mpr ht.le)]

/-- The integral of an even extension is twice its positive-half integral, also
for totalized Bochner integrals when the integrability condition fails. -/
theorem integral_comp_abs_eq_two_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) :
    (∫ t : ℝ, f |t|) = (2 : ℝ) • ∫ t in Ioi (0 : ℝ), f t := by
  have he : (∫ t in Ioi (0 : ℝ), f |t|) = ∫ t in Ioi (0 : ℝ), f t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [abs_of_pos ht]
  by_cases hf : IntegrableOn f (Ioi 0)
  · have hfull : Integrable (fun t : ℝ => f |t|) :=
      memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hf).comp_abs)
    rw [integral_eq_integral_Ioi_add_neg hfull]
    simp_rw [abs_neg]
    rw [integral_add hfull.integrableOn hfull.integrableOn, he, two_smul ℝ]
  · have hfull : ¬Integrable (fun t : ℝ => f |t|) := by
      intro h
      apply hf
      exact h.integrableOn.congr_fun (fun t ht => by dsimp only; rw [abs_of_pos ht])
        measurableSet_Ioi
    rw [integral_undef hfull, integral_undef hf, smul_zero]

end MeasureTheory
