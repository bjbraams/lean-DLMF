/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic
/-!
# The integral of a logarithmic derivative and a continuous phase

For an absolutely continuous nonvanishing complex curve, the imaginary part of its
logarithmic-derivative integral equals the change of any continuous phase. The phase itself
needs no differentiability hypothesis. Mathlib's uniqueness of lifts for the exponential
covering and TauCeti's endpoint-ratio formula for absolutely continuous curves identify the
two continuous logarithm lifts.

## Main results

* `Complex.integral_deriv_div_im_eq_phase_sub`: the change-of-phase formula, in either orientation.
-/

public noncomputable section
open Complex Set MeasureTheory
namespace Complex
/-- For a nonvanishing absolutely continuous curve, the imaginary part of the logarithmic
derivative integral is the change in any continuous phase. -/
lemma integral_deriv_div_im_eq_phase_sub
    {σ : ℝ → ℂ} {a b : ℝ} (hσ : AbsolutelyContinuousOnInterval σ a b)
    (hne : ∀ t ∈ uIcc a b, σ t ≠ 0) {θ : ℝ → ℝ}
    (hθ : ContinuousOn θ (uIcc a b))
    (hphase : ∀ t ∈ uIcc a b, σ t = (‖σ t‖ : ℂ) * exp ((θ t : ℂ) * I)) :
    (∫ t in a..b, deriv σ t / σ t).im = θ b - θ a := by
  let L : ℝ → ℂ := fun t => (Real.log ‖σ t‖ : ℂ) + (θ t : ℂ) * I
  have hL : ContinuousOn L (uIcc a b) := by
    apply ContinuousOn.add
    · exact continuous_ofReal.comp_continuousOn (hσ.continuousOn.norm.log
        (fun t ht => (norm_pos_iff.mpr (hne t ht)).ne'))
    · exact (continuous_ofReal.comp_continuousOn hθ).mul continuousOn_const
  have hexp (t : ℝ) (ht : t ∈ uIcc a b) : exp (L t) = σ t := by
    dsimp only [L]
    rw [exp_add, ← ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hne t ht))]
    exact (hphase t ht).symm
  have havoid : (0 : ℂ) ∉ σ '' uIcc a b := by
    rintro ⟨t, ht, he⟩
    exact hne t ht he
  have hi : IntervalIntegrable (fun t => deriv σ t / σ t) volume a b := by
    simpa only [sub_zero, div_eq_mul_inv, mul_comm] using
      hσ.intervalIntegrable_inv_sub_mul_deriv havoid
  let A : ℝ → ℂ := fun t => ∫ s in a..t, deriv σ s / σ s
  have hA : AbsolutelyContinuousOnInterval A a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc
  have hAexp (t : ℝ) (ht : t ∈ uIcc a b) : exp (A t) = σ t / σ a := by
    have hst : AbsolutelyContinuousOnInterval σ a t :=
      hσ.mono (uIcc_subset_uIcc left_mem_uIcc ht)
    have hz : (0 : ℂ) ∉ σ '' uIcc a t := by
      rintro ⟨s, hs, he⟩
      exact hne s (uIcc_subset_uIcc left_mem_uIcc ht hs) he
    have h := hst.exp_two_pi_I_mul_windingNumber hz
    rw [hst.windingNumber_eq_integral hz, ← mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul] at h
    simpa only [sub_zero, A, div_eq_mul_inv, mul_comm] using h
  have hE : EqOn (fun t => (⟨exp (L t), exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}))
      (fun t => (⟨exp (A t + L a), exp_ne_zero _⟩ : {z : ℂ // z ≠ 0})) (uIcc a b) := by
    intro t ht
    have hv : exp (L t) = exp (A t + L a) := by
      rw [hexp t ht, exp_add, hAexp t ht, hexp a left_mem_uIcc]
      exact (div_mul_cancel₀ _ (hne a left_mem_uIcc)).symm
    exact Subtype.ext hv
  have hEq : EqOn L (fun t => A t + L a) (uIcc a b) :=
    Complex.isCoveringMap_exp.eqOn_of_comp_eqOn isPreconnected_uIcc hL
      (hA.continuousOn.add continuousOn_const) hE left_mem_uIcc (by simp [A])
  have hb := congrArg Complex.im (hEq right_mem_uIcc)
  simp only [L, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
    zero_add] at hb
  dsimp only [A] at hb
  linarith
end Complex
