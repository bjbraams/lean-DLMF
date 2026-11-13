/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.MeasureTheory.VectorMeasure.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integration by parts for Lebesgue–Stieltjes measures

A right-continuous nondecreasing function has its Lebesgue–Stieltjes measure as its
distributional derivative. Integration by parts against compactly supported `C¹` functions
includes all jump atoms and requires no bound on the Stieltjes function at infinity.

The proof restricts to a finite interval containing the test support and uses TauCeti
`VectorMeasure.integral_deriv_smul_apply_Iic_eq_neg_integral` together with Mathlib
`VectorMeasure.integral_toSignedMeasure`.
-/

public section

open MeasureTheory Set

namespace StieltjesFunction

set_option maxHeartbeats 0

/-- Integration by parts when the test support lies in a fixed finite horizon. -/
private lemma integral_deriv_mul_eq_neg_of_tsupport_subset_Ioc (α : StieltjesFunction ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) {a b : ℝ}
    (hs : tsupport φ ⊆ Ioc a b) :
    ∫ x, deriv φ x * α x = -∫ x, φ x ∂α.measure := by
  let μ := α.measure.restrict (Ioc a b)
  have hfinite : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    rw [α.measure_Ioc]
    exact ENNReal.ofReal_ne_top
  let := hfinite
  have hvar : IsFiniteMeasure μ.toSignedMeasure.variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  let := hvar
  have hφd : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hdφ : Integrable (deriv φ) := hφd.integrable_of_hasCompactSupport hcφ.deriv
  have hzero : ∫ x, deriv φ x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun x => (hφ.differentiable one_ne_zero x).hasDerivAt) hdφ
      (hφ.continuous.integrable_of_hasCompactSupport hcφ)
  have hprod : Integrable (fun x => deriv φ x * α x) := by
    simpa only [smul_eq_mul] using α.mono.locallyIntegrable
      |>.integrable_smul_left_of_hasCompactSupport hφd hcφ.deriv
  have heq (x : ℝ) : deriv φ x * μ.toSignedMeasure (Iic x) =
      deriv φ x * α x - deriv φ x * α a := by
    by_cases hx : x ∈ tsupport φ
    · have hax := hs hx
      have hset : Iic x ∩ Ioc a b = Ioc a x := by
        ext y
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨hyx, hay, _⟩
          exact ⟨hay, hyx⟩
        · rintro ⟨hay, hyx⟩
          exact ⟨hyx, hay, hyx.trans hax.2⟩
      rw [Measure.toSignedMeasure_apply_measurable measurableSet_Iic]
      simp only [measureReal_def, μ, Measure.restrict_apply measurableSet_Iic, hset,
        α.measure_Ioc]
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (α.mono hax.1.le))]
      ring_nf
    · have hd0 : deriv φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (tsupport_deriv_subset h))
      rw [hd0]
      simp
  have hi := μ.toSignedMeasure.integral_deriv_smul_apply_Iic_eq_neg_integral hφ hcφ
  have hscalar : ContinuousLinearMap.lsmul ℝ ℝ = (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext
    simp
  rw [hscalar, MeasureTheory.VectorMeasure.integral_toSignedMeasure] at hi
  simp only [smul_eq_mul] at hi
  rw [integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_sub hprod (hdφ.mul_const _), integral_mul_const, hzero, zero_mul, sub_zero] at hi
  dsimp only [μ] at hi
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioc a b) (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)))] at hi
  exact hi

/-- Lebesgue–Stieltjes integration by parts for a compactly supported `C¹` test function. -/
lemma integral_mul_deriv_eq_neg (α : StieltjesFunction ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    ∫ x, α x * deriv φ x = -∫ x, φ x ∂α.measure := by
  obtain ⟨a, ha⟩ := hcφ.isCompact.bddBelow
  obtain ⟨b, hb⟩ := hcφ.isCompact.bddAbove
  have hs : tsupport φ ⊆ Ioc (a - 1) (b + 1) := by
    intro x hx
    exact ⟨by linarith [ha hx], by linarith [hb hx]⟩
  simpa only [mul_comm] using integral_deriv_mul_eq_neg_of_tsupport_subset_Ioc α hφ hcφ hs


end StieltjesFunction
