/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential bounds for primitives on a half-line

An exponential bound with positive rate for a derivative gives an exponential
bound with the same rate for its primitive. One-sided derivatives at zero suffice.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Asymptotics

/-- An exponential bound for a continuous derivative on the nonnegative half-line
gives an explicit bound of the same positive exponential rate for the primitive. -/
theorem norm_le_mul_exp_of_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {q q' : ℝ → E} {α M : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hq : ContinuousOn q (Ici 0))
    (hq' : ContinuousOn q' (Ici 0))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt q (q' t) (Ici 0) t)
    (hb : ∀ t ≥ 0, ‖q' t‖ ≤ M * Real.exp (α * t)) {t : ℝ} (ht : 0 ≤ t) :
    ‖q t‖ ≤ (‖q 0‖ + M / α) * Real.exp (α * t) := by
  have hqi : IntervalIntegrable q' volume 0 t :=
    (hq'.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht
  have hFTC : (∫ u in (0 : ℝ)..t, q' u) = q t - q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht (hq.mono Icc_subset_Ici_self)
      (fun u hu => (hd u hu.1.le).hasDerivAt (Ici_mem_nhds hu.1)) hqi
  have hE : IntervalIntegrable (fun u : ℝ => M * Real.exp (α * u)) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he (u : ℝ) : HasDerivAt (fun v : ℝ => M / α * Real.exp (α * v))
      (M * Real.exp (α * u)) u := by
    convert (((hasDerivAt_id u).const_mul α).exp.const_mul (M / α)) using 1
    · funext v
      dsimp only [id_eq]
    · dsimp only [id_eq]
      field_simp [hα.ne']
  have hEI : (∫ u in (0 : ℝ)..t, M * Real.exp (α * u)) =
      M / α * (Real.exp (α * t) - 1) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u) hE]
    simp only [mul_zero, Real.exp_zero]
    ring
  have hnorm : ‖q t - q 0‖ ≤ M / α * (Real.exp (α * t) - 1) := by
    rw [← hFTC, ← hEI]
    exact (intervalIntegral.norm_integral_le_integral_norm ht).trans
      (intervalIntegral.integral_mono_on ht hqi.norm hE (fun u hu => hb u hu.1))
  have he1 : 1 ≤ Real.exp (α * t) := Real.one_le_exp (mul_nonneg hα.le ht)
  have htri : ‖q t‖ ≤ ‖q t - q 0‖ + ‖q 0‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q t - q 0) (q 0)
  nlinarith [mul_le_mul_of_nonneg_left he1 (norm_nonneg (q 0)), div_nonneg hM hα.le]

end Asymptotics
