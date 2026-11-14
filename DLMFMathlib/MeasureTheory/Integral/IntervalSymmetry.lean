/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!
# Reflection symmetry of interval integrals

Reflection about the midpoint of an interval identifies the two half integrals.

## Main results

* `intervalIntegral.integral_eq_two_smul_of_reflection`: the full integral is twice the
  integral over the first half, for real normed target spaces. The identity also holds
  when the integrals are totalized, without an integrability assumption.

## Implementation notes

The proof reuses Mathlib's change of variables `intervalIntegral.integral_comp_sub_left`
and the corresponding transformation of interval integrability.
-/

open MeasureTheory Set
namespace intervalIntegral
/-- Reflection symmetry doubles the integral over a half interval, including totalized integrals. -/
public theorem integral_eq_two_smul_of_reflection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t, f (2 * T - t) = f t) :
    ∫ t in (0 : ℝ)..(2 * T), f t = (2 : ℝ) • ∫ t in (0 : ℝ)..T, f t := by
  by_cases hi : IntervalIntegrable f volume 0 T
  · have hr : IntervalIntegrable f volume T (2 * T) := by
      have h := (hi.comp_sub_left (2 * T)).congr (fun t _ => hf t)
      have he : 2 * T - T = T := by ring
      simpa only [sub_zero, he] using h.symm
    have heq : ∫ t in T..(2 * T), f t = ∫ t in (0 : ℝ)..T, f t := by
      have h := integral_comp_sub_left (a := (0 : ℝ)) (b := T) f (2 * T)
      rw [show 2 * T - T = T by ring, sub_zero] at h
      rw [← h]
      exact integral_congr (fun t _ => hf t)
    rw [← integral_add_adjacent_intervals hi hr, heq, two_smul ℝ]
  · have hfull : ¬ IntervalIntegrable f volume 0 (2 * T) := by
      intro h
      apply hi
      apply h.mono_set
      rw [uIcc_of_le hT, uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * T)]
      exact Icc_subset_Icc le_rfl (by linarith)
    rw [integral_undef hi, integral_undef hfull, smul_zero]
end intervalIntegral
