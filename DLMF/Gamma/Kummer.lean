/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Integrals.Log

/-!
# Kummer's Fourier expansion of `log Γ` (AAR §1.7)

The cosine coefficients of `log Γ` on `(0,1)` are determined by Euler's reflection formula
together with the Fourier series of `log(sin π x)`. The even part of `log Γ` on a symmetric
subinterval of `(0,1)` is identified below, and `∫_0^1 log(sin π x) dx = -log 2` is recorded
from Mathlib's `integral_log_sin_zero_pi`.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Real

open scoped Real Interval

noncomputable section

namespace Real

/-- `log Γ` is interval integrable between any two positive reals. -/
theorem intervalIntegrable_log_Gamma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => log (Gamma x)) volume a b := by
  have hmin : 0 < min a b := lt_min ha hb
  have hcont : ContinuousOn (fun x : ℝ => log (Gamma x)) (uIcc a b) :=
    fun x hx => (hasDerivAt_log_Gamma (hmin.trans_le hx.1)).continuousAt.continuousWithinAt
  exact hcont.intervalIntegrable

/-- Logarithmic reflection formula: `log Γ(x) + log Γ(1 - x) = log π - log sin(π x)` for `0 < x <
1`. -/
theorem log_Gamma_add_log_Gamma_one_sub {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    log (Gamma x) + log (Gamma (1 - x)) = log π - log (sin (π * x)) := by
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have hsin : 0 < sin (π * x) :=
    sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hx0)
      ((mul_lt_iff_lt_one_right pi_pos).2 hx1)
  have hmul := Gamma_mul_Gamma_one_sub x
  have : log (Gamma x * Gamma (1 - x)) = log (π / sin (π * x)) := by rw [hmul]
  rw [log_mul (Gamma_pos_of_pos hx0).ne' (Gamma_pos_of_pos h1x).ne',
    log_div pi_pos.ne' hsin.ne'] at this
  linarith

/-- Reflection identifies the even part of `log Γ` on a symmetric subinterval of `(0,1)`. -/
theorem two_mul_integral_log_Gamma {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    2 * ∫ x in ε..(1 - ε), log (Gamma x) =
      ∫ x in ε..(1 - ε), (log π - log (sin (π * x))) := by
  have hεle : ε ≤ 1 - ε := by linarith
  have hb : 0 < 1 - ε := by linarith
  have hintG : IntervalIntegrable (fun x : ℝ => log (Gamma x)) volume ε (1 - ε) :=
    intervalIntegrable_log_Gamma hε0 hb
  have hintG' : IntervalIntegrable (fun x : ℝ => log (Gamma (1 - x))) volume ε (1 - ε) := by
    simpa [sub_sub_cancel] using (hintG.comp_sub_left (c := 1)).symm
  have hadd := integral_add hintG hintG'
  have hsub : ∫ x in ε..(1 - ε), log (Gamma (1 - x)) =
      ∫ x in ε..(1 - ε), log (Gamma x) := by
    simpa [sub_sub_cancel] using
      integral_comp_sub_left (fun x : ℝ => log (Gamma x)) (1 : ℝ) (a := ε) (b := 1 - ε)
  have hcong : ∫ x in ε..(1 - ε), (log (Gamma x) + log (Gamma (1 - x))) =
      ∫ x in ε..(1 - ε), (log π - log (sin (π * x))) :=
    integral_congr fun x hx => by
      rw [uIcc_of_le hεle] at hx
      exact log_Gamma_add_log_Gamma_one_sub (hε0.trans_le hx.1)
        (lt_of_le_of_lt hx.2 (by linarith))
  rw [← hcong, hadd, hsub]
  ring

/-- `∫_0^1 log(sin π x) dx = -log 2`, used in Kummer's evaluation of the constant term. -/
theorem integral_log_sin_pi_zero_one :
    ∫ x in (0 : ℝ)..1, log (sin (π * x)) = -log 2 := by
  have hc : (π : ℝ) ≠ 0 := pi_ne_zero
  have h := intervalIntegral.integral_comp_mul_left (f := fun t : ℝ => log (sin t)) (c := π)
    (hc := hc) (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at h
  rw [h, integral_log_sin_zero_pi]
  simp [smul_eq_mul]
  field [hc]

end Real
