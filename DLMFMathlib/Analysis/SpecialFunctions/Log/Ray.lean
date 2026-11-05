/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithms along a complex ray

The principal logarithm along `t ↦ ta`, for `t > 0`, is `log t + log a`. Its product
with any nonnegative integral power is integrable at zero, and with a positive power
it tends to zero. These statements also hold for the totalized logarithm when `a = 0`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Complex

/-- Separating the real radial coordinate from a logarithmic monomial. -/
lemma log_mul_pow_ray {a : ℂ} (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    log ((t : ℂ) * a) * ((t : ℂ) * a) ^ n =
      ((Real.log t : ℂ) * (t : ℂ) ^ n) * a ^ n + log a * (t : ℂ) ^ n * a ^ n := by
  rw [log_ofReal_mul ht ha, mul_pow]
  ring

/-- A logarithmic monomial on a complex ray is integrable on the unit interval. -/
lemma intervalIntegrable_log_mul_pow_ray (a : ℂ) (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => log ((t : ℂ) * a) * ((t : ℂ) * a) ^ n)
      volume 0 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hlog : IntervalIntegrable (fun t : ℝ => (Real.log t : ℂ)) volume 0 1 :=
    ⟨ofRealCLM.integrable_comp intervalIntegral.intervalIntegrable_log'.1,
      ofRealCLM.integrable_comp intervalIntegral.intervalIntegrable_log'.2⟩
  have hpow : Continuous (fun t : ℝ => (t : ℂ) ^ n) := by fun_prop
  have h := ((hlog.mul_continuousOn hpow.continuousOn).mul_const (a ^ n)).add
    (((hpow.intervalIntegrable 0 1).const_mul (log a)).mul_const (a ^ n))
  apply h.congr_uIoo
  intro t ht
  exact (log_mul_pow_ray ha (by simpa using ht.1) n).symm

/-- A logarithmic monomial of positive degree tends to zero at the origin of a ray. -/
lemma tendsto_log_mul_pow_ray {n : ℕ} (hn : 0 < n) (a : ℂ) :
    Tendsto (fun t : ℝ => log ((t : ℂ) * a) * ((t : ℂ) * a) ^ n)
      (𝓝[>] 0) (𝓝 0) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hreal : Tendsto (fun t : ℝ => Real.log t * t ^ n) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := n) (by exact_mod_cast hn))
  have hfirst : Tendsto (fun t : ℝ => (Real.log t : ℂ) * (t : ℂ) ^ n)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_mul, ofReal_pow, ofReal_zero] using
      (continuous_ofReal.tendsto 0).comp hreal
  have hpow : Tendsto (fun t : ℝ => (t : ℂ) ^ n) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (t : ℂ) ^ n) := by fun_prop
    simpa only [ofReal_zero, zero_pow (Nat.ne_of_gt hn)] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := (hfirst.mul_const (a ^ n)).add
    ((hpow.const_mul (log a)).mul_const (a ^ n))
  simp only [zero_mul, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (log_mul_pow_ray ha ht n).symm

end Complex
