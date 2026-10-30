/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.TrigR4SeriesExtension
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivative identities for scalar power-series operations

Mathlib's Cauchy–Taylor coefficients give the differentiated coefficient series near the
center. The principal complex power derivative is written as a first-order differential
identity, convenient for determining coefficients of powers by convolution.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace Complex

/-- Differentiate a scalar power series near its center by shifting its coefficients. -/
theorem eventually_hasSum_deriv_powerSeries {a : ℕ → ℂ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * z ^ n) (deriv f z) := by
  have hfa := hf.analyticAt
  have ha : a = fun n : ℕ => iteratedDeriv n f 0 / n.factorial :=
    FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
      (hf.eq_formalMultilinearSeries hfa.hasFPowerSeriesAt)
  have hs := hfa.deriv.hasFPowerSeriesAt.eventually_hasSum
  simp only [zero_add] at hs
  filter_upwards [hs] with z hz
  convert hz using 1
  ext n
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, ha,
    ← iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- Principal complex powers satisfy the first-order power differential identity on the slit plane. -/
theorem mul_deriv_cpow_const {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hz : f z ∈ slitPlane) (ν : ℂ) :
    f z * deriv (fun w => f w ^ ν) z = ν * (deriv f z * f z ^ ν) := by
  rw [(hf.hasDerivAt.cpow_const (c := ν) hz).deriv]
  have hpow : f z ^ (ν - 1) * f z = f z ^ ν := by
    calc
      _ = f z ^ (ν - 1) * f z ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = f z ^ ((ν - 1) + 1) := (Complex.cpow_add _ _ (Complex.slitPlane_ne_zero hz)).symm
      _ = _ := by congr 1; ring
  calc
    _ = ν * deriv f z * (f z ^ (ν - 1) * f z) := by ring
    _ = _ := by rw [hpow]; ring

end Complex
