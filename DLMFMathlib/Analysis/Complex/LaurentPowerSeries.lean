/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Natural Laurent moments of a scalar power series

The Cauchy integral on a circle inside the domain of holomorphy recovers the coefficients
of any scalar power series representing the function near the center.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Real Topology NNReal ENNReal

namespace Complex

/-- A nonnegative Laurent moment equals the corresponding local power-series coefficient. -/
theorem circleIntegral_mul_zpow_neg_nat_eq {f : ℂ → ℂ} {a : ℕ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall c r))
    (ha : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ => a n * z ^ n) (f (c + z))) (n : ℕ) :
    (2 * π * I)⁻¹ * ∮ z in C(c, r), f z * (z - c) ^ (-(n : ℤ) - 1) = a n := by
  have hpa : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) c := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ha] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hz
  let R : ℝ≥0 := ⟨r, hr.le⟩
  have hpr : HasFPowerSeriesAt f (cauchyPowerSeries f c r) c :=
    (hf.hasFPowerSeriesOnBall (R := R) hr).hasFPowerSeriesAt
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1))
    (hpa.eq_formalMultilinearSeries hpr)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    cauchyPowerSeries_apply, one_div] at hh
  rw [hh]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  change f z * (z - c) ^ (-(n : ℤ) - 1) = (z - c)⁻¹ ^ n * ((z - c)⁻¹ * f z)
  rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, pow_succ]
  simp only [mul_inv_rev, inv_pow]
  ring

end Complex
