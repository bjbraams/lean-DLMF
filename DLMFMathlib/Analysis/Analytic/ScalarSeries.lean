/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Tactic

/-!
# Analytic scalar series from absolute convergence

`FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_summable_norm` proves analyticity
on the unit ball when the coefficient norms give an absolutely convergent series at every
real radius less than one. It uses Mathlib's scalar formal multilinear series and their
radius of convergence.
-/

open Filter
open scoped Topology NNReal ENNReal
namespace FormalMultilinearSeries
/-- Absolute convergence at every smaller radius gives an analytic scalar power series
on the open unit ball. -/
public theorem analyticOnNhd_tsum_mul_pow_of_summable_norm
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] (c : ℕ → K)
    (hc : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun n => ‖c n‖ * r ^ n)) :
    AnalyticOnNhd K (fun z : K => ∑' n : ℕ, c n * z ^ n) (Metric.ball 0 1) := by
  let p := FormalMultilinearSeries.ofScalars K c
  have hp : (1 : ℝ≥0∞) ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    apply p.le_radius_of_summable_norm
    have hsum := hc r r.coe_nonneg (by exact_mod_cast hr)
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using hsum
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzr : (‖z‖₊ : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by exact_mod_cast hz1) hp
  have hpos : 0 < p.radius := lt_of_lt_of_le zero_lt_one hp
  have H := (p.hasFPowerSeriesOnBall hpos).analyticOnNhd z
    (by simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hzr)
  convert H using 1
  funext w
  simp only [p, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul]
end FormalMultilinearSeries
