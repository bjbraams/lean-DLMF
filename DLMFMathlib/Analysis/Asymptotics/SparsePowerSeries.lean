/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic
/-!
# Remainder bounds for sparse power series

`Asymptotics.isBigO_tsum_nat_pow_sub_sum` bounds a sparse power-series tail by any
power below its remaining exponents. A geometric majorant gives a uniform estimate
in a neighborhood of zero, without requiring a reindexing of the coefficients.
-/

open Filter Finset
open scoped Topology
namespace Asymptotics
/-- A power series with exponents at least their indices converges in the open unit ball. -/
public theorem summable_nat_pow_of_le_exponent {K : Type*} [NormedField K] [CompleteSpace K]
    {z : K} (hz : ‖z‖ < 1) (e : ℕ → ℕ) (he : ∀ n, n ≤ e n) :
    Summable (fun n : ℕ => z ^ e n) :=
  (summable_geometric_of_lt_one (norm_nonneg z) hz).of_norm_bounded fun n => by
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg z) hz.le (he n)

/-- A sparse power-series tail has the order of any lower bound on its remaining exponents. -/
public theorem isBigO_tsum_nat_pow_sub_sum {K : Type*} [NormedField K] [CompleteSpace K]
    (e : ℕ → ℕ) (M N : ℕ) (he : ∀ n, N + n ≤ e (n + M)) :
    (fun z : K => (∑' n : ℕ, z ^ e n) - ∑ n ∈ range M, z ^ e n) =O[𝓝 0]
      fun z => z ^ N := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : K) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  have hz2 : ‖z‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hz1 : ‖z‖ < 1 := by linarith
  have hmaj : Summable (fun n : ℕ => ‖z‖ ^ N * ‖z‖ ^ n) :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz1).mul_left _
  have hb (n : ℕ) : ‖z ^ e (n + M)‖ ≤ ‖z‖ ^ N * ‖z‖ ^ n := by
    rw [norm_pow, ← pow_add]
    exact pow_le_pow_of_le_one (norm_nonneg z) hz1.le (he n)
  have htail : Summable (fun n : ℕ => z ^ e (n + M)) := hmaj.of_norm_bounded hb
  have habs : Summable (fun n : ℕ => ‖z ^ e (n + M)‖) :=
    hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hf : Summable (fun n : ℕ => z ^ e n) := (summable_nat_add_iff M).mp htail
  rw [← hf.sum_add_tsum_nat_add M, add_sub_cancel_left, norm_pow]
  calc
    _ ≤ ∑' n : ℕ, ‖z ^ e (n + M)‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' n : ℕ, ‖z‖ ^ N * ‖z‖ ^ n := habs.tsum_le_tsum hb hmaj
    _ = ‖z‖ ^ N / (1 - ‖z‖) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg z) hz1]
      rfl
    _ ≤ 2 * ‖z‖ ^ N := (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ‖z‖)).mpr (by
      nlinarith [pow_nonneg (norm_nonneg z) N])
/-- A sparse power series with constant term one and increasing remaining exponents tends to
one at zero. -/
public theorem tendsto_tsum_nat_pow_zero {K : Type*} [NormedField K] [CompleteSpace K]
    (e : ℕ → ℕ) (he0 : e 0 = 0) (he : ∀ n, 1 + n ≤ e (n + 1)) :
    Tendsto (fun z : K => ∑' n : ℕ, z ^ e n) (𝓝 0) (𝓝 1) := by
  have H := (isBigO_tsum_nat_pow_sub_sum (K := K) e 1 1 he).trans_tendsto
    (by simpa using (continuous_pow 1).tendsto (0 : K))
  simpa [he0, Finset.sum_range_one] using H.add_const 1

end Asymptotics
