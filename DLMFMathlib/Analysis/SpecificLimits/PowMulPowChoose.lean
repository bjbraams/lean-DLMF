/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summability of `R^k r^(k choose 2)`

For `0 ≤ r < 1` and any `R ≥ 0` the series `∑ R^k r^(k(k-1)/2)` converges: the ratio of
consecutive terms is `R r^k → 0`. Such super-geometric series dominate theta-type series and
basic hypergeometric series with a quadratic phase factor.

## Main results

* `summable_pow_mul_pow_choose_two`: `∑ R^k r^(k choose 2)` converges for `0 ≤ R`, `0 ≤ r < 1`.
-/

@[expose] public section

open Filter

/-- `∑ R^k r^(k choose 2)` converges for `0 ≤ R` and `0 ≤ r < 1`. -/
theorem summable_pow_mul_pow_choose_two {R r : ℝ} (hR : 0 ≤ R) (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun k : ℕ => R ^ k * r ^ (k.choose 2) := by
  have hlim : Tendsto (fun k : ℕ => R * r ^ k) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).const_mul R
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  rw [show (k + 1).choose 2 = k.choose 2 + k by
    rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]]
  have h0 : 0 ≤ R ^ k * r ^ (k.choose 2) := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg h0]
  calc R ^ (k + 1) * r ^ (k.choose 2 + k) = (R * r ^ k) * (R ^ k * r ^ (k.choose 2)) := by ring
    _ ≤ 1 / 2 * (R ^ k * r ^ (k.choose 2)) := mul_le_mul_of_nonneg_right hk.le h0
