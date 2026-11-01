/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.PSeries

/-!
# Catalan's constant

This file defines Catalan's constant `G = ∑ (-1)^k/(2k+1)² = β(2)` (DLMF 25.11.40), which is not
in Mathlib, and proves that its series converges absolutely.

## Main definitions

* `catalanConstant`: Catalan's constant `G`.

## Main results

* `summable_one_div_odd_sq`: `∑ 1/(2k+1)²` converges.
* `hasSum_catalanConstant`: the series of `G` converges absolutely to `G`.

## Implementation notes

The values `∑ 1/(2k+1)² = π²/8` and `ψ'(1/4) = π² + 8G` are in `DLMF.Constants.Catalan`.
-/

@[expose] public section

noncomputable section

namespace DLMF.Constants

/-- **Catalan's constant** `G = ∑ (-1)^k/(2k+1)² = β(2)` (Duverney Remark 2.9). -/
@[dlmf 25.11.E40]
def catalanConstant : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * k + 1) ^ 2

/-- `∑ 1/(2k+1)²` converges. -/
theorem summable_one_div_odd_sq : Summable fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2 := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (h.comp_injective (add_left_injective 1))
  simp only [Function.comp]
  push_cast
  gcongr
  linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- The series of Catalan's constant converges absolutely. -/
theorem hasSum_catalanConstant :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1) ^ 2) catalanConstant := by
  refine (Summable.of_norm ?_).hasSum
  refine summable_one_div_odd_sq.congr fun k => ?_
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (by positivity)]

end DLMF.Constants
