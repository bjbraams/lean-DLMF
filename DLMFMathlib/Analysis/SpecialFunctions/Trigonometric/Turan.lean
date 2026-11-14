/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Turán's strict sine-transform positivity criterion

Andrews, Askey and Roy, *Special Functions*, Theorem 7.5.1,
pp. 383–385, synopsis AAR-7.4.1–7.6.4. The hypothesis is an actual
absolutely summable infinite half-integer sine series.
-/

@[expose] public noncomputable section

namespace Real

/-- A nonzero absolutely summable half-integer sine series that is nonnegative on the closed
half-period has a strictly positive integrated integer-frequency sine series inside it.
Andrews–Askey–Roy, Theorem 7.5.1, synopsis AAR-7.4.1–7.6.4. -/
theorem tsum_sin_div_pos_of_tsum_half_shift_sin_nonneg {a : ℕ → ℝ}
    (ha : Summable (fun n => |a n|)) (hne : ∃ n, a n ≠ 0)
    (hpositive : ∀ φ ∈ Set.Icc (0 : ℝ) Real.pi,
      0 ≤ ∑' n : ℕ, a n * sin (((n : ℝ) + 1 / 2) * φ))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    Summable (fun n : ℕ => a n * sin (((n : ℝ) + 1) * θ) / (n + 1)) ∧
      0 < ∑' n : ℕ, a n * sin (((n : ℝ) + 1) * θ) / (n + 1) := by
  sorry

end Real
