/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Bell
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exact saddle and sharp relative Bell-coefficient error

Olver, *Asymptotics and Special Functions*, Chapter 9, §3,
pp. 329–331, synopsis O-9.04. The exact saddle is used rather than a finite
inverse-logarithmic substitute. Bell numbers themselves are Mathlib's Nat.bell.
-/

@[expose] public noncomputable section
open Filter Asymptotics
open scoped Topology
namespace DLMF.Combinatorics.BellSaddle

/-- The positive exact saddle `N log N=n`. Olver, Chapter 9, §3, pp. 329–331. -/
def value (n : ℕ) : ℝ := (existsUnique_mul_log_eq (Nat.cast_nonneg n)).choose

/-- The saddle is at least one and solves its exact equation. -/
theorem value_spec (n : ℕ) : 1 ≤ value n ∧ value n * Real.log (value n) = n :=
  (existsUnique_mul_log_eq (Nat.cast_nonneg n)).choose_spec.1

/-- The actual coefficient of `exp(exp z)` in terms of the canonical Bell number.
Olver, Chapter 9, §3, pp. 329–331. -/
def coefficient (n : ℕ) : ℝ := Real.exp 1 * Nat.bell n / n.factorial

/-- The defining Bell normalization of the entire-function coefficient. -/
theorem coefficient_def (n : ℕ) :
    coefficient n = Real.exp 1 * Nat.bell n / n.factorial := rfl

/-- The sharp relative error is `O(1/N)`. Olver, Chapter 9, §3, pp. 329–331. -/
theorem isBigO_coefficient_div_main_sub_one :
    (fun n : ℕ => coefficient n /
      (Real.exp (value n) / (Real.sqrt (2 * Real.pi * (n + value n)) *
        Real.log (value n) ^ ((n : ℝ) + 1 / 2))) - 1) =O[atTop]
          (fun n : ℕ => (value n)⁻¹) := by
  sorry

/-- Even the first inverse-log saddle substitute destroys the leading relative
asymptotic. Olver, Chapter 9, §3, pp. 329–331. -/
theorem tendsto_first_log_substitute_main_div_main :
    Tendsto (fun n : ℕ =>
      (Real.exp ((n : ℝ) / Real.log n) /
        (Real.sqrt (2 * Real.pi * (n + (n : ℝ) / Real.log n)) *
          Real.log ((n : ℝ) / Real.log n) ^ ((n : ℝ) + 1 / 2))) /
      (Real.exp (value n) / (Real.sqrt (2 * Real.pi * (n + value n)) *
        Real.log (value n) ^ ((n : ℝ) + 1 / 2)))) atTop atTop := by
  sorry

end DLMF.Combinatorics.BellSaddle
