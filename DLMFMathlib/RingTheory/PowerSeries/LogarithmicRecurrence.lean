/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Coefficient recurrences for formal logarithms and reciprocals

Olver, *Asymptotics and Special Functions*, Chapter 1, §8, pp. 19–22,
synopsis O-1.13. The logarithm is Mathlib's canonical `PowerSeries.logOf`.
-/

@[expose] public noncomputable section

open Finset

namespace PowerSeries

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The coefficient recurrence obtained from `P (log P)' = P'`.
Olver, Chapter 1, §8, synopsis O-1.13. -/
theorem natCast_mul_coeff_logOf (P : K⟦X⟧) (hP : constantCoeff P = 1) (n : ℕ) :
    (n : K) * coeff n (logOf P) = (n : K) * coeff n P -
      ∑ j ∈ Icc 1 (n - 1), (j : K) * coeff j (logOf P) * coeff (n - j) P := by
  sorry

/-- The reciprocal recurrence, indexed by positive first-factor degree.
Olver, Chapter 1, §8, synopsis O-1.13; equivalent to Mathlib `coeff_inv`.
The nonzero constant coefficient is precisely the formal unit condition. -/
theorem coeff_inv_eq_sum_Icc (P : K⟦X⟧) (hP : constantCoeff P ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    coeff n P⁻¹ = -(constantCoeff P)⁻¹ *
      ∑ j ∈ Icc 1 n, coeff j P * coeff (n - j) P⁻¹ := by
  sorry

end PowerSeries
