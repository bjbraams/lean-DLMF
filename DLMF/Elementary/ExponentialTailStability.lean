/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Basic.LogExp
public import DLMF.IncompleteGamma.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential tails and stability of subtraction recurrences

Temme, *Special Functions* (1996), §13.1, pp. 334–335. The exact tails
and finite backward sums make absolute and relative errors explicit.
-/

@[expose] public noncomputable section
open Filter Finset
open scoped Topology
namespace DLMF.Elementary.Real

/-- The exponential series tail after degree `n`, for a real argument.
Temme §13.1, synopsis TEM-13-01. -/
def exponentialTail (n : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (n + k + 1) / (n + k + 1).factorial

/-- The defining absolutely convergent exponential tail, Temme §13.1,
synopsis TEM-13-01. -/
theorem exponentialTail_def (n : ℕ) (x : ℝ) :
    exponentialTail n x = ∑' k : ℕ, x ^ (n + k + 1) / (n + k + 1).factorial := rfl

/-- Exponential tails are summable at every real argument, Temme §13.1,
synopsis TEM-13-01. -/
theorem summable_exponentialTail (n : ℕ) (x : ℝ) :
    Summable (fun k : ℕ => x ^ (n + k + 1) / (n + k + 1).factorial) := by
  sorry

/-- The tail and finite partial sum partition the exponential, Temme §13.1,
synopsis TEM-13-01. -/
theorem exponentialTail_add_partialSum (n : ℕ) (x : ℝ) :
    exponentialTail n x + ∑ k ∈ range (n + 1), x ^ k / k.factorial = _root_.Real.exp x := by
  sorry

/-- Subtraction propagates the exponential tail, Temme §13.1, synopsis TEM-13-01. -/
theorem exponentialTail_succ (n : ℕ) (x : ℝ) :
    exponentialTail (n + 1) x = exponentialTail n x - x ^ (n + 1) / (n + 1).factorial := by
  sorry

/-- The homogeneous second-order stability model, Temme §13.1, synopsis TEM-13-01. -/
theorem exponentialTail_recurrence (n : ℕ) (x : ℝ) :
    (n + 2) * exponentialTail (n + 2) x - (x + n + 2) * exponentialTail (n + 1) x +
      x * exponentialTail n x = 0 := by
  sorry

/-- Exponential tails decay to zero, Temme §13.1, synopsis TEM-13-01. -/
theorem tendsto_exponentialTail (x : ℝ) :
    Tendsto (fun n => exponentialTail n x) atTop (𝓝 0) := by
  sorry

/-- The incomplete-gamma interpretation of the stability model, Temme §13.1,
synopsis TEM-13-01. -/
theorem exponentialTail_eq_regularizedGamma (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (exponentialTail n x : ℂ) = Complex.exp x * DLMF.Confluent.regularizedGamma (n + 1) x := by
  sorry

/-- An initial error in subtraction remains constant in absolute size,
Temme §13.1, synopsis TEM-13-01. -/
theorem sub_exponentialTail_eq_initial_error {x ε : ℝ} (y : ℕ → ℝ)
    (hzero : y 0 = exponentialTail 0 x + ε)
    (hstep : ∀ n, y (n + 1) = y n - x ^ (n + 1) / (n + 1).factorial) :
    ∀ n, y n - exponentialTail n x = ε := by
  intro n
  induction n with
  | zero => rw [hzero]; ring
  | succ n ih => rw [hstep, exponentialTail_succ]; linarith

/-- A fixed nonzero absolute contamination has unbounded relative error,
Temme §13.1, synopsis TEM-13-01. -/
theorem tendsto_abs_error_div_exponentialTail {x ε : ℝ} (hx : 0 < x) (hε : ε ≠ 0) :
    Tendsto (fun n => |ε| / exponentialTail n x) atTop atTop := by
  sorry

/-- A zero terminal value propagated backwards has exactly the omitted tail as error,
Temme §13.1, synopsis TEM-13-01. -/
theorem exponentialTail_sub_backward_sum {n M : ℕ} (h : n ≤ M) (x : ℝ) :
    exponentialTail n x - ∑ k ∈ Icc (n + 1) M, x ^ k / k.factorial =
      exponentialTail M x := by
  sorry

end DLMF.Elementary.Real
