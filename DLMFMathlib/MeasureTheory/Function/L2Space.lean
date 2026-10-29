/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Squared norms of square-integrable representatives

The squared `L²` norm is the integral of the squared pointwise norm. This form
avoids the square roots and extended-real norms in the general `Lp` API.
-/

@[expose] public noncomputable section

open MeasureTheory

/-- The integral of the squared pointwise norm equals the squared norm of its
`L²` equivalence class. -/
theorem MeasureTheory.MemLp.integral_norm_sq_eq_norm_toLp_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α} {f : α → E}
    (hf : MemLp f 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]

/-- The squared norm of an `L²` element is the integral of its representative's
squared pointwise norm. -/
theorem MeasureTheory.Lp.integral_norm_sq_eq_norm_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α} (f : Lp E 2 μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  simpa using (Lp.memLp f).integral_norm_sq_eq_norm_toLp_sq
