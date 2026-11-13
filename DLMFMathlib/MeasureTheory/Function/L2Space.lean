/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Squared norms of square-integrable representatives

The squared `L²` norm is the integral of the squared pointwise norm. This form avoids the
square roots and extended-real norms in the general `Lp` API. TauCeti supplies
`MeasureTheory.Lp.integral_norm_sq_eq_norm_sq` and `MeasureTheory.MemLp.norm_toLp_sq`;
the representative adapter below preserves the integral-first orientation.

## Main results

* `MeasureTheory.MemLp.integral_norm_sq_eq_norm_toLp_sq`: the integral of the squared
  pointwise norm equals the squared norm of the `L²` class.
* `MeasureTheory.Lp.integral_norm_sq_eq_norm_sq`: the squared norm of an `L²` element is the
  integral of its representative's squared pointwise norm.
-/

public noncomputable section

open MeasureTheory

/-- The integral of the squared pointwise norm equals the squared norm of its
`L²` equivalence class. -/
theorem MeasureTheory.MemLp.integral_norm_sq_eq_norm_toLp_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α} {f : α → E}
    (hf : MemLp f 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := by
  exact hf.norm_toLp_sq.symm
