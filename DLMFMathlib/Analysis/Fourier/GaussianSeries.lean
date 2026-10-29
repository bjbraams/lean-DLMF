/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.PSeries

/-!
# Absolute convergence of complex Gaussian series

Mathlib's Gaussian decay estimates imply summability on the integer lattice,
including arbitrary complex linear and constant terms.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics

/-- A complex quadratic exponential with negative real leading coefficient is
absolutely summable on the integers. -/
theorem Complex.summable_exp_quadratic {a : ℂ} (ha : a.re < 0) (b c : ℂ) :
    Summable (fun n : ℤ => cexp (a * n ^ 2 + b * n + c)) := by
  have h := (((cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ha b (-2)).isBigO).comp_tendsto
    Int.tendsto_coe_cofinite).const_mul_left (cexp c)
  simpa only [Function.comp_apply, ofReal_intCast, Complex.exp_add, mul_comm] using
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)) h
