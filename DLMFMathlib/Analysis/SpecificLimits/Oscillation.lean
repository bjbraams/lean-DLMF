/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Limits incompatible with a nonconstant oscillating phase

Even and odd integer subsequences detect when multiplication by a periodic
complex phase prevents convergence to a nonzero limit.
-/

@[expose] public noncomputable section

open Filter Complex
open scoped Topology

/-- If a function and its product with the phase `exp(π i t)` both have limits at
positive infinity, the first limit is zero. Even and odd integer subsequences
force the two candidate limits to be equal and opposite. -/
theorem Complex.eq_zero_of_tendsto_mul_exp_pi_I {f : ℝ → ℂ} {A B : ℂ}
    (hA : Tendsto f atTop (𝓝 A))
    (hB : Tendsto (fun t : ℝ => f t * Complex.exp (Real.pi * I * t)) atTop (𝓝 B)) :
    A = 0 := by
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h21 : Tendsto (fun n : ℕ => (2 : ℝ) * n + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 h2
  have he (n : ℕ) : Complex.exp ((Real.pi : ℂ) * I * ((2 : ℝ) * n)) = 1 := by
    convert Complex.exp_nat_mul_two_pi_mul_I n using 1
    congr 1
    push_cast
    ring
  have ho (n : ℕ) : Complex.exp ((Real.pi : ℂ) * I * ((2 : ℝ) * n + 1)) = -1 := by
    push_cast
    rw [mul_add, mul_one, Complex.exp_add]
    have hn := he n
    push_cast at hn
    rw [hn, Complex.exp_pi_mul_I, one_mul]
  norm_num only [ofReal_ofNat, ofReal_natCast] at he ho
  have hBA : B = A := tendsto_nhds_unique (hB.comp h2)
    ((hA.comp h2).congr fun n => by dsimp only [Function.comp_def]; push_cast; rw [he, mul_one])
  have hBA' : B = -A := tendsto_nhds_unique (hB.comp h21)
    (((hA.comp h21).neg).congr fun n => by
      dsimp only [Function.comp_def]
      push_cast
      rw [ho, mul_neg_one])
  linear_combination (hBA' - hBA) / 2
