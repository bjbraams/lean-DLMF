/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Borel–Laplace recovery of a convergent power series

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 3, Exercise 3.17,
equations (3.63)–(3.64): dividing power-series coefficients by factorials gives a
Laplace-integrable entire transform whose Laplace integral recovers the original sum.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set

namespace Complex

/-- Borel–Laplace recovery inside the convergence disk, including absolute integrability.
Duverney Chapter 3, Exercise 3.17, (3.63)–(3.64), synopsis DU-3.19. -/
theorem integral_exp_neg_mul_factorialSeries {a : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => a n * z ^ n) (f z))
    {z : ℂ} (hz : ‖z‖ < R) :
    IntegrableOn (fun t : ℝ => exp (-t) *
      ∑' n : ℕ, a n * (z * t) ^ n / n.factorial) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), exp (-t) *
        ∑' n : ℕ, a n * (z * t) ^ n / n.factorial) = f z := by
  sorry

end Complex
