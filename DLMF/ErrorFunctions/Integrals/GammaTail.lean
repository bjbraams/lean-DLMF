/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic.Functions
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The shifted gamma-tail integral for the complementary error function

Temme, *Special Functions* (1996), Chapter 11, Exercise 11.1, pages 310–311.
This is the positive-real Laplace integral used to derive the signed error-function
asymptotic remainder.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace DLMF.Confluent

/-- The normalized shifted gamma-tail kernel is absolutely integrable.
Temme Exercise 11.1, synopsis TEM-11-21. -/
theorem Real.integrableOn_erfc_gammaTail_kernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => _root_.Real.exp (-t) *
      (1 + t / x ^ 2) ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  sorry

/-- The complementary error function as the source's shifted gamma-tail integral.
Temme Exercise 11.1, synopsis TEM-11-21. -/
theorem erfc_eq_gammaTail_integral {x : ℝ} (hx : 0 < x) :
    erfc x = _root_.Real.exp (-x ^ 2) / (_root_.Real.sqrt π * x) *
      ((∫ t in Ioi (0 : ℝ), _root_.Real.exp (-t) *
        (1 + t / x ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  sorry

end DLMF.Confluent
