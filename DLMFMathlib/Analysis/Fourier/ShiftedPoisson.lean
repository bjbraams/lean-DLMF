/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Fourier.PoissonBoundedVariation
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Shifted, twisted Poisson summation for integrable functions of bounded variation

Temme, *Special Functions* (1996), Theorem 12.2, pages 326–327, with midpoint
values at jumps and the absolute value of the spacing. The Fourier side is an
ordered symmetric limit; absolute convergence is asserted only on the sampling side.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace Real

/-- Full bounded-variation Poisson summation, with arbitrary translation, real twist
and nonzero signed spacing. No continuity or integrable monotone envelope is assumed.
Temme, Theorem 12.2, pp. 326–327, synopsis TEM-12-08; corrected midpoint convention
and absolute spacing as recorded in TEM-E07. -/
theorem tendsto_sum_Icc_twistedFourier_of_boundedVariationOn (f : ℝ → ℂ)
    (hf : Integrable f) (hbv : BoundedVariationOn f univ) (a x : ℝ)
    {b : ℝ} (hb : b ≠ 0) :
    Summable (fun n : ℤ => ‖(Function.leftLim f (x + n * b) +
      Function.rightLim f (x + n * b)) / 2‖) ∧
    Tendsto (fun M : ℕ => ((|b| : ℝ) : ℂ)⁻¹ *
      ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (∫ t : ℝ, f t * cexp (I * t * ((2 * π * m + a) / b))) *
          cexp (-I * x * ((2 * π * m + a) / b))) atTop
      (𝓝 (∑' n : ℤ, cexp (I * n * a) *
        ((Function.leftLim f (x + n * b) + Function.rightLim f (x + n * b)) / 2))) := by
  sorry

end Real
