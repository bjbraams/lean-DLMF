/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The trigonometric beta integral with complex exponents

Temme, *Special Functions* (1996), Chapter 3, (3.1)–(3.3), pp. 41–45,
synopsis TEM-03-01. Sine and cosine are positive inside the integration interval,
so their complex powers use the real logarithm of their positive values.
-/

@[expose] public noncomputable section
open Complex MeasureTheory
namespace DLMF.Gamma

/-- The beta sine/cosine integral with its full complex-parameter domain,
Temme Chapter 3, (3.1)–(3.3), synopsis TEM-03-01. -/
theorem intervalIntegrable_and_betaIntegral_eq_sin_cos {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    IntervalIntegrable (fun θ : ℝ => (Real.sin θ : ℂ) ^ (2 * a - 1) *
      (Real.cos θ : ℂ) ^ (2 * b - 1)) volume 0 (Real.pi / 2) ∧
      betaIntegral a b = 2 * ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
        (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (2 * b - 1) := by
  sorry

end DLMF.Gamma
