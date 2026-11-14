/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A full-period affine trigonometric reciprocal integral

Olver, *Asymptotics and Special Functions*, Chapter 5, Lemma 14.1,
p. 184, synopsis O-5.25. The positive square root and the case `b=c=0`
are included; any starting angle gives the same full-period integral.
-/

@[expose] public noncomputable section

namespace Real

/-- The affine cosine/sine denominator stays positive and has the exact full-period
reciprocal integral. Olver, Chapter 5, Lemma 14.1, p. 184, synopsis O-5.25. -/
theorem integral_inv_affine_cos_sin {a b c : ℝ} (ha : sqrt (b ^ 2 + c ^ 2) < a)
    (θ₀ : ℝ) :
    (∀ θ : ℝ, 0 < a + b * cos θ + c * sin θ) ∧
    IntervalIntegrable (fun θ => (a + b * cos θ + c * sin θ)⁻¹)
      MeasureTheory.volume θ₀ (θ₀ + 2 * Real.pi) ∧
    (∫ θ : ℝ in θ₀..θ₀ + 2 * Real.pi, (a + b * cos θ + c * sin θ)⁻¹) =
      2 * Real.pi / sqrt (a ^ 2 - b ^ 2 - c ^ 2) := by
  sorry

end Real
