/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Completeness from a nonvanishing exponentially decaying multiplier

Andrews, Askey and Roy, *Special Functions*, Theorem 6.5.2, pp. 307–308
(synopsis AAR-6.5.1–6.6.2). The multiplier may change sign or be complex;
it is not interpreted as a positive measure density. A bounded integration
interval makes the tail condition vacuous. At infinite endpoints the condition
is the precise exponential big-oh hypothesis of the source.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.MemLp

/-- Vanishing polynomial moments after multiplication by a nonzero exponentially decaying
`L²` function force an `L²` function to vanish. Andrews–Askey–Roy,
*Special Functions*, Theorem 6.5.2, pp. 307–308
(synopsis AAR-6.5.1–6.6.2). Arbitrary measurable subsets and complex multipliers
are permitted; the book's interval and real-multiplier form is a special case. -/
theorem ae_eq_zero_of_moments_mul_eq_zero_of_exponential_decay {S : Set ℝ}
    (hS : MeasurableSet S) {f p : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict S)) (hp : MemLp p 2 (volume.restrict S))
    (hpnonzero : ∀ᵐ x ∂volume.restrict S, p x ≠ 0)
    {c C R : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ S, R ≤ |x| → ‖p x‖ ≤ C * Real.exp (-c * |x|))
    (hmom : ∀ n : ℕ, ∫ x : ℝ in S, (x : ℂ) ^ n * f x * p x = 0) :
    f =ᵐ[volume.restrict S] 0 := by
  sorry

end MeasureTheory.MemLp
