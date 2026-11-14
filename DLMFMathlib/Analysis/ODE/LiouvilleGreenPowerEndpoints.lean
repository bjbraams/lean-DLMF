/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Differentiated power conditions for finite Liouville–Green error variation

Olver, *Asymptotics and Special Functions*, Chapter 6, §4.1–4.2,
(4.01)–(4.06), pp. 200–201, synopsis O-6.06. The source's statement that
an asymptotic relation can be differentiated twice means control of the first
two derivatives, not merely twice differentiability of its left side.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace LiouvilleGreen

/-- Sufficient differentiated-power conditions at a finite singular endpoint, with a
quantitative local density and tail bound. Olver, Chapter 6, §4.1, (4.01)–(4.05),
pp. 200–201, synopsis O-6.06. The coordinate is distance `t>0` from the endpoint. -/
theorem integrable_errorDensity_of_power_at_zero {f : ℝ → ℝ} {g : ℝ → ℂ}
    {α β c b : ℝ} (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) (hb : 0 < b)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 b)) (hpos : ∀ t ∈ Ioo 0 b, 0 < f t)
    (hg : ContinuousOn g (Ioo 0 b))
    (hfeq : IsEquivalent (𝓝[>] (0 : ℝ)) f (fun t => c * t ^ (-2 * α - 2)))
    (hf' : IsBigO (𝓝[>] (0 : ℝ)) (deriv f) (fun t => t ^ (-2 * α - 3)))
    (hf'' : IsBigO (𝓝[>] (0 : ℝ)) (iteratedDeriv 2 f) (fun t => t ^ (-2 * α - 4)))
    (hgb : IsBigO (𝓝[>] (0 : ℝ)) g (fun t => t ^ (-α - 2 + β))) :
    let D := fun t : ℝ =>
      ((f t ^ (-(1 / 4 : ℝ)) *
        iteratedDeriv 2 (fun s => f s ^ (-(1 / 4 : ℝ))) t : ℝ) : ℂ) -
          g t * (f t ^ (-(1 / 2 : ℝ)) : ℝ)
    (∃ δ : ℝ, 0 < δ ∧ δ ≤ b ∧ IntegrableOn D (Ioo 0 δ)) ∧
      IsBigO (𝓝[>] (0 : ℝ)) D (fun t => t ^ (min α β - 1)) ∧
      IsBigO (𝓝[>] (0 : ℝ)) (fun t => ∫ s : ℝ in Ioo 0 t, ‖D s‖)
        (fun t => t ^ min α β) := by
  sorry

/-- Sufficient differentiated-power conditions at infinity, with an explicit integrable
power majorant and tail order. Olver, Chapter 6, §4.2, (4.06), p. 201,
synopsis O-6.06. -/
theorem integrable_errorDensity_of_power_atTop {f : ℝ → ℝ} {g : ℝ → ℂ}
    {α β c b : ℝ} (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c)
    (hf : ContDiffOn ℝ 2 f (Ioi b)) (hpos : ∀ t ∈ Ioi b, 0 < f t)
    (hg : ContinuousOn g (Ioi b))
    (hfeq : IsEquivalent atTop f (fun t => c * t ^ (2 * α - 2)))
    (hf' : IsBigO atTop (deriv f) (fun t => t ^ (2 * α - 3)))
    (hf'' : IsBigO atTop (iteratedDeriv 2 f) (fun t => t ^ (2 * α - 4)))
    (hgb : IsBigO atTop g (fun t => t ^ (α - 2 - β))) :
    let D := fun t : ℝ =>
      ((f t ^ (-(1 / 4 : ℝ)) *
        iteratedDeriv 2 (fun s => f s ^ (-(1 / 4 : ℝ))) t : ℝ) : ℂ) -
          g t * (f t ^ (-(1 / 2 : ℝ)) : ℝ)
    (∃ R : ℝ, b ≤ R ∧ IntegrableOn D (Ioi R)) ∧
      IsBigO atTop D (fun t => t ^ (-min α β - 1)) ∧
      IsBigO atTop (fun t => ∫ s : ℝ in Ioi t, ‖D s‖)
        (fun t => t ^ (-min α β)) := by
  sorry

/-- The inverse-square split cancels the nonintegrable error term exactly. This is the
`-1/4` correction that reproduces the two distinct Frobenius exponents; either the
exponential or oscillatory sign uses the same positive `c`.
Olver, Chapter 6, §4.3, pp. 201–202, synopsis O-6.06. -/
theorem integrable_errorDensity_inverseSquare_split {r : ℝ → ℂ} {c b : ℝ}
    (hc : 0 < c) (hb : 0 < b) (hr : ContinuousOn r (Ioo 0 b))
    (hrb : r =O[𝓝[>] (0 : ℝ)] fun t => t⁻¹) :
    let A := fun t : ℝ => (c / t ^ 2) ^ (-(1 : ℝ) / 4)
    let D := fun t : ℝ => ((A t * iteratedDeriv 2 A t : ℝ) : ℂ) -
      (-(4 * (t : ℂ) ^ 2)⁻¹ + r t) / Real.sqrt (c / t ^ 2)
    (∀ t ∈ Ioo 0 b, D t = -(t : ℂ) * r t / Real.sqrt c) ∧
      (∃ δ : ℝ, 0 < δ ∧ δ ≤ b ∧ IntegrableOn D (Ioo 0 δ)) := by
  sorry

end LiouvilleGreen
