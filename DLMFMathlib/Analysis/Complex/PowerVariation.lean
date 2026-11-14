/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Variation of complex powers on straight lines and progressive paths

Olver, *Asymptotics and Special Functions*, Chapter 6, Lemma 13.1 and §13.2,
pp. 225–226, synopsis O-6.19. The straight-line formula uses an actual continuous
logarithmic lift. The right-half-plane result is an infimum over finite paths
completed with their positive-ray tail, not an assertion of finite attainment.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Real Topology ENNReal

namespace Complex

/-- The Gamma quotient controlling variation of `z^(-α)` on a complete straight line.
Olver, Chapter 6, Lemma 13.1, (13.02), synopsis O-6.19. -/
def powerVariationConstant (α : ℝ) : ℝ :=
  Real.sqrt π * Real.Gamma (α / 2 + 1) / Real.Gamma ((α + 1) / 2)

/-- The explicit Gamma quotient. -/
theorem powerVariationConstant_def (α : ℝ) :
    powerVariationConstant α = Real.sqrt π * Real.Gamma (α / 2 + 1) /
      Real.Gamma ((α + 1) / 2) := rfl

/-- Exact total variation on any complete straight line at positive distance `d` from
zero, with a continuous logarithm on the line. Olver, Chapter 6, Lemma 13.1,
(13.01)–(13.02), p. 225, synopsis O-6.19. -/
theorem eVariationOn_exp_neg_mul_lift_line {α d θ : ℝ} (hα : 0 < α) (hd : 0 < d)
    {L : ℝ → ℂ} (hL : Continuous L)
    (hexp : ∀ t : ℝ, exp (L t) = exp (I * θ) * ((d : ℂ) + I * t)) :
    eVariationOn (fun t : ℝ => exp (-(α : ℂ) * L t)) univ =
      ENNReal.ofReal (2 * powerVariationConstant α * d ^ (-α)) := by
  sorry

/-- Costs of finite smooth progressive paths from `z` to a positive real `R`,
completed by the exact positive-ray tail variation `R^(-α)`.
Olver, Chapter 6, §13.2 and its footnote, p. 226, synopsis O-6.19. -/
def progressivePowerVariationCosts (α : ℝ) (z : ℂ) : Set ℝ :=
  {c | ∃ R : ℝ, ∃ γ : ℝ → ℂ, 0 < R ∧ γ 0 = z ∧ γ 1 = (R : ℂ) ∧
    ContDiffOn ℝ 2 γ (Icc 0 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, 0 < (γ t).re) ∧
    MonotoneOn (fun t => (γ t).re) (Icc 0 1) ∧
    c = (eVariationOn (fun t => (γ t) ^ (-(α : ℂ))) (Icc 0 1)).toReal + R ^ (-α)}

/-- The finite-path and tail conditions defining the progressive variation costs. -/
theorem mem_progressivePowerVariationCosts_iff (α : ℝ) (z : ℂ) (c : ℝ) :
    c ∈ progressivePowerVariationCosts α z ↔
      ∃ R : ℝ, ∃ γ : ℝ → ℂ, 0 < R ∧ γ 0 = z ∧ γ 1 = (R : ℂ) ∧
        ContDiffOn ℝ 2 γ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, 0 < (γ t).re) ∧
        MonotoneOn (fun t => (γ t).re) (Icc 0 1) ∧
        c = (eVariationOn (fun t => (γ t) ^ (-(α : ℂ))) (Icc 0 1)).toReal + R ^ (-α) :=
  Iff.rfl

/-- The sharp right-half-plane progressive variation is an infimum of finite completed
path costs; finite attainment is not asserted. Olver, Chapter 6, §13.2,
(13.03), pp. 225–226, synopsis O-6.19. -/
theorem csInf_progressivePowerVariationCosts {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : 0 < z.re) :
    (progressivePowerVariationCosts α z).Nonempty ∧
      BddBelow (progressivePowerVariationCosts α z) ∧
      sInf (progressivePowerVariationCosts α z) = ‖z‖ ^ (-α) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c ∈ progressivePowerVariationCosts α z,
        c < ‖z‖ ^ (-α) + ε := by
  sorry

end Complex
