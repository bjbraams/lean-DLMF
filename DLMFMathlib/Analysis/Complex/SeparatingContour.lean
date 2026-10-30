/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity.Finset

/-!
# Geometric predicates for separating infinite contours

These are general point-set and parameterization predicates, independent of any
special function or integral identity. Left and right pole families belong to
distinct connected components of the complement of the contour. Exact tails fix
the orientation; finite indentations are unrestricted. All declarations are definitions.
-/

@[expose] public section
open Filter Set
noncomputable section
namespace Complex

/-- Two sets lie in distinct components of the complement of a contour. -/
def SeparatesPoleSets (L : ℝ → ℂ) (P Q : Set ℂ) : Prop :=
  ∃ u v : ℂ, u ∉ Set.range L ∧ v ∉ Set.range L ∧
    connectedComponentIn (Set.range L)ᶜ u ≠ connectedComponentIn (Set.range L)ᶜ v ∧
    P ⊆ connectedComponentIn (Set.range L)ᶜ u ∧
    Q ⊆ connectedComponentIn (Set.range L)ᶜ v

/-- An upward contour with straight vertical tails; the two real offsets may differ. -/
def HasVerticalTails (L : ℝ → ℂ) : Prop :=
  ∃ σ₀ σ₁ : ℝ,
    (∀ᶠ t : ℝ in atBot, L t = σ₀ + t * Complex.I) ∧
    (∀ᶠ t : ℝ in atTop, L t = σ₁ + t * Complex.I)

/-- A right-infinite contour with lower outgoing and upper returning horizontal tails. -/
def HasHorizontalRightTails (L : ℝ → ℂ) : Prop :=
  ∃ x₀ x₁ h₀ h₁ : ℝ, h₀ < h₁ ∧
    (∀ᶠ t : ℝ in atBot, L t = (-t + x₀) + h₀ * Complex.I) ∧
    (∀ᶠ t : ℝ in atTop, L t = (t + x₁) + h₁ * Complex.I)

/-- A contour stays a uniform positive distance from a specified pole set. -/
def StaysAwayFrom (L : ℝ → ℂ) (P : Set ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, ∀ s ∈ P, δ ≤ ‖L t - s‖

end Complex
