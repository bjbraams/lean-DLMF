/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Continuous logarithmic lifts on a set

The branch data for contour powers in Kristensson, *Second Order Differential
Equations*, Theorems 6.1–6.2, and Olver, *Asymptotics and Special Functions*,
Chapters 4–5. Logarithms along a contour are specified by continuity and their
exponential, with normalization imposed separately at the initial point.
-/

@[expose] public section

namespace Complex

/-- A continuous logarithmic lift of a complex-valued function on a set.
It records a continued branch rather than taking pointwise principal logarithms. -/
def IsLogarithmicLiftOn {α : Type*} [TopologicalSpace α]
    (γ : α → ℂ) (s : Set α) (L : α → ℂ) : Prop :=
  ContinuousOn L s ∧ ∀ t ∈ s, exp (L t) = γ t

/-- The conditions defining a continuous logarithmic lift. -/
theorem isLogarithmicLiftOn_iff {α : Type*} [TopologicalSpace α]
    (γ : α → ℂ) (s : Set α) (L : α → ℂ) :
    IsLogarithmicLiftOn γ s L ↔ ContinuousOn L s ∧ ∀ t ∈ s, exp (L t) = γ t := Iff.rfl

/-- Construct a logarithmic lift from continuity and the exponential identity.
Branch data used in Kristensson, Theorems 6.1–6.2. -/
theorem IsLogarithmicLiftOn.mk {α : Type*} [TopologicalSpace α]
    {γ : α → ℂ} {s : Set α} {L : α → ℂ}
    (hL : ContinuousOn L s) (hexp : ∀ t ∈ s, exp (L t) = γ t) :
    IsLogarithmicLiftOn γ s L := ⟨hL, hexp⟩

/-- A logarithmic lift is continuous on its domain.
Branch data used in Kristensson, Theorems 6.1–6.2. -/
theorem IsLogarithmicLiftOn.continuousOn {α : Type*} [TopologicalSpace α]
    {γ : α → ℂ} {s : Set α} {L : α → ℂ} (hL : IsLogarithmicLiftOn γ s L) :
    ContinuousOn L s := hL.1

/-- Exponentiating a logarithmic lift recovers the given function. -/
theorem IsLogarithmicLiftOn.exp_eq {α : Type*} [TopologicalSpace α]
    {γ : α → ℂ} {s : Set α} {L : α → ℂ} (hL : IsLogarithmicLiftOn γ s L)
    {t : α} (ht : t ∈ s) : exp (L t) = γ t := hL.2 t ht

/-- A function admitting a logarithmic lift has no zeros on the lift domain. -/
theorem IsLogarithmicLiftOn.ne_zero {α : Type*} [TopologicalSpace α]
    {γ : α → ℂ} {s : Set α} {L : α → ℂ} (hL : IsLogarithmicLiftOn γ s L)
    {t : α} (ht : t ∈ s) : γ t ≠ 0 := by
  rw [← hL.exp_eq ht]
  exact exp_ne_zero _

end Complex
