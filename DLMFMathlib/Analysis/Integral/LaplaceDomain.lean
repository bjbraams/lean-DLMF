/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Absolute convergence domain of a functional Laplace integral

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 2, Definition 2.10,
equation (2.58). The abscissa is extended real so that convergence for all real arguments
is represented by negative infinity. These are transforms of complex-valued functions
with respect to Lebesgue measure on the positive half-line.
-/

@[expose] public noncomputable section

open Set

namespace MeasureTheory

/-- The Laplace integral on the positive half-line, totalized by the Bochner integral
outside its absolute convergence domain. Duverney Definition 2.10, DU-2.14. -/
def laplaceIntegral (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (Real.exp (-x * t) : ℂ) * f t

/-- The defining Laplace integral. Duverney (2.58), synopsis DU-2.14. -/
theorem laplaceIntegral_def (f : ℝ → ℂ) (x : ℝ) :
    laplaceIntegral f x = ∫ t in Ioi (0 : ℝ), (Real.exp (-x * t) : ℂ) * f t := rfl

/-- A continuous function is Laplace-transformable if some real exponential damping
makes it absolutely integrable. Duverney Definition 2.10, synopsis DU-2.14. -/
def IsLaplaceTransformable (f : ℝ → ℂ) : Prop :=
  ContinuousOn f (Ioi 0) ∧
    ∃ x : ℝ, IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) * f t) (Ioi 0)

/-- The Laplace-transformability predicate. Duverney Definition 2.10, DU-2.14. -/
theorem isLaplaceTransformable_iff (f : ℝ → ℂ) :
    IsLaplaceTransformable f ↔ ContinuousOn f (Ioi 0) ∧
      ∃ x : ℝ, IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) * f t) (Ioi 0) := Iff.rfl

/-- Introduction of Laplace transformability. Duverney Definition 2.10, DU-2.14. -/
theorem IsLaplaceTransformable.mk {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {x : ℝ}
    (hx : IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) * f t) (Ioi 0)) :
    IsLaplaceTransformable f := ⟨hf, x, hx⟩

/-- A Laplace-transformable function is continuous on the positive half-line.
Duverney Definition 2.10, synopsis DU-2.14. -/
theorem IsLaplaceTransformable.continuousOn {f : ℝ → ℂ} (hf : IsLaplaceTransformable f) :
    ContinuousOn f (Ioi 0) := hf.1

/-- A Laplace-transformable function has a real damping exponent with absolute convergence.
Duverney Definition 2.10, synopsis DU-2.14. -/
theorem IsLaplaceTransformable.exists_integrableOn {f : ℝ → ℂ}
    (hf : IsLaplaceTransformable f) :
    ∃ x : ℝ, IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) * f t) (Ioi 0) := hf.2

/-- The extended-real abscissa of absolute convergence of the Laplace integral.
Duverney Definition 2.10, synopsis DU-2.14. -/
def laplaceAbscissa (f : ℝ → ℂ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) ''
    {x : ℝ | IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) * f t) (Ioi 0)})

/-- The abscissa is the infimum of the absolute convergence domain.
Duverney Definition 2.10, synopsis DU-2.14. -/
theorem laplaceAbscissa_def (f : ℝ → ℂ) :
    laplaceAbscissa f = sInf ((fun x : ℝ => (x : EReal)) ''
      {x : ℝ | IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) * f t) (Ioi 0)}) := rfl

/-- Absolute convergence holds strictly to the right of the abscissa.
Duverney Definition 2.10 and the paragraph following (2.58), synopsis DU-2.14. -/
theorem IsLaplaceTransformable.integrableOn_of_abscissa_lt {f : ℝ → ℂ}
    (hf : IsLaplaceTransformable f) {x : ℝ} (hx : laplaceAbscissa f < (x : EReal)) :
    IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) * f t) (Ioi 0) := by
  sorry

end MeasureTheory
