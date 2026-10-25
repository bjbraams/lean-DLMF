/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Singularities of normalized scalar complex linear differential equations

The coefficient germs define the classification: a removable totalization at a
singular point is ignored, and an analytic extension is recorded explicitly.
The reciprocal-variable pullback is extracted by applying the original operator
to normalized monomials in `1/z-u`; this avoids imposing a choice of values at zero
on rational coefficient functions. This file contains definitions only.
-/

@[expose] public section
open Filter Set
open scoped Topology
noncomputable section
namespace Complex

/-- Value of a normalized order-n scalar linear differential operator. -/
def linearODEValue {n : ℕ} (c : Fin n → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv n f z + ∑ j, c j z * iteratedDeriv j.val f z

/-- A coefficient germ has an analytic extension at a finite point. -/
def linearODEOrdinaryAt {n : ℕ} (c : Fin n → ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∀ j, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ c j =ᶠ[𝓝[≠] z₀] g

/-- Weighted coefficients have analytic extensions, allowing an ordinary point. -/
def linearODEAtMostRegularAt {n : ℕ} (c : Fin n → ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∀ j, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
    (fun z => (z - z₀) ^ (n - j.val) * c j z) =ᶠ[𝓝[≠] z₀] g

/-- A regular singular point, explicitly excluding ordinary points. -/
def linearODERegularSingularAt {n : ℕ} (c : Fin n → ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ¬linearODEOrdinaryAt c z₀ ∧ linearODEAtMostRegularAt c z₀

/-- An irregular singular point. -/
def linearODEIrregularAt {n : ℕ} (c : Fin n → ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ¬linearODEOrdinaryAt c z₀ ∧ ¬linearODEAtMostRegularAt c z₀

/-- The unnormalized coefficient of the jth derivative after the change z=1/u.
Normalized monomials extract each derivative coefficient by its jet at u. -/
def linearODEReciprocalRaw {n : ℕ} (c : Fin n → ℂ → ℂ) (j : ℕ) (u : ℂ) : ℂ :=
  linearODEValue c (fun z => (z⁻¹ - u) ^ j / j.factorial) u⁻¹

/-- Normalized coefficients after the reciprocal change of variable. -/
def linearODEReciprocalCoeff {n : ℕ} (c : Fin n → ℂ → ℂ) (j : Fin n) (u : ℂ) : ℂ :=
  linearODEReciprocalRaw c j.val u / linearODEReciprocalRaw c n u

/-- Ordinary behavior at infinity is ordinary behavior of the reciprocal equation at zero. -/
def linearODEOrdinaryAtInfinity {n : ℕ} (c : Fin n → ℂ → ℂ) : Prop :=
  linearODEOrdinaryAt (linearODEReciprocalCoeff c) 0

/-- At most regular behavior at infinity, including removable degeneracies. -/
def linearODEAtMostRegularAtInfinity {n : ℕ} (c : Fin n → ℂ → ℂ) : Prop :=
  linearODEAtMostRegularAt (linearODEReciprocalCoeff c) 0

/-- Irregular behavior at infinity. -/
def linearODEIrregularAtInfinity {n : ℕ} (c : Fin n → ℂ → ℂ) : Prop :=
  linearODEIrregularAt (linearODEReciprocalCoeff c) 0

end Complex
