/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Airy functions and their differential equation: definitions

The regularized hypergeometric series define `Ai`, `Bi`, their derivative functions and
solutions of Airy's equation. Differential, initial-value and connection properties are
proved in `DLMF.Airy.Properties`.
-/

@[expose] public noncomputable section

open Complex
open scoped Real ComplexConjugate

namespace DLMF.Airy

/-- The series `f(z) = ₀F̃₁(;2/3;z³/9)` (DLMF 9.4, Beals–Wong (9.9.4)). -/
def airyF (z : ℂ) : ℂ := regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (z ^ 3 / 9)

/-- The series `g(z) = z ₀F̃₁(;4/3;z³/9)`. -/
def airyG (z : ℂ) : ℂ := z * regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (z ^ 3 / 9)

/-- The derivative of `airyF`. -/
def airyFDeriv (z : ℂ) : ℂ := z ^ 2 / 3 * regularizedHGFun (∅ : Multiset ℂ) {5 / 3} (z ^ 3 / 9)

/-- The derivative of `airyG`. -/
def airyGDeriv (z : ℂ) : ℂ :=
  regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (z ^ 3 / 9) +
    z ^ 3 / 3 * regularizedHGFun (∅ : Multiset ℂ) {7 / 3} (z ^ 3 / 9)


/-- The Airy function `Ai` (DLMF 9.4.1), via its Maclaurin series. -/
@[dlmf 9.4.E1]
def airyAi (z : ℂ) : ℂ :=
  (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * airyF z - (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyG z

/-- The derivative `Ai'` (DLMF 9.4.2). -/
@[dlmf 9.4.E2]
def airyAiDeriv (z : ℂ) : ℂ :=
  (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * airyFDeriv z -
    (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyGDeriv z

/-- The Airy function `Bi` (DLMF 9.4.3), via its Maclaurin series. -/
@[dlmf 9.4.E3]
def airyBi (z : ℂ) : ℂ :=
  (Real.sqrt 3 : ℂ) *
    ((((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * airyF z +
      (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyG z)

/-- The derivative `Bi'` (DLMF 9.4.4). -/
@[dlmf 9.4.E4]
def airyBiDeriv (z : ℂ) : ℂ :=
  (Real.sqrt 3 : ℂ) *
    ((((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * airyFDeriv z +
      (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * airyGDeriv z)


/-- `w, w'` solve Airy's equation `w'' = z w` on all of `ℂ`. -/
def IsAirySol (w w' : ℂ → ℂ) : Prop := ∀ z, HasDerivAt w (w' z) z ∧ HasDerivAt w' (z * w z) z

end DLMF.Airy
