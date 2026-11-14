/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.Analysis.Contour.Residue.Theorem
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Divisor counts for doubly periodic meromorphic functions

Temme, *Special Functions* (1996), §12.3 and Exercises 12.4–12.5,
synopsis TEM-12-09. A `PeriodPair` consists of full periods, rather than
half-periods. Counts use meromorphic orders and include multiplicities.
-/

@[expose] public noncomputable section
open Set Complex
attribute [local instance] Classical.propDecidable
namespace PeriodPair

/-- The open translated fundamental parallelogram for a pair of full periods,
Temme §12.3, synopsis TEM-12-09. -/
def openPeriodCell (L : PeriodPair) (a : ℂ) : Set ℂ :=
  {z | ∀ j : Fin 2, L.basis.repr (z - a) j ∈ Ioo (0 : ℝ) 1}

/-- The basis-coordinate definition of a fundamental period cell, TEM-12-09. -/
theorem mem_openPeriodCell_iff (L : PeriodPair) (a z : ℂ) :
    z ∈ openPeriodCell L a ↔ ∀ j : Fin 2, L.basis.repr (z - a) j ∈ Ioo (0 : ℝ) 1 := Iff.rfl

/-- Pole multiplicity at a point, with zero for nonpoles,
Temme §12.3, synopsis TEM-12-09. -/
def poleMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  Int.toNat (-((meromorphicOrderAt f z).untopD 0))

/-- Zero multiplicity at a point, with zero for poles and for an infinite order.
The infinite-order case is excluded in the nonconstant counting theorems.
Temme §12.3, synopsis TEM-12-09. -/
def zeroMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  Int.toNat ((meromorphicOrderAt f z).untopD 0)

/-- The positive part of the negative meromorphic order, TEM-12-09. -/
theorem poleMultiplicity_def (f : ℂ → ℂ) (z : ℂ) :
    poleMultiplicity f z = Int.toNat (-((meromorphicOrderAt f z).untopD 0)) := rfl

/-- The positive part of the meromorphic order, TEM-12-09. -/
theorem zeroMultiplicity_def (f : ℂ → ℂ) (z : ℂ) :
    zeroMultiplicity f z = Int.toNat ((meromorphicOrderAt f z).untopD 0) := rfl

/-- The total pole multiplicity in an open period cell,
Temme Exercises 12.4–12.5, synopsis TEM-12-09. -/
def poleCount (L : PeriodPair) (a : ℂ) (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ z : ℂ, if z ∈ openPeriodCell L a then poleMultiplicity f z else 0

/-- The total multiplicity of the preimages of a finite value in a period cell,
Temme Exercises 12.4–12.5, synopsis TEM-12-09. -/
def valueCount (L : PeriodPair) (a : ℂ) (f : ℂ → ℂ) (c : ℂ) : ℕ :=
  ∑ᶠ z : ℂ, if z ∈ openPeriodCell L a then zeroMultiplicity (fun w => f w - c) z else 0

/-- The finite-support sum defining the pole count, TEM-12-09. -/
theorem poleCount_def (L : PeriodPair) (a : ℂ) (f : ℂ → ℂ) :
    poleCount L a f = ∑ᶠ z : ℂ, if z ∈ openPeriodCell L a then poleMultiplicity f z else 0 := rfl

/-- The finite-support sum defining the value count, TEM-12-09. -/
theorem valueCount_def (L : PeriodPair) (a : ℂ) (f : ℂ → ℂ) (c : ℂ) :
    valueCount L a f c =
      ∑ᶠ z : ℂ, if z ∈ openPeriodCell L a then zeroMultiplicity (fun w => f w - c) z else 0 := rfl

/-- Only finitely many poles occur in a fundamental period cell,
Temme Exercise 12.4, synopsis TEM-12-09. -/
theorem finite_poles_openPeriodCell (L : PeriodPair) (a : ℂ) {f : ℂ → ℂ}
    (hf : Meromorphic f) :
    {z | z ∈ openPeriodCell L a ∧ 0 < poleMultiplicity f z}.Finite := by
  sorry

/-- The residue sum of an elliptic function in a fundamental parallelogram is zero,
Temme Exercise 12.4, synopsis TEM-12-09. -/
theorem finsum_residue_openPeriodCell_eq_zero (L : PeriodPair) (a : ℂ) {f : ℂ → ℂ}
    (hf : Meromorphic f) (hper : ∀ w ∈ L.lattice, Function.Periodic f w)
    (hbd : ∀ z ∈ frontier (openPeriodCell L a), AnalyticAt ℂ f z) :
    (∑ᶠ z : ℂ, if z ∈ openPeriodCell L a then TauCeti.Contour.residue f z else 0) = 0 := by
  sorry

/-- A nonconstant doubly periodic meromorphic function has at least two poles,
counted with multiplicity, in a cell whose boundary contains no pole,
Temme Exercise 12.4, synopsis TEM-12-09. -/
theorem two_le_poleCount (L : PeriodPair) (a : ℂ) {f : ℂ → ℂ}
    (hf : Meromorphic f) (hper : ∀ w ∈ L.lattice, Function.Periodic f w)
    (hnonconst : ∃ z w, AnalyticAt ℂ f z ∧ AnalyticAt ℂ f w ∧ f z ≠ f w)
    (hbd : ∀ z ∈ frontier (openPeriodCell L a), AnalyticAt ℂ f z) :
    2 ≤ poleCount L a f := by
  sorry

/-- Every value has as many preimages as there are poles, including multiplicities,
Temme Exercise 12.5, synopsis TEM-12-09. -/
theorem valueCount_eq_poleCount (L : PeriodPair) (a : ℂ) {f : ℂ → ℂ}
    (hf : Meromorphic f) (hper : ∀ w ∈ L.lattice, Function.Periodic f w)
    (hnonconst : ∃ z w, AnalyticAt ℂ f z ∧ AnalyticAt ℂ f w ∧ f z ≠ f w)
    (c : ℂ) (hbd : ∀ z ∈ frontier (openPeriodCell L a),
      meromorphicOrderAt (fun w => f w - c) z = 0) :
    {z | z ∈ openPeriodCell L a ∧ 0 < zeroMultiplicity (fun w => f w - c) z}.Finite ∧
      valueCount L a f c = poleCount L a f := by
  sorry

end PeriodPair
