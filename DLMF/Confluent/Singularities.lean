/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.RegularizedSeries
public import DLMFMathlib.Analysis.ODE.Singularities
public import DLMFMathlib.Analysis.ODE.Wronskian

/-!
# Singularities and the second solution of the confluent limit equation

Kristensson, *Second Order Differential Equations*, Chapter 7, §7.1,
pp. 123–125 and §7.3, pp. 132–133. The Kummer and `0F1` equations have regular
origins (with a removable Kummer exception) and irregular infinity. The analytic
factor of the second `0F1` solution is the existing regularized series at parameter
`2-c`; its powers and Wronskian use the principal slit plane.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Confluent

/-- Kummer's origin is at most regular for every parameter pair.
Kristensson, Chapter 7, §7.1, pp. 123–125. -/
theorem kummer_linearODEAtMostRegularAt_zero (a c : ℂ) :
    LinearODEAtMostRegularAt ![fun z => -a / z, fun z => c / z - 1] 0 := by
  sorry

/-- The origin of Kummer's normalized equation is ordinary precisely in its
removable case `a=c=0`. Kristensson, Chapter 7, §7.1, pp. 123–125. -/
theorem kummer_linearODEOrdinaryAt_zero_iff (a c : ℂ) :
    LinearODEOrdinaryAt ![fun z => -a / z, fun z => c / z - 1] 0 ↔ a = 0 ∧ c = 0 := by
  sorry

/-- Outside its removable case the Kummer origin is strictly regular singular.
Kristensson, Chapter 7, §7.1, pp. 123–125. -/
theorem kummer_linearODERegularSingularAt_zero {a c : ℂ} (h : a ≠ 0 ∨ c ≠ 0) :
    LinearODERegularSingularAt ![fun z => -a / z, fun z => c / z - 1] 0 := by
  sorry

/-- Infinity is irregular for Kummer's equation, even when a particular solution
happens to be elementary. Kristensson, Chapter 7, §7.1, pp. 123–125. -/
theorem kummer_linearODEIrregularAtInfinity (a c : ℂ) :
    LinearODEIrregularAtInfinity ![fun z => -a / z, fun z => c / z - 1] := by
  sorry

/-- The `0F1` limit equation has a strictly regular singular origin for every lower
parameter: its zeroth-order coefficient is `-1/z`. Kristensson, Chapter 7,
§7.3, pp. 132–133. -/
theorem limitFunction_linearODERegularSingularAt_zero (c : ℂ) :
    LinearODERegularSingularAt ![fun z => -(1 : ℂ) / z, fun z => c / z] 0 := by
  sorry

/-- The `0F1` limit equation has irregular infinity. Kristensson, Chapter 7,
§7.3, pp. 132–133. -/
theorem limitFunction_linearODEIrregularAtInfinity (c : ℂ) :
    LinearODEIrregularAtInfinity ![fun z => -(1 : ℂ) / z, fun z => c / z] := by
  sorry

/-- Gauging the regularized series at `2-c` by `z^(1-c)` gives the second limit
solution. Its analytic factor satisfies the existing `regularized0F1_ode` with
parameter `2-c`. Kristensson, Chapter 7, (7.10)–(7.11), pp. 132–133. -/
theorem limitFunction_second_solution (c : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    let u := fun w : ℂ => w ^ (1 - c) * regularizedHGFun ∅ {2 - c} w
    z * deriv (deriv u) z + c * deriv u z - u z = 0 := by
  sorry

/-- The two regularized limit solutions have Wronskian `sin(pi*c)/pi*z^(-c)`.
It is nonzero for noninteger `c`, giving the source's independent local pair.
Kristensson, Chapter 7, §7.3, pp. 132–133. -/
theorem wronskian_limitFunction_pair (c : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    ODE.wronskian (regularizedHGFun (∅ : Multiset ℂ) {c})
      (fun w : ℂ => w ^ (1 - c) * regularizedHGFun ∅ {2 - c} w) z =
        sin (Real.pi * c) / Real.pi * z ^ (-c) := by
  sorry

end DLMF.Confluent
