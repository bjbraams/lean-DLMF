/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bessel functions: definitions

Mathlib provides the first-kind Bessel function `Complex.besselJ`. This file defines the
second-kind and modified Bessel functions (DLMF §§10.2, 10.25, 10.27), with integer orders
given by limits in the order parameter. Series, derivative and differential-equation
properties are in `DLMF.Bessel.RegularizedSeries` and `DLMF.Bessel.Modified`.

## Main definitions

* `besselY`: Weber's function `Y_ν` (DLMF 10.2.3).
* `besselI`: the modified Bessel function `I_ν` (DLMF 10.25.2).
* `besselK`: Macdonald's function `K_ν` (DLMF 10.27.4).
-/

@[expose] public noncomputable section

open Complex
open scoped Real Nat Topology

namespace DLMF.Bessel

/-- Bessel function of the second kind (Weber's `Y_ν`), with integer orders
defined by their limits in the order parameter (AAR §4.6). -/
@[dlmf 10.2.E3]
def besselY (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      (besselJ μ z * cos (μ * π) - besselJ (-μ) z) / sin (μ * π))
  else (besselJ ν z * cos (ν * π) - besselJ (-ν) z) / sin (ν * π)

/-- Modified Bessel function of the first kind. -/
@[dlmf 10.25.E2]
def besselI (ν z : ℂ) : ℂ :=
  (z / 2) ^ ν * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (z ^ 2 / 4)

/-- Modified Bessel function of the second kind (Macdonald's `K_ν`), with integer
orders defined by their limits in the order parameter (AAR (4.12.3)). -/
@[dlmf 10.27.E4]
def besselK (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      π / 2 * (besselI (-μ) z - besselI μ z) / sin (μ * π))
  else π / 2 * (besselI (-ν) z - besselI ν z) / sin (ν * π)

end DLMF.Bessel
