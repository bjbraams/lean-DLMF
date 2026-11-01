/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.RegularizedSeries
public import DLMF.Bessel.Basic.Equation

/-!
# Nicholson's integral (AAR §4.13)

## Main results

* `nicholson_integral`: Nicholson's integral for `J_ν² + Y_ν²` (AAR §4.13).

## Implementation notes

The basic properties of the modified Bessel functions (values at the origin, the connection
with `J_ν` and the modified Bessel equation) are in `DLMF.Bessel.Basic.Equation`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Bessel

/-- Nicholson's integral for `J_ν² + Y_ν²` (AAR §4.13). -/
theorem nicholson_integral {ν : ℂ} {x : ℝ} (hx : 0 < x) :
    (besselJ ν x) ^ 2 + (besselY ν x) ^ 2 =
      (8 / (π ^ 2 : ℂ)) *
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          cosh (2 * ν * (t : ℂ)) * besselK 0 (2 * x * Real.sinh t : ℂ) := by
  sorry

end DLMF.Bessel
