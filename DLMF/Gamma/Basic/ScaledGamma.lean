/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The scaled Gamma function

This file defines the scaled Gamma function `Γ*(z) = Γ(z) / (e^{-z} z^z (2π/z)^{1/2})` of
DLMF 5.11.3.

## Main definitions

* `scaledGamma`: the scaled Gamma function `Γ*(z)` (DLMF 5.11.3).

## Implementation notes

The powers are Mathlib's principal complex powers. Stirling's series and the asymptotics of
`Γ*` are in `DLMF.Gamma.Asymptotics.Stirling`.
-/

@[expose] public section

open scoped Real

noncomputable section

namespace DLMF.Gamma

/-- Scaled Gamma `Γ*(z)` in DLMF 5.11.3. -/
@[dlmf 5.11.E3]
def scaledGamma (z : ℂ) : ℂ :=
  Complex.Gamma z / (Complex.exp (-z) * z ^ z * (2 * π / z) ^ (1 / 2 : ℂ))

end DLMF.Gamma
