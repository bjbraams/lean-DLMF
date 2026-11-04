/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.IncompleteGamma
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Tricomi's incomplete Gamma function: definition (DLMF §8.2)

## Main definitions

* `tricomiIncompleteGamma`: Tricomi's entire incomplete Gamma function
  `γ*(a,z) = e^{-z} 𝐌(1, a+1, z)` (DLMF 8.2.6–8.2.7).

## Implementation notes

The normalized functions `P` and `Q` are the continuations `regularizedGamma` and
`regularizedIncompleteGammaQ` of `DLMF.IncompleteGamma.Basic`, built on `γ*`. Recurrences and
series of `γ*` are proved in `DLMF.Statistical.IncompleteGamma`.
-/

@[expose] public noncomputable section

open Complex DLMF.Confluent
open scoped Real Topology Nat

namespace DLMF.Statistical

/-- Tricomi's entire incomplete Gamma function `γ*(a,z) = e^{-z} 𝐌(1, a+1, z)`. -/
def tricomiIncompleteGamma (a z : ℂ) : ℂ := exp (-z) * regularizedHGFun {1} {a + 1} z

end DLMF.Statistical
