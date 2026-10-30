/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.IncompleteGamma
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Normalized incomplete Gamma functions: definitions

The totalized quotients `P`, `Q` and Tricomi's entire regularization `γ*` retain their
original definitions. Recurrences, continuation and integral properties are proved in
`DLMF.Statistical.IncompleteGamma`.
-/

@[expose] public noncomputable section

open Complex DLMF.Confluent
open scoped Real Topology Nat

namespace DLMF.Statistical

/-- The regularized lower incomplete Gamma function `P(a,z) = γ(a,z)/Γ(a)` (DLMF 8.2.4). -/
@[dlmf 8.2.E4]
def normIncGammaP (a z : ℂ) : ℂ := lowerIncGamma a z / Gamma a

/-- The regularized upper incomplete Gamma function `Q(a,z) = Γ(a,z)/Γ(a)` (DLMF 8.2.4). -/
@[dlmf 8.2.E4]
def normIncGammaQ (a z : ℂ) : ℂ := upperIncGamma a z / Gamma a


/-- Tricomi's entire incomplete Gamma function `γ*(a,z) = e^{-z} 𝐌(1, a+1, z)`. -/
def scIncGamma (a z : ℂ) : ℂ := exp (-z) * regularizedHGFun {1} {a + 1} z

end DLMF.Statistical
