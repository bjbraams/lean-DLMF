/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.Functions

/-!
# Chosen period pairs and Weierstrass functions from their invariants
-/

@[expose] public noncomputable section

open Complex PeriodPair
open scoped Real

namespace DLMF.Weierstrass

/-- A chosen period pair with invariants `g₂, g₃` (junk `PeriodPair` when none exists, i.e.
when `g₂³ = 27g₃²`). Used to define the invariants form of the Weierstrass functions. -/
def periodPairOfInvariants (g₂ g₃ : ℂ) : PeriodPair :=
  Classical.epsilon fun L : PeriodPair ↦ L.g₂ = g₂ ∧ L.g₃ = g₃

/-- `℘(z; g₂, g₃)` (DLMF 23.3.8): `℘(z|𝕃)` for the lattice with invariants `g₂, g₃`; DLMF
assumes `g₂³ ≠ 27g₃²`. -/
@[dlmf 23.3.E8]
def weierstrassPInvariants (g₂ g₃ z : ℂ) : ℂ := ℘[periodPairOfInvariants g₂ g₃] z

/-- `ζ(z; g₂, g₃)` (DLMF §23.3(i)). -/
@[dlmf 23.3.i]
def weierstrassZetaInvariants (g₂ g₃ z : ℂ) : ℂ := weierstrassZeta (periodPairOfInvariants g₂ g₃) z

/-- `σ(z; g₂, g₃)` (DLMF §23.3(i)). -/
@[dlmf 23.3.i]
def weierstrassSigmaInvariants (g₂ g₃ z : ℂ) : ℂ :=
  weierstrassSigma (periodPairOfInvariants g₂ g₃) z

end DLMF.Weierstrass
