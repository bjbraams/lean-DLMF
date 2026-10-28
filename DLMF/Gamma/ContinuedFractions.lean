/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Continued fractions (DLMF §5.10)

The Stieltjes-type continued fraction for Binet's function. The source lists
explicit partial numerators `a_0,…,a_6`; those values are recorded below. The
general coefficients are not given in closed form, so no convergence statement is made.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-- Partial numerators `a_k` in DLMF 5.10.1, with the seven tabulated values. -/
@[dlmf 5.10.E1]
def logGammaContFractCoeff : ℕ → ℂ
  | 0 => 1 / 12
  | 1 => 1 / 30
  | 2 => 53 / 210
  | 3 => 195 / 371
  | 4 => 22999 / 22737
  | 5 => 29944523 / 19733142
  | 6 => 109352241009 / 48264275462
  | _ => 0

/-- The generalized continued fraction `0 + a₀/(z + a₁/(z + ⋯))` with the coefficients
`logGammaContFractCoeff` of DLMF 5.10.1 (Stieltjes's continued fraction for Binet's function). -/
@[dlmf 5.10.E1]
def logGammaContinuedFraction (z : ℂ) : GenContFract ℂ where
  h := 0
  s := Stream'.Seq.ofStream fun k => ⟨logGammaContFractCoeff k, z⟩

/-- Binet's function, the left-hand side of 5.10.1. -/
@[dlmf 5.10.E1]
def logGammaBinet (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) + x - (x - 1 / 2) * Real.log x - (1 / 2) * Real.log (2 * π)

/- The convergence statement of DLMF 5.10.1 was removed: `logGammaContFractCoeff` records only
the seven tabulated partial numerators and sets the rest to zero, so the convergents stabilize
at a truncation that differs from `logGammaBinet` (by about `1.5e-7` at `x = 3/2`). Stating
the limit requires the full coefficient sequence. See `STATEMENT_AUDIT_2026-09-27.md`. -/

end DLMF.Gamma
