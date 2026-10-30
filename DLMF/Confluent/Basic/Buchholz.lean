/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Coefficients of the Whittaker–Buchholz expansion (DLMF §13.24)

The normalized hyperbolic generating function defines the Taylor coefficients in Whittaker's
Bessel-function expansion. Their analytic properties and the expansion itself are developed in
`DLMF.Confluent.WhittakerBuchholz`.
-/

@[expose] public noncomputable section

open Complex
open scoped Real Topology Nat

namespace DLMF.Confluent

/-- Generating function for `p_s^{(μ)}(z)` in DLMF 13.24.3. -/
@[dlmf 13.24.E3]
def whittakerBesselGenerating (μ z t : ℂ) : ℂ :=
  if t = 0 then 1
  else exp (-z / 2 * (cosh t / sinh t - t⁻¹)) * (t / sinh t) ^ (1 - 2 * μ)

/-- The coefficient `p_s^{(μ)}(z) (-z)^s` of the Bessel expansion of Whittaker's `M` (DLMF 13.24.3),
the `s`-th Taylor coefficient at `0` of the generating function times `(-z)^s`. -/
@[dlmf 13.24.E3]
def whittakerBesselCoeff (μ z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (whittakerBesselGenerating μ z) 0 / s.factorial * (-z) ^ s


end DLMF.Confluent
