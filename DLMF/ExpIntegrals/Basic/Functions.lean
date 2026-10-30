/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Confluent.Basic.ExponentialIntegrals
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Exponential, trigonometric and hyperbolic integral functions
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory

namespace DLMF.Confluent

/-- The entire complementary exponential integral. -/
@[dlmf 6.2.E3]
def expIntEin (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(k+1) / ((k+1).factorial * (k+1 : ℂ))

/-- The entire sine integral. -/
@[dlmf 6.2.E9]
def sinInt (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(2*k+1) / ((2*k+1).factorial * (2*k+1 : ℂ))

/-- The entire complementary cosine integral. -/
@[dlmf 6.2.E12]
def cosIntCin (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(2*k+2) / ((2*k+2).factorial * (2*k+2 : ℂ))

/-- Principal cosine integral. -/
@[dlmf 6.2.E13]
def cosInt (z : ℂ) : ℂ :=
  -cosIntCin z + log z + Real.eulerMascheroniConstant

/-- The shifted sine integral si. -/
@[dlmf 6.2.E10]
def sinIntTail (z : ℂ) : ℂ :=
  sinInt z - π/2

/-- The entire hyperbolic sine integral. -/
@[dlmf 6.2.E15]
def sinhInt (z : ℂ) : ℂ :=
  ∑' k : ℕ, z^(2*k+1) / ((2*k+1).factorial * (2*k+1 : ℂ))

/-- Principal hyperbolic cosine integral. -/
@[dlmf 6.2.E16]
def coshInt (z : ℂ) : ℂ :=
  Real.eulerMascheroniConstant + log z + ∑' k : ℕ, z^(2*k+2) / ((2*k+2).factorial * (2*k+2 : ℂ))

/-- Real Ei, with a totalized value at zero outside its mathematical domain. -/
@[dlmf 6.2.E5]
def Real.expIntEi (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log |x| - (DLMF.Confluent.expIntEin (-x)).re

/-- Real logarithmic integral, singular at x=1. -/
@[dlmf 6.2.E8]
def Real.logIntLi (x : ℝ) : ℝ :=
  Real.expIntEi (Real.log x)

/-- Auxiliary sine/cosine integral f. -/
@[dlmf 6.2.E17]
def expIntAuxF (z : ℂ) : ℂ :=
  cosInt z * sin z - sinIntTail z * cos z

/-- Auxiliary sine/cosine integral g. -/
@[dlmf 6.2.E18]
def expIntAuxG (z : ℂ) : ℂ :=
  -cosInt z * cos z - sinIntTail z * sin z

end DLMF.Confluent
