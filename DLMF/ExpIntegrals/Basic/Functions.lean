/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMF.Confluent.Basic.ExponentialIntegrals
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Exponential, trigonometric and hyperbolic integral functions

Definitions of the functions of DLMF §6.2. The generalized exponential integral `E_p`, and
hence `E₁ = expIntegralE 1`, is defined in the confluent hypergeometric area.

## Main definitions

* `expIntegralEin`: the entire complementary exponential integral `Ein(z)` (DLMF 6.2.3).
* `Real.expIntegralEi`: the real exponential integral `Ei(x)` (DLMF 6.2.5), totalized at `0`.
* `Real.logIntegralLi`: the real logarithmic integral `li(x)` (DLMF 6.2.8).
* `sinIntegral`, `sinIntegralTail`: the sine integrals `Si(z)` and `si(z)` (DLMF 6.2.9, 6.2.10).
* `cosIntegralCin`, `cosIntegral`: the entire `Cin(z)` and the principal `Ci(z)` (DLMF 6.2.12,
  6.2.13).
* `sinhIntegral`, `coshIntegral`: the entire `Shi(z)` and the principal `Chi(z)` (DLMF 6.2.15,
  6.2.16).
* `sinIntegralAuxiliaryF`, `sinIntegralAuxiliaryG`: the auxiliary functions `f(z)`, `g(z)` (DLMF
  6.2.17, 6.2.18).
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory

namespace DLMF.Confluent

/-- The entire complementary exponential integral. -/
@[dlmf 6.2.E3]
def expIntegralEin (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(k+1) / ((k+1).factorial * (k+1 : ℂ))

/-- The entire sine integral. -/
@[dlmf 6.2.E9]
def sinIntegral (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(2*k+1) / ((2*k+1).factorial * (2*k+1 : ℂ))

/-- The entire complementary cosine integral. -/
@[dlmf 6.2.E12]
def cosIntegralCin (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(2*k+2) / ((2*k+2).factorial * (2*k+2 : ℂ))

/-- Principal cosine integral. -/
@[dlmf 6.2.E13]
def cosIntegral (z : ℂ) : ℂ :=
  -cosIntegralCin z + log z + Real.eulerMascheroniConstant

/-- The shifted sine integral si. -/
@[dlmf 6.2.E10]
def sinIntegralTail (z : ℂ) : ℂ :=
  sinIntegral z - π/2

/-- The entire hyperbolic sine integral. -/
@[dlmf 6.2.E15]
def sinhIntegral (z : ℂ) : ℂ :=
  ∑' k : ℕ, z^(2*k+1) / ((2*k+1).factorial * (2*k+1 : ℂ))

/-- Principal hyperbolic cosine integral. -/
@[dlmf 6.2.E16]
def coshIntegral (z : ℂ) : ℂ :=
  Real.eulerMascheroniConstant + log z + ∑' k : ℕ, z^(2*k+2) / ((2*k+2).factorial * (2*k+2 : ℂ))

/-- Real Ei, with a totalized value at zero outside its mathematical domain. -/
@[dlmf 6.2.E5]
def Real.expIntegralEi (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log |x| - (DLMF.Confluent.expIntegralEin (-x)).re

/-- Real logarithmic integral, singular at x=1. -/
@[dlmf 6.2.E8]
def Real.logIntegralLi (x : ℝ) : ℝ :=
  Real.expIntegralEi (Real.log x)

/-- Auxiliary sine/cosine integral f. -/
@[dlmf 6.2.E17]
def sinIntegralAuxiliaryF (z : ℂ) : ℂ :=
  cosIntegral z * sin z - sinIntegralTail z * cos z

/-- Auxiliary sine/cosine integral g. -/
@[dlmf 6.2.E18]
def sinIntegralAuxiliaryG (z : ℂ) : ℂ :=
  -cosIntegral z * cos z - sinIntegralTail z * sin z

end DLMF.Confluent
