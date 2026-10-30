/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.IncompleteGamma
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Generalized exponential integral and legacy real primitive definitions
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory Asymptotics

namespace DLMF.Confluent

/-- The generalized exponential integral `E_p(z) = z^{p-1} Γ(1-p, z)` (DLMF 8.19.1). -/
@[dlmf 8.19.E1]
def genExpIntE (p z : ℂ) : ℂ :=
  z ^ (p - 1) * upperIncGamma (1 - p) z

/-- The entire function `Ein(x) = ∫₀ˣ (1 - e^{-t})/t dt` (DLMF 6.2.3), on the real line. -/
@[dlmf 6.2.E3]
def Real.expIntEin (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (1 - Real.exp (-t)) / t

/-- The sine integral `Si(x) = ∫₀ˣ sin t / t dt` (DLMF 6.2.9). -/
@[dlmf 6.2.E9]
def Real.sinInt (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.sinc t

/-- The entire function `Cin(x) = ∫₀ˣ (1 - cos t)/t dt` (DLMF 6.2.12), on the real line. -/
@[dlmf 6.2.E12]
def Real.cosIntCin (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (1 - Real.cos t) / t

/-- The cosine integral `Ci(x) = -Cin(x) + log x + γ` (DLMF 6.2.13), for `x > 0`. -/
@[dlmf 6.2.E13]
def Real.cosInt (x : ℝ) : ℝ :=
  -Real.cosIntCin x + Real.log x + Real.eulerMascheroniConstant

end DLMF.Confluent
