/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Confluent.Basic.ErrorFunctions

/-!
# Complex error, Fresnel, Dawson and Gaussian primitives
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory

namespace DLMF.Confluent

/-- Faddeeva complex probability function. -/
@[dlmf 7.2.E3]
def faddeevaW (z : ℂ) : ℂ :=
  exp (-z^2)*erfc (-I*z)

/-- Entire Dawson integral. -/
@[dlmf 7.2.E5]
def dawsonF (z : ℂ) : ℂ :=
  exp (-z^2)*primitive (fun t => exp (t^2)) z

/-- Entire Fresnel cosine integral. -/
@[dlmf 7.2.E7]
def fresnelCosInt (z : ℂ) : ℂ :=
  primitive (fun t => cos (π*t^2/2)) z

/-- Entire Fresnel sine integral. -/
@[dlmf 7.2.E8]
def fresnelSinInt (z : ℂ) : ℂ :=
  primitive (fun t => sin (π*t^2/2)) z

/-- Entire continued Fresnel tail integral. -/
@[dlmf 7.2.E6]
def fresnelTail (z : ℂ) : ℂ :=
  (1+I)/2 - fresnelCosInt z-I*fresnelSinInt z

/-- Entire Fresnel auxiliary f. -/
@[dlmf 7.2.E10]
def fresnelAuxFComplex (z : ℂ) : ℂ :=
  (1/2-fresnelSinInt z)*cos (π*z^2/2)-(1/2-fresnelCosInt z)*sin (π*z^2/2)

/-- Entire Fresnel auxiliary g. -/
@[dlmf 7.2.E11]
def fresnelAuxGComplex (z : ℂ) : ℂ :=
  (1/2-fresnelCosInt z)*cos (π*z^2/2)+(1/2-fresnelSinInt z)*sin (π*z^2/2)

/-- Goodwin–Staton integral on the slit plane. -/
@[dlmf 7.2.E12]
def goodwinStatonG (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/(t+z)

/-- Alternative Q notation in DLMF §7.1. -/
def gaussianTail (z : ℂ) : ℂ :=
  erfc (z/Real.sqrt 2)/2

/-- Alternative P or Φ notation in DLMF §7.1. -/
def gaussianCdf (z : ℂ) : ℂ :=
  erfc (-z/Real.sqrt 2)/2

/-- The capitalized Erf convention of DLMF §7.1. -/
def scaledErf (z : ℂ) : ℂ :=
  Real.sqrt π/2*erf z

/-- DLMF §7.1 Erfi normalization, without the usual 2/sqrt(π) factor. -/
def dawsonPrimitive (z : ℂ) : ℂ :=
  exp (z^2)*dawsonF z

/-- Alternative Fresnel C₁ normalization. -/
def fresnelC1 (z : ℂ) : ℂ :=
  fresnelCosInt (Real.sqrt (2/π)*z)

/-- Alternative Fresnel S₁ normalization. -/
def fresnelS1 (z : ℂ) : ℂ :=
  fresnelSinInt (Real.sqrt (2/π)*z)

/-- Alternative Fresnel C₂ normalization with the principal square root. -/
def fresnelC2 (z : ℂ) : ℂ :=
  fresnelCosInt ((2*z/π)^(1/2 : ℂ))

/-- Alternative Fresnel S₂ normalization with the principal square root. -/
def fresnelS2 (z : ℂ) : ℂ :=
  fresnelSinInt ((2*z/π)^(1/2 : ℂ))

end DLMF.Confluent
