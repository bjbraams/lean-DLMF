/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerM
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Canonical parabolic cylinder functions and Weber solution data
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory intervalIntegral

namespace DLMF.Confluent

/-- The even solution `u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` (DLMF 12.7.12). -/
@[dlmf 12.7.E12]
def pcfEven (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2)

/-- The odd solution `u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)` (DLMF 12.7.13). -/
@[dlmf 12.7.E13]
def pcfOdd (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2)

/-- The derivative of `u₁`. -/
def pcfEvenDeriv (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * (-(1 / 2) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2) +
    (a + 1 / 2) * kummerM (a / 2 + 1 / 4 + 1) (1 / 2 + 1) (z ^ 2 / 2))

/-- The derivative of `u₂`. -/
def pcfOddDeriv (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * ((1 - z ^ 2 / 2) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2) +
    (a + 3 / 2) / 3 * z ^ 2 * kummerM (a / 2 + 3 / 4 + 1) (3 / 2 + 1) (z ^ 2 / 2))

/-- **Weber's parabolic cylinder function** `U(a,z)`, the entire solution of
`w'' = (z²/4 + a) w` fixed by its initial values (DLMF 12.2.6, 12.2.7, 12.4.1):
`U(a,z) = U(a,0) u₁(a,z) + U'(a,0) u₂(a,z)`. The reciprocal Gamma factors vanish at the
poles, as for the entire function `1/Γ`. -/
@[dlmf 12.4.E1]
def pcfU (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ * pcfEven a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ * pcfOdd a z

/-- The derivative `U'(a,z)`. -/
def pcfUDeriv (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
      pcfEvenDeriv a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ * pcfOddDeriv a z

/-- Whittaker's notation `D_ν(z) = U(-ν - 1/2, z)` (DLMF 12.2.5). -/
@[dlmf 12.2.E5]
def pcfD (ν z : ℂ) : ℂ := pcfU (-ν - 1 / 2) z

/-- A function and a derivative candidate solve Weber's equation with parameter `a`. -/
def IsWeberSol (a : ℂ) (f f' : ℂ → ℂ) : Prop :=
  ∀ z, HasDerivAt f (f' z) z ∧ HasDerivAt f' ((z ^ 2 / 4 + a) * f z) z

/-- The moments `∫₀^∞ t^c e^{-t²/2 - z t} dt` used in DLMF 12.5.1. -/
def pcfMoment (c z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)

/-- `V(a,0)` (DLMF 12.2.8), with reciprocal Gamma factors, so that it is entire in `a`. -/
def pcfVZero (a : ℂ) : ℂ :=
  π * (2 : ℂ) ^ (a / 2 + 1 / 4) * (Gamma (3 / 4 - a / 2))⁻¹ ^ 2 * (Gamma (1 / 4 + a / 2))⁻¹

/-- `V'(a,0)` (DLMF 12.2.9), with reciprocal Gamma factors. -/
def pcfVDerivZero (a : ℂ) : ℂ :=
  π * (2 : ℂ) ^ (a / 2 + 3 / 4) * (Gamma (1 / 4 - a / 2))⁻¹ ^ 2 * (Gamma (3 / 4 + a / 2))⁻¹

/-- **Weber's second function** `V(a,z) = V(a,0) u₁(a,z) + V'(a,0) u₂(a,z)` (DLMF 12.4.2). It is
entire in `a` and `z`; see `pcfV_eq` for the classical form in terms of `U(a, ±z)`. -/
@[dlmf 12.4.E2]
def pcfV (a z : ℂ) : ℂ := pcfVZero a * pcfEven a z + pcfVDerivZero a * pcfOdd a z

/-- The derivative `V'(a,z)`. -/
def pcfVDeriv (a z : ℂ) : ℂ := pcfVZero a * pcfEvenDeriv a z + pcfVDerivZero a * pcfOddDeriv a z

end DLMF.Confluent
