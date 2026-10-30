/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Bessel.Basic

/-!
# Struve functions, power series and inhomogeneous equations
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open MeasureTheory DLMF.Bessel

namespace DLMF.Struve

/-- The ordinary or modified Bessel differential operator, with its singularity cleared. -/
def besselResidual (ν σ : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z^2*iteratedDeriv 2 f z+z*deriv f z-(σ*z^2+ν^2)*f z

/-- Reciprocal gamma coefficients; zeros of reciprocal gamma retain exceptional orders. -/
def struveCoeff (ν : ℂ) (n : ℕ) : ℂ :=
  1 / (Gamma (n+3/2) * Gamma (n+ν+3/2))

/-- Entire normalized Struve series. -/
def struveHCore (ν z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1)^n * (z/2)^(2*n) * struveCoeff ν n

/-- Principal Struve H function. -/
@[dlmf 11.2.E1]
def struveH (ν z : ℂ) : ℂ :=
  (z/2)^(ν+1) * struveHCore ν z

/-- Continuation on the logarithmic plane. -/
def struveHOnLog (ν w : ℂ) : ℂ :=
  exp ((ν+1)*(w-log 2)) * struveHCore ν (exp w)

/-- Entire normalized Struve series. -/
def struveLCore (ν z : ℂ) : ℂ :=
  ∑' n : ℕ, 1 * (z/2)^(2*n) * struveCoeff ν n

/-- Principal Struve L function. -/
@[dlmf 11.2.E2]
def struveL (ν z : ℂ) : ℂ :=
  (z/2)^(ν+1) * struveLCore ν z

/-- Continuation on the logarithmic plane. -/
def struveLOnLog (ν w : ℂ) : ℂ :=
  exp ((ν+1)*(w-log 2)) * struveLCore ν (exp w)

/-- A common signed regularized-series representation of the ordinary and modified Struve functions. -/
def struveQuadratic (ν σ z : ℂ) : ℂ :=
  (z/2)^(ν+1)*regularizedHGFun {1} {3/2,ν+3/2} (σ*z^2/4)

/-- The auxiliary ordinary Struve function `H_ν(z) - Y_ν(z)`. -/
@[dlmf 11.2.E5]
def struveK (ν z : ℂ) : ℂ :=
  struveH ν z - besselY ν z

/-- The auxiliary modified Struve function `L_ν(z) - I_ν(z)`. -/
@[dlmf 11.2.E6]
def struveM (ν z : ℂ) : ℂ :=
  struveL ν z - besselI ν z

/-- The ordinary or modified inhomogeneous Bessel equation defining a Struve solution, with the
DLMF reciprocal-Gamma forcing term. -/
@[dlmf 11.2.E7, dlmf 11.2.E9]
def struveEquation (ν : ℂ) (modified : Bool) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  iteratedDeriv 2 f z + deriv f z/z + ((if modified then -1 else 1)-ν^2/z^2)*f z = (z/2)^(ν-1)/(Real.sqrt π*Gamma (ν+1/2))

/-- An analytic function on S satisfying the ordinary or modified Struve differential equation at
each point of S. -/
def IsStruveSolutionOn (ν : ℂ) (modified : Bool) (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ f S ∧ ∀ z ∈ S, struveEquation ν modified f z

end DLMF.Struve
