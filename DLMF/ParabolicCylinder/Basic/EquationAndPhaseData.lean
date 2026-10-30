/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic.Functions

/-!
# Quadratic cylinder equations, amplitudes and phases
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric

namespace DLMF.Confluent

/-- The scalar quadratic-potential equation `f″(z) + (az²+bz+c)f(z) = 0`, written using totalized
iterated derivatives. -/
@[dlmf 12.2.E1]
def IsQuadraticCylinderSolution (a b c : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, iteratedDeriv 2 f z+(a*z^2+b*z+c)*f z=0

/-- The oscillatory Weber equation `f″(z) + (z²/4-a)f(z) = 0`, written using totalized iterated
derivatives. -/
@[dlmf 12.2.E3]
def IsOscillatoryCylinderSolution (a : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, iteratedDeriv 2 f z+(z^2/4-a)*f z=0

/-- The barred U solution; meaningful only away from positive half-integral parameters, not complex conjugation. -/
@[dlmf 12.2.E21]
def pcfUBar (a z : ℂ) : ℂ :=
  Gamma (1/2-a)*pcfV a z

/-- The derivative of the Gamma-normalized second cylinder solution: `Γ(1/2-a) V′(a,z)`. -/
def pcfUBarDeriv (a z : ℂ) : ℂ :=
  Gamma (1/2-a)*pcfVDeriv a z

/-- The modulus of the complex pair `U(a,x) + i UBar(a,x)` on the real axis. -/
@[dlmf 12.2.E22]
def pcfF (a x : ℝ) : ℝ :=
  ‖pcfU a x+I*pcfUBar a x‖

/-- Principal phase representative; a continuous lift differs by integral multiples of two pi. -/
@[dlmf 12.2.E22]
def pcfTheta (a x : ℝ) : ℝ :=
  arg ((pcfU a x+I*pcfUBar a x))

/-- The modulus of the derivative pair `U′(a,x) + i UBar′(a,x)` on the real axis. -/
@[dlmf 12.2.E23]
def pcfG (a x : ℝ) : ℝ :=
  ‖pcfUDeriv a x+I*pcfUBarDeriv a x‖

/-- Principal phase representative; a continuous lift differs by integral multiples of two pi. -/
@[dlmf 12.2.E23]
def pcfPsi (a x : ℝ) : ℝ :=
  arg (-(pcfUDeriv a x+I*pcfUBarDeriv a x))

/-- The generalized cylinder equation with nonzero exponent parameter `lam`, evaluated at the
specified argument. -/
@[dlmf 12.15.E1]
def IsGeneralizedCylinderSolution (ν lam : ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  lam ≠ 0 ∧ iteratedDeriv 2 f z+(ν+1/lam-z^lam/lam^2)*f z=0

end DLMF.Confluent
