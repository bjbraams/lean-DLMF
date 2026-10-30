/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.Basic.IncompleteGamma
public import DLMF.Core.Framework

/-!
# Continued incomplete Gamma functions: definitions

The logarithmic-plane versions and the continued normalized functions `P` and `Q`
are defined here. Their analytic and differential properties are in
`DLMF.IncompleteGamma.ContinuedProperties`.
-/

@[expose] public noncomputable section

open Complex DLMF.Statistical DLMF
open scoped Real Topology Nat

namespace DLMF.Confluent

/-- Upper incomplete Gamma on the logarithmic plane, also at integral a. -/
def upperIncGammaOnLog (a w : ℂ) : ℂ :=
  upperIncGamma a (exp w) - segmentIntegral (fun u => exp (a*u-exp u)) (log (exp w)) w

/-- Lower incomplete Gamma on the logarithmic plane away from its parameter poles. -/
def lowerIncGammaOnLog (a w : ℂ) : ℂ :=
  Gamma a*exp (a*w)*scIncGamma a (exp w)

/-- Analytically continued P; at nonpositive integral a it differs from the old totalized quotient. -/
@[dlmf 8.2.E4]
def normIncGammaPContinued (a z : ℂ) : ℂ :=
  z^a*scIncGamma a z

/-- Analytically continued Q. -/
@[dlmf 8.2.E4]
def normIncGammaQContinued (a z : ℂ) : ℂ :=
  1-normIncGammaPContinued a z

/-- Continued P on the logarithmic plane. -/
def normIncGammaPOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*scIncGamma a (exp w)

/-- Continued Q on the logarithmic plane. -/
def normIncGammaQOnLog (a w : ℂ) : ℂ :=
  1-normIncGammaPOnLog a w

end DLMF.Confluent
