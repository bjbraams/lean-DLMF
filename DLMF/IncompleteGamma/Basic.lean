/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.Basic.IncompleteGamma
public import DLMF.Core.Basic
public import DLMF.IncompleteGamma.Basic.IncompleteBeta

/-!
# Continued incomplete Gamma functions: definitions

The incomplete Gamma functions on the logarithmic plane and the continued normalized functions
`P` and `Q`. Their analytic and differential properties are in
`DLMF.IncompleteGamma.ContinuedProperties`.

## Main definitions

* `upperIncompleteGammaOnLog`, `lowerIncompleteGammaOnLog`: the incomplete Gamma functions on the
  logarithmic plane.
* `regularizedGammaOnLog`, `regularizedIncompleteGammaQOnLog`: the continued `P` and `Q` on the
  logarithmic plane.
* `regularizedGamma`, `regularizedIncompleteGammaQ`: the analytically continued `P` and `Q`,
  DLMF 8.2.4.

The continued incomplete Beta functions `incompleteBeta` and `regularizedIncompleteBeta` (DLMF
§8.17) are defined in `DLMF.IncompleteGamma.Basic.IncompleteBeta`.
-/

@[expose] public noncomputable section

open Complex DLMF.Statistical DLMF
open scoped Real Topology Nat

open DLMF.Core

namespace DLMF.Confluent

/-- Upper incomplete Gamma on the logarithmic plane, also at integral a. -/
def upperIncompleteGammaOnLog (a w : ℂ) : ℂ :=
  upperIncompleteGamma a (exp w) - segmentIntegral (fun u => exp (a*u-exp u)) (log (exp w)) w

/-- Lower incomplete Gamma on the logarithmic plane away from its parameter poles. -/
def lowerIncompleteGammaOnLog (a w : ℂ) : ℂ :=
  Gamma a*exp (a*w)*tricomiIncompleteGamma a (exp w)

/-- The analytically continued `P(a, z) = z^a γ*(a, z)` (DLMF 8.2.4, 8.2.7), entire in `a`.
Away from nonpositive integral `a` it is the quotient `γ(a,z)/Γ(a)`; at `a = -n` and `z ≠ 0` it
takes the limiting value `1`. -/
@[dlmf 8.2.E4]
def regularizedGamma (a z : ℂ) : ℂ :=
  z^a*tricomiIncompleteGamma a z

/-- Analytically continued Q. -/
@[dlmf 8.2.E4]
def regularizedIncompleteGammaQ (a z : ℂ) : ℂ :=
  1-regularizedGamma a z

/-- Continued P on the logarithmic plane. -/
def regularizedGammaOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*tricomiIncompleteGamma a (exp w)

/-- Continued Q on the logarithmic plane. -/
def regularizedIncompleteGammaQOnLog (a w : ℂ) : ℂ :=
  1-regularizedGammaOnLog a w

end DLMF.Confluent
