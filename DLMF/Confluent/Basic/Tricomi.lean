/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerM
public import TauCeti.Analysis.SpecialFunctions.Erf
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Tricomi's function `U`

This file defines Tricomi's confluent hypergeometric function `U(a,b,z)` on the principal
branch through the connection formula DLMF 13.2.42.

## Main definitions

* `kummerUConnection`: the connection formula in terms of Kummer's `M`, valid at noninteger `b`.
* `kummerU`: Tricomi's function; at integer `b` it is the limit of the connection formula along
  noninteger parameters.
* `kummerUOnLog`: the connection formula on the logarithmic argument plane, with `w` a
  logarithm of the argument.

## Main results

* `kummerU_eq_connection`: `kummerU` agrees with the connection formula at noninteger `b`.

## Implementation notes

At integer `b` the totalized Gamma factors in the connection formula do not give the continued
value, so `kummerU` uses `limUnder` there. The definition alone does not establish that the
limit exists; that is `tendsto_kummerUConnection` in `DLMF.Confluent.BasicProperties.Continuity`.
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric

namespace DLMF.Confluent

/-- The connection formula for Tricomi's function at noninteger second parameter.
At integers, totalized Gamma factors do not give the continued value. -/
def kummerUConnection (a b z : ℂ) : ℂ :=
  Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z +
    Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z

/-- Tricomi's principal-branch function, with integer second parameters assigned
by limits of the connection formula along noninteger parameters.
The definition alone does not establish existence of these limits; a `Tendsto`
theorem is required when using the integer branch. -/
@[dlmf 13.2.E42]
def kummerU (a b z : ℂ) : ℂ := by
  classical
  exact if ∀ k : ℤ, b ≠ k then kummerUConnection a b z else
    Filter.limUnder (𝓝[integerComplement] b) (fun c => kummerUConnection a c z)

/-- The noninteger connection formula on the logarithmic argument plane.
The variable `w` represents a logarithm of the actual argument `exp w`. -/
def kummerUOnLog (a b w : ℂ) : ℂ :=
  Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (exp w) +
    Gamma (b - 1) / Gamma a * exp ((1 - b) * w) *
      kummerM (a - b + 1) (2 - b) (exp w)
/-- Tricomi's function agrees with its connection formula at noninteger parameters. -/
theorem kummerU_eq_connection (a b z : ℂ) (hb : ∀ k : ℤ, b ≠ k) :
    kummerU a b z = kummerUConnection a b z := by
  simp [kummerU, hb]

end DLMF.Confluent
