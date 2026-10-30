/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.Tricomi

/-!
# Lower and upper incomplete-gamma normalizations
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric

namespace DLMF.Confluent

/-- Lower incomplete gamma via `₁F₁`, AAR §4.4:
`γ(s,z) = z^s / s · M(s, s+1, -z)`. -/
@[dlmf 13.6.E5]
def lowerIncGamma (s z : ℂ) : ℂ :=
  z ^ s / s * kummerM s (s + 1) (-z)
/-- Upper incomplete gamma via Tricomi's `U`, from DLMF 13.6.6. -/
def upperIncGamma (s z : ℂ) : ℂ := exp (-z) * kummerU (1 - s) (1 - s) z

end DLMF.Confluent
