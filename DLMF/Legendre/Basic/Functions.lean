/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Hypergeometric.Basic.PrincipalBranch

/-!
# Legendre and Ferrers functions in the hypergeometric normalization
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric

namespace DLMF.Legendre

/-- Legendre function of the first kind `P_ν(z) = F(-ν, ν+1; 1; (1-z)/2)`, analytic off
`(-∞, -1]` (DLMF 14.3.6 with `μ = 0`, Temme (8.5)). -/
@[dlmf 14.3.E6]
def legendreP (ν z : ℂ) : ℂ := regularizedGaussHG (-ν) (ν + 1) 1 ((1 - z) / 2)

/-- The Ferrers function of the first kind on `(-1, 1)`,
`𝖯^μ_ν(x) = ((1+x)/(1-x))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-x)/2)` (DLMF 14.3.1). -/
@[dlmf 14.3.E1]
def ferrersP (ν μ : ℂ) (x : ℝ) : ℂ :=
  (((1 + x) / (1 - x) : ℝ) : ℂ) ^ (μ / 2) * regularizedGaussHG (ν + 1) (-ν) (1 - μ) ((1 - x) / 2)

end DLMF.Legendre
