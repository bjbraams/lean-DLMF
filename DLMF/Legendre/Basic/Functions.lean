/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMF.Hypergeometric.Basic.PrincipalBranch

/-!
# Legendre and Ferrers functions in the hypergeometric normalization

## Main definitions

* `legendreP`: the Legendre function of the first kind `P_ν(z) = F(-ν, ν+1; 1; (1-z)/2)`,
  analytic off `(-∞, -1]` (DLMF 14.3.6 with `μ = 0`).
* `ferrersP`: the Ferrers function of the first kind on `(-1, 1)`,
  `𝖯^μ_ν(x) = ((1+x)/(1-x))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-x)/2)` (DLMF 14.3.1).
* `legendreQ`: the Legendre function of the second kind
  `Q_ν(z) = √π Γ(ν+1) (2z)^{-ν-1} 𝐅((ν+2)/2, (ν+1)/2; ν+3/2; 1/z²)` (DLMF 14.3.7 with `μ = 0`).
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric

namespace DLMF.Legendre

/-- Legendre function of the first kind `P_ν(z) = F(-ν, ν+1; 1; (1-z)/2)`, analytic off
`(-∞, -1]` (DLMF 14.3.6 with `μ = 0`, Temme (8.5)). -/
@[dlmf 14.3.E6]
def legendreP (ν z : ℂ) : ℂ := regularizedGaussHypergeometric (-ν) (ν + 1) 1 ((1 - z) / 2)

/-- The Ferrers function of the first kind on `(-1, 1)`,
`𝖯^μ_ν(x) = ((1+x)/(1-x))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-x)/2)` (DLMF 14.3.1). -/
@[dlmf 14.3.E1]
def ferrersP (ν μ : ℂ) (x : ℝ) : ℂ :=
  (((1 + x) / (1 - x) : ℝ) : ℂ) ^ (μ / 2) *
      regularizedGaussHypergeometric (ν + 1) (-ν) (1 - μ) ((1 - x) / 2)

/-- Legendre function of the second kind
`Q_ν(z) = √π Γ(ν+1) (2z)^{-ν-1} 𝐅((ν+2)/2, (ν+1)/2; ν+3/2; 1/z²)`, analytic off `(-∞, 1]`
(DLMF 14.3.7 with `μ = 0`, Temme (8.8)). -/
@[dlmf 14.3.E7]
def legendreQ (ν z : ℂ) : ℂ :=
  (Real.sqrt π * Gamma (ν + 1) * 2 ^ (-(ν + 1))) *
    (z ^ (-(ν + 1)) * regularizedGaussHypergeometric ((ν + 2) / 2) ((ν + 1) / 2)
        (ν + 3 / 2) (1 / z ^ 2))

end DLMF.Legendre
