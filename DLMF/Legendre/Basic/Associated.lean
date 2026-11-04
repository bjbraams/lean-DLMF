/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic.Functions

/-!
# Associated Legendre, Ferrers and conical functions (DLMF §§14.3, 14.20)

## Main definitions

* `legendreBranchPower`: the power `(z² - 1)^{c/2}`, continued from `z > 1`.
* `associatedP`: `P^μ_ν(z) = ((z+1)/(z-1))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-z)/2)` (DLMF 14.3.6).
* `olverQ`: Olver's `𝑸^μ_ν` (DLMF 14.3.10), regularized before multiplying by Gamma so that
  exceptional parameters are retained.
* `associatedQ`: the classical `Q^μ_ν` (DLMF 14.3.7).
* `LegendreQRegular`: the condition `ν + μ ∉ {-1, -2, …}`.
* `ferrersW1`, `ferrersW2`: the auxiliary functions `w₁`, `w₂` of DLMF 14.3.13–14.3.14.
* `ferrersQ`: the Ferrers function `𝖰^μ_ν` (DLMF 14.3.12).
* `conicalP`, `conicalQHat`: the conical function `𝖯^{-μ}_{-1/2+iτ}` and Dunster's companion
  `𝖰̂^{-μ}_{-1/2+iτ}` (DLMF 14.20.2).

## Implementation notes

The representation of `𝖰^μ_ν` through `w₁` and `w₂` supplies integer-order values without
division by `sin(μπ)`. The properties of these functions are in `DLMF.Legendre.Associated` and
`DLMF.Legendre.Conical`.
-/

@[expose] public noncomputable section

open Complex DLMF.Hypergeometric

open scoped Real

namespace DLMF.Legendre

/-- The inherited power of z squared minus one, continued from z greater than one. -/
def legendreBranchPower (μ z : ℂ) : ℂ :=
  exp (μ/2*(log (z-1)+log (z+1)))

/-- DLMF 14.3.6: the associated Legendre function of the first kind, `P^μ_ν(z) =
((z+1)/(z-1))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-z)/2)` with principal branches and the regularized
hypergeometric function `𝐅`. -/
@[dlmf 14.3.E6]
def associatedP (ν μ z : ℂ) : ℂ :=
  exp (μ/2*(log (z+1)-log (z-1)))*regularizedGaussHypergeometric (ν+1) (-ν) (1-μ) ((1-z)/2)

/-- Olver Q is regularized before multiplying by Gamma, so exceptional parameters are retained. -/
@[dlmf 14.3.E10]
def olverQ (ν μ z : ℂ) : ℂ :=
  Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*z^(ν+μ+1))*
    regularizedGaussHypergeometric ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2)

/-- Classical associated Q, defined mathematically when degree plus order is not a negative
integer. -/
@[dlmf 14.3.E7]
def associatedQ (ν μ z : ℂ) : ℂ :=
  exp (μ*π*I)*Gamma (ν+μ+1)*olverQ ν μ z

/-- The parameter condition `ν + μ ∉ {-1, -2, -3, …}` under which the classical `Q^μ_ν` and Ferrers
`𝖰^μ_ν` are defined. -/
def LegendreQRegular (ν μ : ℂ) : Prop :=
  ∀ n : ℕ, ν+μ ≠ -(n+1)

/-- DLMF 14.3.13: the even Ferrers auxiliary function `w₁(ν, μ, x) = 2^μ Γ((ν+μ+1)/2)/Γ((ν-μ+2)/2)
(1-x²)^{-μ/2} 𝐅(-(ν+μ)/2, (ν-μ+1)/2; 1/2; x²)`. -/
@[dlmf 14.3.E13]
def ferrersW1 (ν μ : ℂ) (x : ℝ) : ℂ :=
  2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)*(1-x^2:ℂ)^(-μ/2)*
    regularizedGaussHypergeometric (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) (x^2)

/-- DLMF 14.3.14: the odd Ferrers auxiliary function `w₂(ν, μ, x) = 2^μ Γ((ν+μ+2)/2)/Γ((ν-μ+1)/2) x
(1-x²)^{-μ/2} 𝐅((1-ν-μ)/2, (ν-μ+2)/2; 3/2; x²)`. -/
@[dlmf 14.3.E14]
def ferrersW2 (ν μ : ℂ) (x : ℝ) : ℂ :=
  2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)*x*(1-x^2:ℂ)^(-μ/2)*
    regularizedGaussHypergeometric ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) (x^2)

/-- This representation supplies integer-order limiting values without division by sin of the
order. -/
@[dlmf 14.3.E12]
def ferrersQ (ν μ : ℂ) (x : ℝ) : ℂ :=
  -π/2*sin ((ν+μ)*π/2)*ferrersW1 ν μ x+π/2*cos ((ν+μ)*π/2)*ferrersW2 ν μ x

/-- The conical Ferrers function `𝖯^{-μ}_{-1/2+iτ}(x)`, i.e. `ferrersP (-1/2 + iτ) (-μ) x`, for real
`τ, μ, x`. -/
def conicalP (τ μ x : ℝ) : ℂ :=
  ferrersP (-1/2+I*τ) (-μ) x

/-- Dunster’s conical companion; the order is minus the parameter μ. -/
@[dlmf 14.20.E2]
def conicalQHat (τ μ x : ℝ) : ℂ :=
  ((exp (μ*π*I)*ferrersQ (-1/2+I*τ) (-μ) x).re:ℂ)-π/2*Real.sin (μ*π)*conicalP τ μ x

end DLMF.Legendre
