/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import DLMF.Confluent.Basic

/-!
# Coulomb functions in the variables `r`, `ε`: definitions (DLMF §§33.14–33.20)

DLMF §33.14 reparametrizes the Coulomb wave equation as
`w'' + (ε + 2/r - ℓ(ℓ+1)/r²) w = 0` (33.14.1) with `r = -ηρ`, `ε = 1/η²`, and defines the
regular solution `f(ε,ℓ;r)`, the irregular solution `h(ε,ℓ;r)` and their energy-normalized forms
`s(ε,ℓ;r)`, `c(ε,ℓ;r)`. All of them are real functions of real `ε`, `r` and `ℓ ∈ ℕ`
(except `s`, `c`, which become imaginary when `A(ε,ℓ) < 0`).

## Definitions and conventions

* `coulombKappa ε r`: the quantity `κ` of 33.14.6, with the upper sign `κ = i ε^{-1/2}` for
  `ε > 0` (DLMF: the sign is immaterial). For `ε < 0` the sign follows the sign of `r`
  (`r = 0` takes the `r < 0` branch). At `ε = 0` it is the junk value `0`.
* `coulombfKummer κ ℓ r`: the complex expression `(2r)^{ℓ+1} e^{-r/κ} M(ℓ+1-κ,2ℓ+2,2r/κ)/(2ℓ+1)!`
  of 33.14.5 as a function of `κ`.
* `coulombf ε ℓ r`: for `ε ≠ 0` the real part of `coulombfKummer (coulombKappa ε r) ℓ r`
  (the expression is real, `DLMF.Coulomb.ofReal_coulombf`); for `ε = 0` the confluent limit
  `(2r)^{ℓ+1} ₀F̃₁(;2ℓ+2;-2r)`, which DLMF 33.20.1–33.20.2 identifies with Bessel functions and
  which is the value of the power series 33.19.1 at `ε = 0`.
* `coulombSFactor ε r`: `S(ε,r)` of 33.14.8.
* `coulombhFormula ε ℓ r`: the complex right-hand side of 33.14.7, with Whittaker's functions
  written through Kummer's `M` and Tricomi's `U`
  (`W_{κ,ℓ+1/2}(z) = e^{-z/2} z^{ℓ+1} U(ℓ+1-κ,2ℓ+2,z)`, `M_{κ,ℓ+1/2}` likewise).
* `coulombh ε ℓ r`: the real part of `coulombhFormula`, except at `ε = 0` and at the poles of
  `Γ(ℓ+1-κ)` (`ε = -1/n²`, `n ≥ ℓ+1`, `r > 0`, where 33.14.7 is a removable `∞ · 0`), where it
  is the limit in `ε` along punctured neighbourhoods (DLMF: `h` is analytic in `ε ≠ 0`, and its
  value at `ε = 0` is the limit 33.20.1–33.20.2). Existence of these limits is a theorem.
* `coulombAProd ε ℓ = ∏_{k=0}^{ℓ} (1 + εk²)` (33.14.11), `coulombBFactor ε ℓ` (33.14.10).
* `coulombs`, `coulombc`: complex valued, `s = (B/2)^{1/2} f`, `c = (2B)^{-1/2} h` with principal
  powers (33.14.9), so that they are imaginary when `B < 0`, as DLMF states.
* `turningPointR ε ℓ` (33.14.3) and `hydrogenRadial n ℓ r` (`φ_{n,ℓ}`, 33.14.14).
* `coulombZeta`, `coulombXi`, `coulombKNorm`: `ζ_ℓ(ν,r)`, `ξ_ℓ(ν,r)` of 33.16.9 and `K(ν,ℓ)` of
  33.16.16. The argument `e^{iπ} 2r/ν` of `ξ` is the negative real `-(2r/ν)`, on which the
  principal branch takes `ph = π`.
* `coulombAlpha`, `coulombGammaCoeff`, `coulombBetaCoeff`, `coulombDeltaCoeff`: the coefficients
  `α_k`, `γ_k`, `β_k`, `δ_k` of 33.19.2–33.19.7; `coulombCkp`: `C_{k,p}` of 33.20.6.
-/

@[expose] public section

open Complex Filter
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

/-- The quantity `κ` of DLMF 33.14.6: `(-ε)^{-1/2}` for `ε < 0`, `r > 0`; `-(-ε)^{-1/2}` for
`ε < 0`, `r ≤ 0`; and `i ε^{-1/2}` (upper sign; DLMF: the choice is immaterial) for `ε > 0`.
The value at `ε = 0` (where DLMF leaves `κ` undefined) is `0`. -/
@[dlmf 33.14.E6]
def coulombKappa (ε r : ℝ) : ℂ :=
  if ε < 0 then (if 0 < r then (((-ε) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    else ((-((-ε) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))
  else I * ((ε ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- The Kummer form `(2r)^{ℓ+1} e^{-r/κ} M(ℓ+1-κ, 2ℓ+2, 2r/κ) / (2ℓ+1)!` of DLMF 33.14.5, as a
function of `κ`. -/
def coulombfKummer (κ : ℂ) (ℓ : ℕ) (r : ℝ) : ℂ :=
  (2 * r : ℂ) ^ (ℓ + 1) * exp (-(r : ℂ) / κ) *
    kummerM (ℓ + 1 - κ) (2 * ℓ + 2) (2 * r / κ) / (2 * ℓ + 1)!

/-- **The regular Coulomb function** `f(ε,ℓ;r)` (DLMF 33.14.4–33.14.5), for real `ε`, `r` and
`ℓ ∈ ℕ`: for `ε ≠ 0` the (real) value of `(2r)^{ℓ+1} e^{-r/κ} M(ℓ+1-κ,2ℓ+2,2r/κ)/(2ℓ+1)!` with
`κ` from 33.14.6, and for `ε = 0` its confluent limit `(2r)^{ℓ+1} ₀F̃₁(;2ℓ+2;-2r)`
(equal to `(2r)^{1/2} J_{2ℓ+1}((8r)^{1/2})` for `r > 0`, DLMF 33.20.1). -/
@[dlmf 33.14.E5]
def coulombf (ε : ℝ) (ℓ : ℕ) (r : ℝ) : ℝ :=
  if ε = 0 then ((2 * r : ℂ) ^ (ℓ + 1) *
      regularizedHGFun 0 {(2 * ℓ + 2 : ℂ)} (-(2 * r))).re
  else (coulombfKummer (coulombKappa ε r) ℓ r).re

/-- The function `S(ε,r)` of DLMF 33.14.8: `2 cos(π|ε|^{-1/2})` (`ε < 0`, `r > 0`), `0`
(`ε < 0`, `r ≤ 0`), `exp(πε^{-1/2})` (`ε > 0`, `r > 0`), `exp(-πε^{-1/2})` (`ε > 0`,
`r ≤ 0`). DLMF leaves `r = 0` and `ε = 0` undefined. -/
@[dlmf 33.14.E8]
def coulombSFactor (ε r : ℝ) : ℝ :=
  if ε < 0 then (if 0 < r then 2 * Real.cos (π * |ε| ^ (-(1 / 2 : ℝ))) else 0)
  else if 0 < r then Real.exp (π * ε ^ (-(1 / 2 : ℝ)))
  else Real.exp (-(π * ε ^ (-(1 / 2 : ℝ))))

/-- The bracketed Whittaker form of DLMF 33.14.7 as a function of `κ` and of the value `S` of
`S(ε,r)`: `Γ(ℓ+1-κ)/(π κ^ℓ) (W_{κ,ℓ+1/2}(2r/κ) + (-1)^ℓ S Γ(ℓ+1+κ)/(2(2ℓ+1)!) M_{κ,ℓ+1/2}(2r/κ))`,
with `W_{κ,ℓ+1/2}(z) = e^{-z/2} z^{ℓ+1} U(ℓ+1-κ,2ℓ+2,z)` and
`M_{κ,ℓ+1/2}(z) = e^{-z/2} z^{ℓ+1} M(ℓ+1-κ,2ℓ+2,z)` (DLMF 13.14.2–13.14.3, principal branch). -/
def coulombhKappa (κ : ℂ) (S : ℝ) (ℓ : ℕ) (r : ℝ) : ℂ :=
  Gamma (ℓ + 1 - κ) / (π * κ ^ ℓ) *
    (exp (-(2 * r / κ) / 2) * (2 * r / κ) ^ (ℓ + 1) * kummerU (ℓ + 1 - κ) (2 * ℓ + 2) (2 * r / κ) +
      (-1) ^ ℓ * S * Gamma (ℓ + 1 + κ) / (2 * (2 * ℓ + 1)!) *
        (exp (-(2 * r / κ) / 2) * (2 * r / κ) ^ (ℓ + 1) *
          kummerM (ℓ + 1 - κ) (2 * ℓ + 2) (2 * r / κ)))

/-- The complex right-hand side of DLMF 33.14.7 with `κ` from 33.14.6 and `S(ε,r)` from
33.14.8. -/
def coulombhFormula (ε : ℝ) (ℓ : ℕ) (r : ℝ) : ℂ :=
  coulombhKappa (coulombKappa ε r) (coulombSFactor ε r) ℓ r

/-- **The irregular Coulomb function** `h(ε,ℓ;r)` (DLMF 33.14.7), for real `ε`, `r ≠ 0`:
the real part of `coulombhFormula ε ℓ r`, except at `ε = 0` and at the poles of `Γ(ℓ+1-κ)`
(`ε = -1/n²` with `n ≥ ℓ+1` and `r > 0`), where 33.14.7 is a removable `∞ · 0` and `h` is the limit
of the formula as `ε` tends to the point (DLMF §33.14(iii): `h` is analytic in `ε ≠ 0`;
33.20.1–33.20.2 give the value at `ε = 0`). The value at `r = 0` is junk. -/
@[dlmf 33.14.E7]
def coulombh (ε : ℝ) (ℓ : ℕ) (r : ℝ) : ℝ := by
  classical
  exact if ε = 0 ∨ ∃ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r = -(m : ℂ) then
    limUnder (𝓝[≠] ε) (fun e => (coulombhFormula e ℓ r).re)
  else (coulombhFormula ε ℓ r).re

/-- `A(ε,ℓ) = ∏_{k=0}^{ℓ} (1 + εk²)` (DLMF 33.14.11). -/
@[dlmf 33.14.E11]
def coulombAProd (ε : ℝ) (ℓ : ℕ) : ℝ := ∏ k ∈ Finset.range (ℓ + 1), (1 + ε * (k : ℝ) ^ 2)

/-- `B(ε,ℓ) = A(ε,ℓ) (1 - exp(-2π/ε^{1/2}))^{-1}` for `ε > 0` and `A(ε,ℓ)` for `ε ≤ 0`
(DLMF 33.14.10). -/
@[dlmf 33.14.E10]
def coulombBFactor (ε : ℝ) (ℓ : ℕ) : ℝ :=
  if 0 < ε then coulombAProd ε ℓ / (1 - Real.exp (-(2 * π / Real.sqrt ε)))
  else coulombAProd ε ℓ

/-- **The energy-normalized regular Coulomb function** `s(ε,ℓ;r) = (B(ε,ℓ)/2)^{1/2} f(ε,ℓ;r)`
(DLMF 33.14.9), complex valued with the principal square root: it is imaginary when
`B(ε,ℓ) < 0` (DLMF §33.14(iv)). -/
@[dlmf 33.14.E9]
def coulombs (ε : ℝ) (ℓ : ℕ) (r : ℝ) : ℂ :=
  ((coulombBFactor ε ℓ / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) * coulombf ε ℓ r

/-- **The energy-normalized irregular Coulomb function** `c(ε,ℓ;r) = (2B(ε,ℓ))^{-1/2} h(ε,ℓ;r)`
(DLMF 33.14.9), complex valued with the principal power; junk (`0`) when `B(ε,ℓ) = 0`. -/
@[dlmf 33.14.E9]
def coulombc (ε : ℝ) (ℓ : ℕ) (r : ℝ) : ℂ :=
  ((2 * coulombBFactor ε ℓ : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) * coulombh ε ℓ r

/-- The outer turning point `r_tp(ε,ℓ) = ((1 + εℓ(ℓ+1))^{1/2} - 1)/ε` of 33.14.1, for `ε > 0`
(DLMF 33.14.3). -/
@[dlmf 33.14.E3]
def turningPointR (ε : ℝ) (ℓ : ℕ) : ℝ := (Real.sqrt (1 + ε * (ℓ * (ℓ + 1))) - 1) / ε

/-- The hydrogenic radial function
`φ_{n,ℓ}(r) = (-1)^{ℓ+1+n} (2/n³)^{1/2} s(-1/n², ℓ; r)` (DLMF 33.14.14), written with the real
square root `(B/2)^{1/2}` of `s`; for `n ≥ ℓ+1`, the range in DLMF, `B(-1/n²,ℓ) > 0` and this is
exactly DLMF's `φ_{n,ℓ}` (`DLMF.Coulomb.hydrogenRadial_eq_coulombs`). -/
@[dlmf 33.14.E14]
def hydrogenRadial (n ℓ : ℕ) (r : ℝ) : ℝ :=
  (-1) ^ (ℓ + 1 + n) * Real.sqrt (2 / (n : ℝ) ^ 3) *
    Real.sqrt (coulombBFactor (-1 / (n : ℝ) ^ 2) ℓ / 2) * coulombf (-1 / (n : ℝ) ^ 2) ℓ r

/-- `ζ_ℓ(ν,r) = W_{ν,ℓ+1/2}(2r/ν)` (DLMF 33.16.9), written as
`e^{-z/2} z^{ℓ+1} U(ℓ+1-ν, 2ℓ+2, z)` with `z = 2r/ν` (principal branch). -/
@[dlmf 33.16.E9]
def coulombZeta (ℓ : ℕ) (ν r : ℝ) : ℂ :=
  exp (-(2 * r / ν : ℂ) / 2) * (2 * r / ν : ℂ) ^ (ℓ + 1) *
    kummerU (ℓ + 1 - ν) (2 * ℓ + 2) (2 * r / ν)

/-- `ξ_ℓ(ν,r) = Re(e^{iπν} W_{-ν,ℓ+1/2}(e^{iπ} 2r/ν))` (DLMF 33.16.9). The argument
`e^{iπ} 2r/ν` is the complex number `-(2r/ν)`; for `2r/ν > 0` it lies on the negative real axis,
where the principal branch takes `ph = π` (the value from the upper half-plane), as DLMF's
`e^{iπ}` prescribes. -/
@[dlmf 33.16.E9]
def coulombXi (ℓ : ℕ) (ν r : ℝ) : ℝ :=
  (exp (I * π * ν) *
    (exp (-(-(2 * r / ν : ℂ)) / 2) * (-(2 * r / ν : ℂ)) ^ (ℓ + 1) *
      kummerU (ℓ + 1 + ν) (2 * ℓ + 2) (-(2 * r / ν : ℂ)))).re

/-- `K(ν,ℓ) = (ν² Γ(ν+ℓ+1) Γ(ν-ℓ))^{-1/2}` (DLMF 33.16.16), with the real power; it is the
intended value when `Γ(ν-ℓ) > 0`, that is when `A(-1/ν², ℓ) > 0`. -/
@[dlmf 33.16.E16]
def coulombKNorm (ν : ℝ) (ℓ : ℕ) : ℝ :=
  (ν ^ 2 * Real.Gamma (ν + ℓ + 1) * Real.Gamma (ν - ℓ)) ^ (-(1 / 2 : ℝ))

/-- The coefficients `α_k` of the power series 33.19.1 of `f(ε,ℓ;r)` (DLMF 33.19.2):
`α₀ = 2^{ℓ+1}/(2ℓ+1)!`, `α₁ = -α₀/(ℓ+1)` and
`k(k+2ℓ+1) α_k + 2α_{k-1} + εα_{k-2} = 0` for `k ≥ 2`. -/
@[dlmf 33.19.E2]
def coulombAlpha (ε : ℝ) (ℓ : ℕ) : ℕ → ℝ
  | 0 => 2 ^ (ℓ + 1) / (2 * ℓ + 1)!
  | 1 => -(2 ^ (ℓ + 1) / (2 * ℓ + 1)!) / (ℓ + 1)
  | k + 2 => -(2 * coulombAlpha ε ℓ (k + 1) + ε * coulombAlpha ε ℓ k) /
      (((k : ℝ) + 2) * ((k : ℝ) + 2 + 2 * ℓ + 1))

/-- The coefficients `γ_k` of DLMF 33.19.3–33.19.4: `γ₀ = γ₁ = 1` and
`γ_k - γ_{k-1} + (1/4)(k-1)(k-2ℓ-2) ε γ_{k-2} = 0` for `k ≥ 2`. -/
@[dlmf 33.19.E4]
def coulombGammaCoeff (ε : ℝ) (ℓ : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | k + 2 => coulombGammaCoeff ε ℓ (k + 1) -
      ((k : ℝ) + 1) * ((k : ℝ) + 2 - 2 * ℓ - 2) * ε * coulombGammaCoeff ε ℓ k / 4

/-- The coefficients `β_k` of DLMF 33.19.7: `β₀ = β₁ = 0` and
`β_k - β_{k-1} + (1/4)(k-1)(k-2ℓ-2) ε β_{k-2} + (1/2)(k-1) ε γ_{k-2} = 0` for `k ≥ 2`. -/
@[dlmf 33.19.E7]
def coulombBetaCoeff (ε : ℝ) (ℓ : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | k + 2 => coulombBetaCoeff ε ℓ (k + 1) -
      ((k : ℝ) + 1) * ((k : ℝ) + 2 - 2 * ℓ - 2) * ε * coulombBetaCoeff ε ℓ k / 4 -
      ((k : ℝ) + 1) * ε * coulombGammaCoeff ε ℓ k / 2

/-- The coefficients `δ_k` of DLMF 33.19.5–33.19.6:
`δ₀ = (β_{2ℓ+1} - 2(ψ(2ℓ+2) + ψ(1)) A(ε,ℓ)) α₀`, `δ₁ = (β_{2ℓ+2} - 2(ψ(2ℓ+3) + ψ(2)) A(ε,ℓ)) α₁`
and `k(k+2ℓ+1) δ_k + 2δ_{k-1} + εδ_{k-2} + 2(2k+2ℓ+1) A(ε,ℓ) α_k = 0` for `k ≥ 2`. -/
@[dlmf 33.19.E5]
def coulombDeltaCoeff (ε : ℝ) (ℓ : ℕ) : ℕ → ℝ
  | 0 => (coulombBetaCoeff ε ℓ (2 * ℓ + 1) -
      2 * (digamma (2 * ℓ + 2) + digamma 1).re * coulombAProd ε ℓ) * coulombAlpha ε ℓ 0
  | 1 => (coulombBetaCoeff ε ℓ (2 * ℓ + 2) -
      2 * (digamma (2 * ℓ + 3) + digamma 2).re * coulombAProd ε ℓ) * coulombAlpha ε ℓ 1
  | k + 2 => -(2 * coulombDeltaCoeff ε ℓ (k + 1) + ε * coulombDeltaCoeff ε ℓ k +
      2 * (2 * ((k : ℝ) + 2) + 2 * ℓ + 1) * coulombAProd ε ℓ * coulombAlpha ε ℓ (k + 2)) /
      (((k : ℝ) + 2) * ((k : ℝ) + 2 + 2 * ℓ + 1))

/-- The coefficients `C_{k,p}` of DLMF 33.20.6: `C_{0,0} = 1`, `C_{k,p} = 0` unless
`2k ≤ p ≤ 3k`, and `C_{k,p} = (-(2ℓ+p) C_{k-1,p-2} + C_{k-1,p-3})/(4p)` for `k > 0`,
`2k ≤ p ≤ 3k` (terms with negative second index are `0`). -/
@[dlmf 33.20.E6]
def coulombCkp (ℓ : ℕ) : ℕ → ℕ → ℝ
  | 0, p => if p = 0 then 1 else 0
  | k + 1, p => if 2 * (k + 1) ≤ p ∧ p ≤ 3 * (k + 1) then
      (-(2 * (ℓ : ℝ) + p) * (if 2 ≤ p then coulombCkp ℓ k (p - 2) else 0) +
        (if 3 ≤ p then coulombCkp ℓ k (p - 3) else 0)) / (4 * p)
    else 0

end DLMF.Coulomb
