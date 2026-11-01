/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.Periods

/-!
# Weierstrass zeta, sigma and half-period function definitions

The Weierstrass `ζ` and `σ` functions of a lattice (DLMF 23.2.5–23.2.6) and the DLMF
names for `℘`, `ζ`, `σ`, the invariants, the lattice roots and the constants `η_j` of
half-period data.

## Main definitions

* `weierstrassZeta`, `weierstrassSigma`: the Weierstrass `ζ` and `σ` functions of a period
  pair (DLMF 23.2.5–23.2.6), with abbreviations for half-period data.
* `HalfPeriods.halfPeriod`: the half-periods `ω_j`, `j = 1, 2, 3`.
* `HalfPeriods.weierstrassP`, `HalfPeriods.derivWeierstrassP`: `℘(z|𝕃)` and `℘'(z|𝕃)`.
* `HalfPeriods.g₂`, `HalfPeriods.g₃`: the invariants (DLMF 23.3.1–23.3.2).
* `HalfPeriods.e`: the lattice roots `e_j = ℘(ω_j)` (DLMF 23.3.9).
* `HalfPeriods.eta`: the constants `η_j = ζ(ω_j)` (DLMF 23.2.12).
* `HalfPeriods.latticeDiscriminant`: the discriminant `Δ = g₂³ - 27g₃²` (DLMF 23.3.4).

## Implementation notes

The Weierstrass `℘` and `℘'` are Mathlib's `PeriodPair.weierstrassP` and
`PeriodPair.derivWeierstrassP`; the invariants `g₂ = 60 G₄`, `g₃ = 140 G₆` are Mathlib's
`PeriodPair.g₂`, `PeriodPair.g₃`. Mathlib sums over all lattice points; the `w = 0` term is
`1/z²` in `℘` and vanishes in `G n` (`n ≥ 1`) because `0⁻¹ = 0`, which reproduces DLMF's sums
over `𝕃 ∖ {0}`. The same convention defines `weierstrassZeta` and `weierstrassSigma` here:
the `w = 0` summand of `ζ` is `1/z`, and the `w = 0` factor of the product for `σ` is `1`.
At lattice points the totalized values are junk where DLMF has poles; the theorems state
their domains.
-/

@[expose] public noncomputable section

open Complex PeriodPair
open scoped Real

namespace DLMF.Weierstrass

/-- The Weierstrass zeta function (DLMF 23.2.5)
`ζ(z) = 1/z + ∑_{w ∈ 𝕃∖{0}} (1/(z-w) + 1/w + z/w²)`. The sum runs over all of `𝕃`: by Lean's
`1/0 = 0` the `w = 0` summand is `1/z`. At a lattice point `z = w₀` the summand `1/(z - w₀)`
is `0`, so the value there is the regular part of `ζ` at its pole. -/
@[dlmf 23.2.E5]
def weierstrassZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, (1 / (z - l) + 1 / l + z / l ^ 2)

/-- The Weierstrass sigma function (DLMF 23.2.6)
`σ(z) = z ∏_{w ∈ 𝕃∖{0}} (1 - z/w) exp(z/w + z²/(2w²))`. The product runs over all of `𝕃`:
by Lean's `z/0 = 0` the `w = 0` factor is `1`. -/
@[dlmf 23.2.E6]
def weierstrassSigma (L : PeriodPair) (z : ℂ) : ℂ :=
  z * ∏' l : L.lattice, ((1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2)))

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The half-periods indexed as in DLMF: `ω_j` for `j = 1, 2, 3` (junk `0` otherwise). -/
def halfPeriod : ℕ → ℂ
  | 1 => H.ω₁
  | 2 => H.ω₂
  | 3 => H.ω₃
  | _ => 0

/-- Identity under the stated parameter and domain assumptions: `H.halfPeriod 1 = H.ω₁`. -/
@[simp] theorem halfPeriod_one : H.halfPeriod 1 = H.ω₁ := rfl
/-- Identity under the stated parameter and domain assumptions: `H.halfPeriod 2 = H.ω₂`. -/
@[simp] theorem halfPeriod_two : H.halfPeriod 2 = H.ω₂ := rfl
/-- Identity under the stated parameter and domain assumptions: `H.halfPeriod 3 = H.ω₃`. -/
@[simp] theorem halfPeriod_three : H.halfPeriod 3 = H.ω₃ := rfl

/-- `℘(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassP (z : ℂ) : ℂ := ℘[H.periodPair] z
/-- `℘'(z|𝕃)` for DLMF lattice data. -/
abbrev derivWeierstrassP (z : ℂ) : ℂ := ℘'[H.periodPair] z
/-- `ζ(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassZeta (z : ℂ) : ℂ := DLMF.Weierstrass.weierstrassZeta H.periodPair z
/-- `σ(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassSigma (z : ℂ) : ℂ := DLMF.Weierstrass.weierstrassSigma H.periodPair z
/-- The invariant `g₂` (DLMF 23.3.1), Mathlib's `PeriodPair.g₂`. -/
abbrev g₂ : ℂ := H.periodPair.g₂
/-- The invariant `g₃` (DLMF 23.3.2), Mathlib's `PeriodPair.g₃`. -/
abbrev g₃ : ℂ := H.periodPair.g₃

/-- The lattice roots `e_j = ℘(ω_j)` (DLMF 23.3.9), `j = 1, 2, 3`. -/
@[dlmf 23.3.E9]
def e (j : ℕ) : ℂ := H.weierstrassP (H.halfPeriod j)

/-- The constants `η_j = ζ(ω_j)` (DLMF 23.2.12), `j = 1, 2, 3`. -/
@[dlmf 23.2.E12]
def eta (j : ℕ) : ℂ := H.weierstrassZeta (H.halfPeriod j)

end HalfPeriods

/-- The discriminant `Δ = g₂³ - 27g₃²` of a lattice (DLMF 23.3.4). -/
@[dlmf 23.3.E4]
def latticeDiscriminant (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

end DLMF.Weierstrass
