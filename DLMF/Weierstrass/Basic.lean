/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Weierstrass.Basic.LatticesAndSigma
public import DLMF.Weierstrass.Basic.EllipticFunctionsAndInvariants

/-!
# Weierstrass lattices, `℘`, `ζ` and `σ` (DLMF §§23.2–23.3(i))

DLMF describes a lattice `𝕃` by half-periods `ω₁, ω₃` with `ℑ(ω₃/ω₁) > 0`; the lattice
generators are `2ω₁, 2ω₃` and `ω₂ = -ω₁ - ω₃` (23.2.1). Mathlib's `PeriodPair` instead stores
the *full* periods `ω₁, ω₂` (with no orientation condition). The structure `HalfPeriods`
records DLMF's data and `HalfPeriods.periodPair` is the bridge: its Mathlib periods are
`2ω₁` and `2ω₃`. Mathlib's names for full periods are therefore *not* DLMF's names; in this
area `H.ω₁, H.ω₂, H.ω₃` always denote DLMF's half-periods.

The Weierstrass `℘` and `℘'` are Mathlib's `PeriodPair.weierstrassP` and
`PeriodPair.derivWeierstrassP`; the invariants `g₂ = 60 G₄`, `g₃ = 140 G₆` are Mathlib's
`PeriodPair.g₂`, `PeriodPair.g₃`. Mathlib sums over all lattice points; the `w = 0` term is
`1/z²` in `℘` and vanishes in `G n` (`n ≥ 1`) because `0⁻¹ = 0`, which reproduces DLMF's sums
over `𝕃 ∖ {0}`. The same convention defines `weierstrassZeta` (23.2.5) and
`weierstrassSigma` (23.2.6) here: the `w = 0` summand of `ζ` is `1/z`, and the `w = 0` factor
of the product for `σ` is `1`. At lattice points the totalized values are junk where DLMF has
poles; every statement below states its domain.

The invariants-form `℘(z; g₂, g₃)` (23.3.8) is defined through a chosen lattice with the given
invariants; it agrees with `℘(z|𝕃)` for every lattice with those invariants, which uses the
(admitted) uniqueness of the lattice.
-/
