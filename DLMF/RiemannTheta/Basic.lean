/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.RiemannTheta.Basic.Definitions

/-!
# Riemann theta functions (DLMF §§21.1–21.2)

For a finite index type `ι` (DLMF's genus `g = card ι`), a *Riemann matrix* is a complex
symmetric `ι × ι` matrix whose imaginary part is positive definite (DLMF §21.1); these form
the Siegel upper half-space `siegelUpperHalfSpace ι`. The Riemann theta function
`riemannTheta z Ω = ∑_{n ∈ ℤ^ι} exp(2πi(½ n·Ω·n + n·z))` (DLMF 21.2.1) and the theta function
with real characteristics `riemannThetaChar α β z Ω` (DLMF 21.2.5) are defined as `tsum`s over
the lattice `ι → ℤ`.

The central analytic result of §21.2(i) is proved in `Convergence`: the defining series converges
absolutely, and uniformly on compact subsets of `ℂ^ι × 𝔖_ι`; the limit is continuous there
and holomorphic in each component of `z` and each entry of `Ω`. The proof uses a positive
lower bound for the imaginary quadratic form near a Riemann matrix and a product majorant
built from Mathlib's one-variable bound `summable_pow_mul_jacobiTheta₂_term_bound`.

The `g = 1` case reduces to the one-variable theta functions of DLMF §20.2
(`DLMF.Elliptic.jacobiThetaThreeTau` etc., built on Mathlib's `jacobiTheta₂`), see 21.2.8–12.

`tsum` is totalized: outside the convergence region the defined value is `0`, and all
identities state the hypothesis `Ω ∈ siegelUpperHalfSpace ι` where it is needed.

Analytic properties are proved in `DLMF.RiemannTheta.Convergence`; scaled functions and characteristic identities are developed in `Scaled` and `Characteristics`.
-/
