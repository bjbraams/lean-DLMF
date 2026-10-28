/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Basic.Definitions
public import DLMF.JacobiElliptic.Basic.QuarterPeriods
public import DLMF.JacobiElliptic.Basic.ModulusInversion
public import DLMF.JacobiElliptic.Basic.AnalyticProperties

/-!
# Jacobian elliptic functions: definitions (DLMF §22.2)

DLMF 22.2 defines the twelve Jacobian elliptic functions `pq(z, k)` (Glaisher's notation:
`p, q ∈ {s, c, d, n}`, `pp = 1`) as quotients of theta functions with nome
`q = exp(-π K'(k)/K(k))` and argument `ζ = π z/(2K(k))`.

## Design

* **Letters.** `JacobiLetter` has the four Glaisher letters `s, c, d, n`. For each letter
  `jacobiLetterTheta p ζ τ` is the normalized theta function
  `θ_s = θ₃(0)/(θ₂(0)θ₄(0)) θ₁(ζ)`, `θ_c = θ₂(ζ)/θ₂(0)`, `θ_d = θ₃(ζ)/θ₃(0)`, `θ_n = θ₄(ζ)/θ₄(0)`
  (all `θ_j(·|τ)` are the project's `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`).
  By Jacobi's `θ₁'(0) = θ₂(0)θ₃(0)θ₄(0)` (DLMF 20.4.6) these are Neville's theta functions of
  §20.1, so `jacobiGlaisher p q ζ τ = θ_p/θ_q` (`= 1` when `p = q`) is DLMF 22.2.11, and the
  constants reproduce DLMF 22.2.4–22.2.9 exactly. Each `pq` is a *reduced* theta quotient, so its
  removable singularities are filled in (e.g. `sd` is finite where `sn` and `dn` have poles).
  Poles carry Lean's junk value `x / 0 = 0`.
* **Lattice form.** `jacobiPQTau p q z τ` uses `τ` (`Im τ > 0`) as the primary parameter, with
  `k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²/θ₃²`, `K = (π/2)θ₃²(0|τ)`, `K' = -iτK` (DLMF 22.2.2,
  22.2.12) and `ζ = πz/(2K)`. All identities that follow from theta-function identities are
  proved in this form.
* **Modulus form.** `jacobiPQk p q z k` is DLMF's literal definition for complex `z` and `k`:
  `K(k) = compEllIntKk k` is the principal-branch integral 19.2.8,
  `K'(k) = compEllIntKpk k = K(√(1-k²))`, `τ = iK'/K` (22.2.12), `q = e^{iπτ}` (22.2.1) and
  `ζ = πz/(2K)` (22.2.3). DLMF's identities (with literal `k`, `k' = √(1-k²)`) hold on
  `jacobiModulusDomain = {Re k > 0} \ [1, ∞)`, where `k² ∈ ℂ \ ((-∞, 0] ∪ [1, ∞))`; there the
  inversion 22.2.2 is the theorem `jacobi_inversion_k`. On the other side of the
  imaginary axis the definition depends only on `k²`, so it gives the functions of `-k`.
* **Real functions.** The existing real-variable `DLMF.Elliptic.Real.jacobiSnm/Cnm/Dnm` (in the
  parameter `m = k²`, defined through the amplitude) are bridged in
  `JacobiElliptic.SpecialValues` by `jacobiSnk_ofReal` etc. for `0 < k < 1` (proved by ODE
  uniqueness).

Mathlib and TauCeti have no Jacobian elliptic functions (checked 2026-10-25).
-/
