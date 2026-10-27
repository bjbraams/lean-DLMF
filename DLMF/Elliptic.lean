/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Elliptic.Complete
public import DLMF.Elliptic.AGM
public import DLMF.Elliptic.Jacobi
public import DLMF.Elliptic.JacobiIdentities
public import DLMF.Elliptic.SpecialValues
public import DLMF.Elliptic.Theta
public import DLMF.Elliptic.ThirdKind
public import DLMF.Elliptic.ThetaAGM
public import DLMF.Elliptic.MathlibCoverage

/-!
# Elliptic integrals and elliptic functions (Temme Chapter 12; DLMF Chapters 19, 20, 22)

Mathlib provides the arithmetic-geometric mean `NNReal.agm`, Jacobi's two-variable theta function
`jacobiTheta₂` and the Weierstrass `℘` function, but no elliptic integrals or Jacobi elliptic
functions. This area adds, for a real parameter `m = k² < 1`:

* `Complete`: `K(m)`, `E(m)`, their derivatives, Legendre's relation and the hypergeometric
  forms (DLMF 19.2.8, 19.4.1–2, 19.5.1–2, 19.7.1), with the derivatives in both `m` and `k`.
* `AGM`: Gauss's theorem `K(m) = π/(2 M(1, √(1-m)))` and the Landen transformations of `K`
  and `E` (Temme §12.1.2, (12.11)–(12.14); DLMF 19.8.5, 19.8.12).
* `Jacobi`: incomplete integrals `F(φ|m)`, `E(φ|m)`, the amplitude, and `sn`, `cn`, `dn` with
  their identities, derivatives and periodicity (Temme §§12.2–12.3, DLMF 22.6.1, 22.13.1–3).
* `Theta`: `θ₁, …, θ₄` in DLMF normalization via `jacobiTheta₂` (DLMF §20.2).
* `ThirdKind`: `Π(φ, n, m)` and `Π(n, m)` for `n, m < 1`: quasi-periodicity, oddness,
  `Π(φ, 0, m) = F(φ, m)` and the closed form at `m = 0`, `Π(n, 0) = π/(2√(1-n))` (DLMF 19.2.7,
  Temme (12.17)).
* `ThetaAGM`: the theta doubling identities and Jacobi's `K = (π/2) θ₃²` with
  `k' = θ₄²/θ₃²` for a real nome (DLMF 20.9.2).
* `JacobiIdentities`: `dn² - m cn² = 1 - m`, the first- and second-order equations of `sn`,
  `cn`, `dn`, the addition formulas (DLMF 22.8.1–3), the shift by `K` and the values at `K/2`,
  and the simple pendulum (Duverney Ch. 5).
* `SpecialValues`: `∫₀ˣ dt/√((1-t²)(1-mt²)) = F(arcsin x|m)` and Jacobi's `arcsn`; `K(1/2)`,
  `E(1/2)`, Gauss's constant `Γ(1/4)² M(1, 1/√2) = 2π^{3/2}`, the lemniscate integral, and the
  perimeter of an ellipse as a `₂F₁` (Duverney Ch. 5).

Names follow Miller's DLMF content dictionaries, with the argument convention as the last letter:
`k` for the modulus, `m = k²` for the parameter, `Tau` or `Q` for the theta functions in `τ` or in
the nome `q`. The real-variable functions live in `DLMF.Elliptic.Real`: `Real.compEllIntKm`,
`Real.compEllIntEm`, `Real.compEllIntPim`, `Real.incEllIntFm`, `Real.incEllIntEm`,
`Real.incEllIntPim`, `Real.jacobiAmm`, `Real.jacobiSnm`, `Real.jacobiCnm`, `Real.jacobiDnm`,
`Real.jacobiArcsnm`, and the theta constants `Real.jacobiThetaThreeNullQ`,
`Real.jacobiThetaFourNullQ`. The complex theta functions are `jacobiThetaOneTau`, …,
`jacobiThetaFourTau`. The argument order is DLMF's, e.g. `Π(φ, n, m)`.
-/
