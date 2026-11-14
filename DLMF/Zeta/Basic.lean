/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.AlternatingHurwitz
public import DLMF.Zeta.Basic.Hurwitz
public import DLMF.Zeta.Basic.HurwitzProperties
public import DLMF.Zeta.Basic.Polylog
public import DLMF.Zeta.Basic.PolylogProperties
public import DLMF.Zeta.Basic.LerchContinuation
public import DLMF.Zeta.Basic.LerchProperties
public import DLMF.Zeta.Basic.Riemann
public import DLMF.Zeta.Basic.RiemannProperties

/-!
# Zeta and related functions: foundations (DLMF Chapter 25)

The foundational layer of DLMF Chapter 25. The Riemann zeta function is Mathlib's
`riemannZeta`; the modules imported here define the other functions of the chapter and prove
their basic properties.

* `DLMF.Zeta.Basic.Riemann`: the Stieltjes constants, Riemann's `ξ`, the factor `χ` of the
  functional equation and the Riemann–Siegel functions `θ` and `Z`.
* `DLMF.Zeta.Basic.RiemannProperties`: the Laurent expansion at `s = 1`, the Dirichlet series of
  the derivatives, the properties of `ξ` and the bridge of `Z` to Mathlib's `hardyZ`.
* `DLMF.Zeta.Basic.Hurwitz`: the Hurwitz zeta function `ζ(s, a)` for complex `a` by
  Euler–Maclaurin continuation, its holomorphy and the bridge to Mathlib's `hurwitzZeta`.
* `DLMF.Zeta.Basic.HurwitzProperties`: parameter derivatives and joint holomorphy.
* `DLMF.Zeta.Basic.Polylog`: the polylogarithm `Li_s(z)`, Lerch's transcendent `Φ(z, s, a)` and
  the Fermi–Dirac and Bose–Einstein integrals.
* `DLMF.Zeta.Basic.LerchProperties`: the branch predicate and analytic API of Lerch’s
  transcendent.
* `DLMF.Zeta.Basic.LerchContinuation`: existence and uniqueness of the principal continuation
  of Lerch's series, including its order-lowering recurrence.
* `DLMF.Zeta.Basic.PolylogProperties`: holomorphy, the derivative recurrence, orders zero and
  one, the unit-circle series and the bridge to Mathlib's periodic zeta function.
-/
