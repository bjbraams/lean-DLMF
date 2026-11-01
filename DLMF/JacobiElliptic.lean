/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.JacobiElliptic.Addition
public import DLMF.JacobiElliptic.AnalyticProperties
public import DLMF.JacobiElliptic.Cyclic
public import DLMF.JacobiElliptic.Derivatives
public import DLMF.JacobiElliptic.ElementaryIdentities
public import DLMF.JacobiElliptic.FourierSeries
public import DLMF.JacobiElliptic.Integrals
public import DLMF.JacobiElliptic.Inverse
public import DLMF.JacobiElliptic.Landen
public import DLMF.JacobiElliptic.Maclaurin
public import DLMF.JacobiElliptic.MathlibCoverage
public import DLMF.JacobiElliptic.OutsideModuli
public import DLMF.JacobiElliptic.EisensteinSeries
public import DLMF.JacobiElliptic.JacobiODE
public import DLMF.JacobiElliptic.PartialFractions
public import DLMF.JacobiElliptic.PeriodsPolesZeros
public import DLMF.JacobiElliptic.Related
public import DLMF.JacobiElliptic.SpecialValues

/-!
# Jacobian elliptic functions (DLMF Chapter 22)

This umbrella module collects the Jacobian elliptic functions `pq(z, k)` (Glaisher's notation,
`p, q ∈ {s, c, d, n}`), defined as theta quotients following DLMF §22.2, both in lattice form
(parameter `τ`) and in DLMF's modulus form with the principal complex `K(k)`, `K'(k)`. It covers
periods, poles and zeros, special values, elementary identities, Landen transformations,
addition theorems, cyclic identities, derivatives and differential equations, series, inverse
functions, integrals, related functions and analytic properties (DLMF §§22.2–22.20).

Results in the modulus form hold on the domain `Re k > 0`, `k ∉ [1, ∞)`. Mathlib has no
Jacobian elliptic functions.
-/
