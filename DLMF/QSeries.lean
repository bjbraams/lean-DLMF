/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QSeries.Heine
public import DLMF.QSeries.Identities
public import DLMF.QSeries.Pochhammer
public import DLMF.QSeries.QBinomial
public import DLMF.QSeries.QCalculus
public import DLMF.QSeries.QExponential
public import DLMF.QSeries.Saalschutz

/-!
# `q`-series (AAR Chapter 10; Duverney Chapter 10)

This area develops `q`-Pochhammer symbols, the `q`-gamma function, the `q`-binomial theorem,
the Jacobi triple product, Ramanujan's `₁ψ₁` and basic hypergeometric series (AAR Chapter 10),
together with Gaussian `q`-binomial coefficients, the `q`-derivative and Jackson integral,
Heine's transformations, Euler's `q`-exponential identities and the terminating
`q`-Pfaff–Saalschütz sum (Duverney Chapter 10). Mathlib has Jacobi theta functions but none
of these `q`-analogues.
-/
