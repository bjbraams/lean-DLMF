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
# `q`-series (AAR Chapter 10)

Mathlib has Jacobi theta functions, the Mellin transform, and the arithmetic theorems on
sums of two and four squares, but not `q`-Pochhammer symbols, `q`-gamma, the `q`-binomial
theorem, Ramanujan's `₁ψ₁`, or basic hypergeometric series.

Following Duverney, *An Introduction to Hypergeometric Functions*, Chapter 10, this area also
has Gaussian `q`-binomial coefficients and Cauchy's finite `q`-binomial theorem (`QBinomial`),
the `q`-derivative and the `q`-fundamental theorem for Jackson's integral (`QCalculus`),
Heine's second and third transformations, the `q`-Gauss and `q`-Chu–Vandermonde summations
(`Heine`), and Euler's two `q`-exponential identities (`QExponential`).

`Saalschutz` proves the terminating `q`-Pfaff–Saalschütz sum for all `q`, as a polynomial
identity and in the quotient form used for Bailey's lemma (`DLMF.Bailey`).
-/
