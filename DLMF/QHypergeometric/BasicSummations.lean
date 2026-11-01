/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QHypergeometric.BasicSummations.OnePhiZero
public import DLMF.QHypergeometric.BasicSummations.QGauss
public import DLMF.QHypergeometric.BasicSummations.Heine

/-!
# Low-order basic hypergeometric functions (DLMF §§17.5–17.6)

This umbrella collects the `q`-binomial theorem and the continuation of `₁φ₀`
(`BasicSummations.OnePhiZero`, DLMF 17.5.2–17.5.4), the `q`-Chu–Vandermonde, `q`-Gauss and
`₁φ₁` sums (`BasicSummations.QGauss`), and Heine's transformations and related `₂φ₁`
identities (`BasicSummations.Heine`, DLMF 17.6.4–17.6.29).

The series retain DLMF's integer phase exponents. Literal product quotients are used only where
their denominators are nonzero; cancelled product forms and removable-limit statements retain
exceptional upper parameters, finite identities require lower-parameter regularity only through
the final retained term, and analytic continuation (via TauCeti's `ContinuesInside`) is kept
separate from totalized divergent sums.
-/
