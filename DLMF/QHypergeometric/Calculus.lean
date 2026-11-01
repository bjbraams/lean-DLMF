/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QHypergeometric.Calculus.QBinomial
public import DLMF.QHypergeometric.Calculus.QDerivative
public import DLMF.QHypergeometric.Calculus.JacksonIntegral

/-!
# `q`-calculus adapters and Gaussian coefficients (DLMF §17.2)

This umbrella collects the Gaussian coefficients and `q`-binomial series
(`Calculus.QBinomial`, DLMF 17.2.6–17.2.40), the `q`-derivative with its removable value at
the origin (`Calculus.QDerivative`, DLMF 17.2.41–17.2.44 and the limit `q → 1`), and the
Jackson integrals (`Calculus.JacksonIntegral`, DLMF 17.2.45–17.2.48). The shifted factorials,
Gaussian polynomials, Jackson integral and `q`-derivative are reused from `DLMF.QSeries`.
-/
