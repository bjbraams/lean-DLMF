/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QHypergeometric.Basic.Series

/-!
# Basic hypergeometric series: common definitions (DLMF §§17.1,17.2,17.4)

The finite, infinite and integer-index shifted factorials, the q-derivative, and the Jackson
integral reuse `DLMF.QSeries`. The integer triangular exponent reuses
`DLMF.QSeries.TripleProduct.tri`. The general unilateral and bilateral series below include
the phase factors specified by DLMF/Gasper–Rahman; both differences of parameter counts
are integers. `tsum` is totalized outside convergence, and the identities state their
convergence and exceptional-parameter hypotheses separately.
The scalar-series interface directly applies Mathlib's `ofScalars`, convergence-radius
bound, and change-of-origin analytic API; it does not impose nonzero upper parameters.

The scalar-series radius and analytic results are in `DLMF.QHypergeometric.Convergence`.
-/
