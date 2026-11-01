/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QHypergeometric.Basic.Series

/-!
# Basic hypergeometric series: common definitions (DLMF §§17.1, 17.2, 17.4)

This file collects the foundational definitions of the general unilateral and bilateral
basic hypergeometric series and their parameter conditions
(`DLMF.QHypergeometric.Basic.Series`). The shifted factorials, the `q`-derivative and the
Jackson integral come from `DLMF.QSeries`; the radius and analytic results are in
`DLMF.QHypergeometric.Convergence`.
-/
