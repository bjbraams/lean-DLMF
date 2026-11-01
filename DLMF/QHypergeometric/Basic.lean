/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QHypergeometric.Basic.Series
public import DLMF.QHypergeometric.Basic.SeriesProperties
public import DLMF.QHypergeometric.Basic.ShiftedFactorials
public import DLMF.QHypergeometric.Basic.Elementary
public import DLMF.QHypergeometric.Basic.Appell
public import DLMF.QHypergeometric.Basic.Calculus

/-!
# Basic hypergeometric series: common definitions (DLMF §§17.1, 17.2, 17.4)

This file collects the foundational definitions of the general unilateral and bilateral
basic hypergeometric series and their parameter conditions
(`DLMF.QHypergeometric.Basic.Series`, `DLMF.QHypergeometric.Basic.SeriesProperties`), the
identities for `q`-shifted factorials (`DLMF.QHypergeometric.Basic.ShiftedFactorials`), the
`q`-exponential, `q`-sine and `q`-cosine functions
(`DLMF.QHypergeometric.Basic.Elementary`), the `q`-Appell functions
(`DLMF.QHypergeometric.Basic.Appell`), and the extended `q`-derivative and the bilateral
Jackson integral (`DLMF.QHypergeometric.Basic.Calculus`). The shifted factorials, the
`q`-derivative and the Jackson integral come from `DLMF.QSeries`; the radius and analytic
results are in `DLMF.QHypergeometric.Convergence`.
-/
