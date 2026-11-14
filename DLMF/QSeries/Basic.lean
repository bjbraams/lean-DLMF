/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QSeries.Basic.Logarithm
public import DLMF.QSeries.Basic.Pochhammer
public import DLMF.QSeries.Basic.Series
public import DLMF.QSeries.Basic.Calculus
public import DLMF.QSeries.Basic.PochhammerProperties
public import DLMF.QSeries.Basic.CalculusProperties
public import DLMF.QSeries.Basic.SeriesProperties

/-!
# Foundations of `q`-series

This file collects the foundational definitions of the `q`-series area: `q`-Pochhammer
symbols, the Jackson integral and `q`-gamma (`DLMF.QSeries.Basic.Pochhammer`), Gaussian
coefficients, `q`-numbers and the `q`-derivative (`DLMF.QSeries.Basic.Calculus`), and
integer-index shifted factorials and basic hypergeometric series
(`DLMF.QSeries.Basic.Series`), together with the basic properties of the shifted factorials and
`q`-gamma (`DLMF.QSeries.Basic.PochhammerProperties`) and of Gaussian coefficients and the
`q`-derivative (`DLMF.QSeries.Basic.CalculusProperties`) and of integer-index shifted
factorials (`DLMF.QSeries.Basic.SeriesProperties`).
-/
