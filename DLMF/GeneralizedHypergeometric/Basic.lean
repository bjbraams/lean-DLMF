/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation
public import DLMF.GeneralizedHypergeometric.Basic.BilateralAndBarnes
public import DLMF.GeneralizedHypergeometric.Basic.SeriesProperties
public import DLMF.GeneralizedHypergeometric.Basic.MeijerG

/-!
# Definitions of generalized hypergeometric functions and branches

This module collects the definitions of DLMF Chapter 16 for `ₚF_q`: parameter multisets,
coefficients and finite series (`DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries`), the
normalized principal continuation (`DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation`),
bilateral series and Barnes integrals (`DLMF.GeneralizedHypergeometric.Basic.BilateralAndBarnes`),
the series facts of §16.2 (`DLMF.GeneralizedHypergeometric.Basic.SeriesProperties`), and the
Meijer G function of §16.17 (`DLMF.GeneralizedHypergeometric.Basic.MeijerG`).
-/
