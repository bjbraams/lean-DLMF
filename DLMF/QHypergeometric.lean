/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.QHypergeometric.Appell
public import DLMF.QHypergeometric.BaileyPairs
public import DLMF.QHypergeometric.Convergence
public import DLMF.QHypergeometric.BasicSummations
public import DLMF.QHypergeometric.BilateralSummations
public import DLMF.QHypergeometric.BilateralTransformations
public import DLMF.QHypergeometric.Calculus
public import DLMF.QHypergeometric.ConstantTerms
public import DLMF.QHypergeometric.Elementary
public import DLMF.QHypergeometric.HigherSummations
public import DLMF.QHypergeometric.Integrals
public import DLMF.QHypergeometric.MathlibCoverage
public import DLMF.QHypergeometric.Transformations

/-!
# Basic hypergeometric and related functions (DLMF Chapter 17)

The acquisition reuses existing project and upstream APIs; open proof obligations
remain explicit. Source scope and branch conventions are tracked in the chapter ledger.
-/
