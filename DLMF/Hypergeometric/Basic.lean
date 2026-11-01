/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.Basic.Pochhammer
public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import DLMF.Hypergeometric.Basic.PrincipalBranch
public import DLMF.Hypergeometric.Basic.AppellF4
public import DLMF.Hypergeometric.Basic.GaussSeries
public import DLMF.Hypergeometric.Basic.GaussEquation
public import DLMF.Hypergeometric.Basic.ParameterAnalyticity
public import DLMF.Hypergeometric.Basic.CutPlane

/-!
# Definitions and elementary coefficient algebra for hypergeometric functions

This module collects the foundational definitions for DLMF Chapter 15: Pochhammer symbols
(`DLMF.Hypergeometric.Basic.Pochhammer`), the Gauss coefficients
(`DLMF.Hypergeometric.Basic.GaussCoefficients`), the cut plane and the continued Gauss function
(`DLMF.Hypergeometric.Basic.PrincipalBranch`), Appell's `F₄`
(`DLMF.Hypergeometric.Basic.AppellF4`), and the basic properties of the Gauss function: the series
on the unit disk (`DLMF.Hypergeometric.Basic.GaussSeries`), the hypergeometric equation and its
standard solutions (`DLMF.Hypergeometric.Basic.GaussEquation`), analyticity in the parameters
(`DLMF.Hypergeometric.Basic.ParameterAnalyticity`) and the continuation to the cut plane
(`DLMF.Hypergeometric.Basic.CutPlane`).
-/
