/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.Basic.EquationAndSolutions
public import DLMF.Mathieu.Basic.Spectral
public import DLMF.Mathieu.Basic.Functions
public import DLMF.Mathieu.Basic.ContinuedFractions

/-!
# Mathieu's equation and the Mathieu functions of integer order (DLMF §28.2)

The foundational definitions of the Mathieu area (DLMF Chapter 28): Mathieu's equation, the basic
solutions and Floquet data in `EquationAndSolutions`, the characteristic values `a_n(q)`, `b_n(q)`
in `Spectral`, the normalized Mathieu functions and their Fourier coefficients in `Functions`, and
truncated continued fractions in `ContinuedFractions`. The initial-value and normalization API is
in `DLMF.Mathieu.FundamentalSolutions`, and the existence and enumeration of characteristic values
in `DLMF.Mathieu.SpectralExistence`.
-/
