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
public import DLMF.Mathieu.Basic.FundamentalSolutions
public import DLMF.Mathieu.Basic.Properties
public import DLMF.Mathieu.Basic.Floquet
public import DLMF.Mathieu.Basic.Eigenfunctions
public import DLMF.Mathieu.Basic.SpectralExistence

/-!
# Mathieu's equation and the Mathieu functions of integer order (DLMF §28.2)

The foundational definitions of the Mathieu area (DLMF Chapter 28): Mathieu's equation, the basic
solutions and Floquet data in `EquationAndSolutions`, the characteristic values `a_n(q)`, `b_n(q)`
in `Spectral`, the normalized Mathieu functions and their Fourier coefficients in `Functions`, and
truncated continued fractions in `ContinuedFractions`. The initial-value and normalization API is
in `FundamentalSolutions`, and the symmetries, parity, Wronskian and half-period relations of the
basic solutions (§28.2(i)–(ii)) are in `Properties`, Floquet's theorem and the characteristic
equation (§28.2(iii)–(iv)) in `Floquet`, and the normalization and parity of `ce_n`, `se_n`
(§28.2(vi)) in `Eigenfunctions`, and the existence and enumeration of the characteristic values
(§28.2(v)) in `SpectralExistence`.
-/
