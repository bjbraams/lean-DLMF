/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Spheroidal.Basic
public import DLMF.Spheroidal.FerrersProperties
public import DLMF.Spheroidal.Equation
public import DLMF.Spheroidal.Eigenvalues
public import DLMF.Spheroidal.Angular
public import DLMF.Spheroidal.FerrersSeries
public import DLMF.Spheroidal.Radial
public import DLMF.Spheroidal.FerrersTools
public import DLMF.Spheroidal.Existence
public import DLMF.Spheroidal.Parity
public import DLMF.Spheroidal.Spectrum

/-!
# Spheroidal wave functions (DLMF Chapter 30)

This umbrella collects the DLMF Chapter 30 development of spheroidal wave functions: the
spheroidal equation, the eigenvalues `λ^m_n(γ²)` and their existence and parity, the angular
functions `𝖯s`, `𝖰s`, `𝑃s`, `𝑄s`, their expansions in Ferrers functions, and the radial functions
`S^{m(j)}_n`.
-/
