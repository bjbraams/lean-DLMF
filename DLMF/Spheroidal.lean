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
public import DLMF.Spheroidal.P2yFerrersTools
public import DLMF.Spheroidal.Existence
public import DLMF.Spheroidal.P3lParity
public import DLMF.Spheroidal.P3lSpectrum

/-!
# Spheroidal wave functions (DLMF Chapter 30)

The spheroidal equation, eigenvalues λ_n^m(γ²), angular functions Ps, Qs, their Ferrers
series and the radial functions S_n^{m(j)}. The ledger is DLMF30Acquisition.md.
-/
