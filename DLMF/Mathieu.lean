/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.Basic
public import DLMF.Mathieu.ContFracDefs
public import DLMF.Mathieu.Properties
public import DLMF.Mathieu.FourierSeries
public import DLMF.Mathieu.SecondSolutions
public import DLMF.Mathieu.SmallQ
public import DLMF.Mathieu.Continuation
public import DLMF.Mathieu.LargeQ
public import DLMF.Mathieu.Zeros
public import DLMF.Mathieu.IntegralEquations
public import DLMF.Mathieu.Expansions
public import DLMF.Mathieu.Noninteger.Defs
public import DLMF.Mathieu.Noninteger.Properties
public import DLMF.Mathieu.Noninteger.Fourier
public import DLMF.Mathieu.Noninteger.Expansions
public import DLMF.Mathieu.Modified.Defs
public import DLMF.Mathieu.Modified.BesselSeries
public import DLMF.Mathieu.Modified.Properties
public import DLMF.Mathieu.Modified.Connection
public import DLMF.Mathieu.Modified.Asymptotics
public import DLMF.Mathieu.Modified.Integrals
public import DLMF.Mathieu.Hill.Defs
public import DLMF.Mathieu.Hill.Floquet
public import DLMF.Mathieu.Hill.Eigenfunctions
public import DLMF.Mathieu.Hill.Ince
public import DLMF.Mathieu.P2sBridge
public import DLMF.Mathieu.Modified.P2mCrossSeries
public import DLMF.Mathieu.Modified.P2mRadial
public import DLMF.Mathieu.Modified.P2mConnection
public import DLMF.Mathieu.Modified.P3mImaginary
public import DLMF.Mathieu.Modified.P3mIntegrals
public import DLMF.Mathieu.Modified.P3mWronskian
public import DLMF.Mathieu.P3qJacobi
public import DLMF.Mathieu.P3qSpectrum
public import DLMF.Mathieu.P3qGeneral
public import DLMF.Mathieu.P3qVector
public import DLMF.Mathieu.P3qCeSe
public import DLMF.Mathieu.P3qCeSeGen

/-!
# Mathieu functions and Hill's equation (DLMF Chapter 28)

Part A (§§28.1–28.11, integer order): `Basic` through `Expansions`; part B (§§28.12–28.19,
noninteger order): `Noninteger`; part C (§§28.20–28.28, modified Mathieu functions):
`Modified`; part B also covers Hill's equation (§§28.29–28.31): `Hill`. The fundamental
solutions and eigenvalues are defined by choice from flagged existence theorems. The ledger
is DLMF28Acquisition.md.
-/
