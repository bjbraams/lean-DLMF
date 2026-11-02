/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.SpectralExistence
public import DLMF.Mathieu.Basic.ContinuedFractions
public import DLMF.Mathieu.Properties
public import DLMF.Mathieu.FourierSeries
public import DLMF.Mathieu.SecondSolutions
public import DLMF.Mathieu.SmallQ
public import DLMF.Mathieu.Continuation
public import DLMF.Mathieu.LargeQ
public import DLMF.Mathieu.Zeros
public import DLMF.Mathieu.IntegralEquations
public import DLMF.Mathieu.Expansions
public import DLMF.Mathieu.Noninteger.Basic
public import DLMF.Mathieu.Noninteger.ExpSeries
public import DLMF.Mathieu.Noninteger.RealContinuation
public import DLMF.Mathieu.Noninteger.Properties
public import DLMF.Mathieu.Noninteger.Fourier
public import DLMF.Mathieu.Noninteger.Expansions
public import DLMF.Mathieu.Modified.Basic
public import DLMF.Mathieu.Modified.BesselSeries
public import DLMF.Mathieu.Modified.Properties
public import DLMF.Mathieu.Modified.Connection
public import DLMF.Mathieu.Modified.Asymptotics
public import DLMF.Mathieu.Modified.Integrals
public import DLMF.Mathieu.Hill.Basic
public import DLMF.Mathieu.Hill.Floquet
public import DLMF.Mathieu.Hill.Eigenfunctions
public import DLMF.Mathieu.Hill.Ince
public import DLMF.Mathieu.SturmBridge
public import DLMF.Mathieu.Modified.CrossSeries
public import DLMF.Mathieu.Modified.RadialSeries
public import DLMF.Mathieu.Modified.CrossConnection
public import DLMF.Mathieu.Modified.ImaginaryArgument
public import DLMF.Mathieu.Modified.KernelIntegrals
public import DLMF.Mathieu.Modified.Wronskians
public import DLMF.Mathieu.SmallQJacobi
public import DLMF.Mathieu.SmallQSpectrum
public import DLMF.Mathieu.SmallQGeneral
public import DLMF.Mathieu.SmallQVector
public import DLMF.Mathieu.SmallQCeSe
public import DLMF.Mathieu.SmallQCeSeGeneral

/-!
# Mathieu functions and Hill's equation (DLMF Chapter 28)

Mathieu functions of integer order (DLMF §§28.1–28.11) in `Basic` through `Expansions`, of
noninteger order (DLMF §§28.12–28.19) in `Noninteger`, modified Mathieu functions
(DLMF §§28.20–28.28) in `Modified`, and Hill's equation (DLMF §§28.29–28.31) in `Hill`. The
fundamental solutions and eigenvalues are defined by choice, justified by existence theorems.
-/
