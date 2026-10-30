/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Lame.Basic
public import DLMF.Lame.Polynomials.Basic
public import DLMF.Lame.Eigenvalues
public import DLMF.Lame.DifferentialEquations
public import DLMF.Lame.FourierSeries
public import DLMF.Lame.SpecialCases
public import DLMF.Lame.Asymptotics
public import DLMF.Lame.IntegralEquations
public import DLMF.Lame.Polynomials.Series
public import DLMF.Lame.Polynomials.Orthogonality
public import DLMF.Lame.OtherSolutions
public import DLMF.Lame.P2lFourier
public import DLMF.Lame.Polynomials.P2pBase
public import DLMF.Lame.Polynomials.P2pODE
public import DLMF.Lame.Polynomials.P2pEigen
public import DLMF.Lame.Polynomials.P2pIdent
public import DLMF.Lame.P3lWeierstrass
public import DLMF.Lame.Polynomials.P3lZeros

/-!
# Lamé functions (DLMF Chapter 29)

Lamé's equation in Jacobian and algebraic forms, the eigenvalues and Lamé functions
Ec, Es (defined by choice from admitted Sturm–Liouville existence theorems) and the
explicit Lamé polynomials of §29.12. The ledger is DLMF29Acquisition.md.
-/
