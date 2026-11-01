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
public import DLMF.Lame.FourierExistence
public import DLMF.Lame.Polynomials.Basis
public import DLMF.Lame.Polynomials.DifferentialEquation
public import DLMF.Lame.Polynomials.Eigenvalues
public import DLMF.Lame.Polynomials.Identities
public import DLMF.Lame.WeierstrassForm
public import DLMF.Lame.Polynomials.Zeros

/-!
# Lamé functions (DLMF Chapter 29)

This umbrella module collects Lamé's equation in its Jacobian, algebraic, trigonometric and
Weierstrass forms, the eigenvalues `a^m_ν(k²)`, `b^m_ν(k²)` and Lamé functions `Ec`, `Es`
(defined by choice from Sturm–Liouville existence theorems), their Fourier series, special cases,
asymptotics and integral equations, and the explicit Lamé polynomials of §29.12 with their
zeros and orthogonality.
-/
