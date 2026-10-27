/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.MatrixArgument.Basic
public import DLMF.MatrixArgument.GammaBeta
public import DLMF.MatrixArgument.Q2mMatrixIntegrals
public import DLMF.MatrixArgument.Zonal
public import DLMF.MatrixArgument.Generalized
public import DLMF.MatrixArgument.Bessel
public import DLMF.MatrixArgument.Confluent
public import DLMF.MatrixArgument.Gaussian
public import DLMF.MatrixArgument.MathlibCoverage

/-! # Functions of matrix argument: DLMF Chapter 35

Real symmetric matrices with Tau Ceti's Lebesgue measure, the cone of positive definite matrices,
the Haar probability measure on `O(m)`, multivariate Gamma and Beta functions, zonal polynomials
defined by DLMF 35.4.2–35.4.3, and Bessel and hypergeometric functions of matrix argument.
Ledger: `DLMF35Acquisition.md`.
-/
