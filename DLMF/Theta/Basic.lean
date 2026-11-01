/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Theta.Basic.Definitions
public import DLMF.Theta.Basic.PowerSeries
public import DLMF.Theta.Basic.Series
public import DLMF.Theta.Basic.Periodicity
public import DLMF.Theta.Basic.Analytic

/-!
# Theta functions: foundations (DLMF §§20.1–20.2)

The definitions of the nome forms `θⱼ(z,q)`, the theta constants and the lattice data of
DLMF Chapter 20; the nome forms, Fourier series, quasi-periodicity, half-period translations
and analyticity of DLMF §20.2(i)–(iii); and the lattice sums and convergence radii of the
theta power series (DLMF §20.6). The project's theta functions themselves are
`DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`.
-/
