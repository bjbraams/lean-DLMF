/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Theta.SeriesAndZeros
public import DLMF.Theta.ZeroValues
public import DLMF.Theta.Products
public import DLMF.Theta.PowerSeries
public import DLMF.Theta.Identities
public import DLMF.Theta.Relations
public import DLMF.Theta.Integrals
public import DLMF.Theta.Generalizations
public import DLMF.Theta.ImaginaryAxisMonotonicity
public import DLMF.Theta.MathlibCoverage

/-!
# Theta functions (DLMF Chapter 20)

The Jacobi theta functions `θⱼ(z|τ)` are `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`
(DLMF normalization, from Mathlib's `jacobiTheta₂`). This area covers DLMF §§20.1–20.2 and
§§20.4–20.11: nome forms, Fourier series, quasi-periodicity and zeros; values at `z = 0`;
infinite products; power series; identities and transformations; relations to elliptic
integrals and the modular function; integrals; and generalizations, together with pointers
to Mathlib.
-/
