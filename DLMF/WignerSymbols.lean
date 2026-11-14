/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.WignerSymbols.NineJFactorialCoordinates
public import DLMF.WignerSymbols.OrbitalModes

public import DLMF.WignerSymbols.ReggeArrays

public import DLMF.WignerSymbols.SpinCoupling

public import DLMF.WignerSymbols.StretchedNineJ

public import DLMF.WignerSymbols.Recoupling

public import DLMF.WignerSymbols.SixJCoordinates

public import DLMF.WignerSymbols.SpinMatrices
public import DLMF.WignerSymbols.Basic
public import DLMF.WignerSymbols.Basic.TriangleConditions
public import DLMF.WignerSymbols.FactorialHelpers
public import DLMF.WignerSymbols.ThreeJ
public import DLMF.WignerSymbols.SixJ
public import DLMF.WignerSymbols.NineJ
public import DLMF.WignerSymbols.ThreeJLegendre
public import DLMF.WignerSymbols.LargeParameters
public import DLMF.WignerSymbols.RacahPochhammer
public import DLMF.WignerSymbols.ThreeJRecursion
public import DLMF.WignerSymbols.SixJRecursion

/-!
# Wigner `3j`, `6j` and `9j` symbols

This area covers DLMF Chapter 34: the `3j`, `6j` and `9j` symbols, their special values,
symmetries, orthogonality relations, sum rules and recursions, the relation with Legendre
polynomials, and the approximation for large parameters. Angular momenta and projections are
rationals with the standing conditions as predicates; `wigner3j` is Racah's formula 34.2.4,
`wigner6j` the sum 34.4.2 and `wigner9j` the sum 34.6.2.
-/
