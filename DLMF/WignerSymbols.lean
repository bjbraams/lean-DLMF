/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.WignerSymbols.Basic
public import DLMF.WignerSymbols.Q2wHelpers
public import DLMF.WignerSymbols.ThreeJ
public import DLMF.WignerSymbols.SixJ
public import DLMF.WignerSymbols.NineJ
public import DLMF.WignerSymbols.ThreeJLegendre
public import DLMF.WignerSymbols.LargeParameters

/-! # 3j, 6j, 9j symbols: DLMF Chapter 34

Angular momenta and projections are rationals with the standing conditions as predicates;
`wigner3j` is Racah's formula 34.2.4, `wigner6j` the sum 34.4.2 and `wigner9j` the sum 34.6.2.
Ledger: `DLMF34Acquisition.md`.
-/
