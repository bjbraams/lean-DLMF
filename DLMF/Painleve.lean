/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Painleve.Basic
public import DLMF.Painleve.Backlund
public import DLMF.Painleve.Airy
public import DLMF.Painleve.LaxPair
public import DLMF.Painleve.Rational
public import DLMF.Painleve.LocalTheory
public import DLMF.Painleve.Poles
public import DLMF.Painleve.Tau
public import DLMF.Painleve.Basic
public import DLMF.Painleve.Equations
public import DLMF.Painleve.BacklundDLMF
public import DLMF.Painleve.Hamiltonian
public import DLMF.Painleve.Isomonodromy
public import DLMF.Painleve.Basic.Solutions
public import DLMF.Painleve.RationalDLMF
public import DLMF.Painleve.ElementarySolutions
public import DLMF.Painleve.SpecialSolutions
public import DLMF.Painleve.RealAsymptotics
public import DLMF.Painleve.Reductions
public import DLMF.Painleve.Combinatorics
public import DLMF.Painleve.FreudWeight

/-! # Painlevé transcendents: DLMF Chapter 32 and Beals–Wong Chapter 15

The DLMF modules (`Basic`, `Basic.Solutions`, `Equations`, `BacklundDLMF`, `Hamiltonian`,
`Isomonodromy`, `RationalDLMF`, `ElementarySolutions`, `SpecialSolutions`, `RealAsymptotics`,
`Reductions`, `Combinatorics`) treat DLMF Chapter 32 in DLMF's normalization. DLMF's PII
`w'' = 2w³ + zw + α` is the Beals–Wong `PII(-α)` (`isPainleveIIOn_iff_isPIIOn`).

The Beals–Wong modules (`Basic`, `Backlund`, `Airy`, `LaxPair`, `Rational`, `LocalTheory`,
`Poles`, `Tau`) follow Beals–Wong Chapter 15, with the parameter convention
`u'' = 2u³ + xu - c` for `PII(c)`. They contain local real existence and uniqueness, the
Bäcklund reflection and integer shifts, rational solutions for every integer parameter,
meromorphic Airy-based solutions for every half-integer parameter, the Lax compatibility
calculation, the energy derivative, a tau-quotient converse, and simple pole and residue
restrictions for solutions known to be meromorphic. The Airy scale satisfies `k³ = -1/2`;
this corrects the substitution printed on page 407 of Beals–Wong.
-/
