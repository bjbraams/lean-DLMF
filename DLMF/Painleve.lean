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
public import DLMF.Painleve.Defs
public import DLMF.Painleve.Equations
public import DLMF.Painleve.BacklundDLMF
public import DLMF.Painleve.Hamiltonian
public import DLMF.Painleve.Isomonodromy
public import DLMF.Painleve.SolutionsDefs
public import DLMF.Painleve.RationalDLMF
public import DLMF.Painleve.ElementarySolutions
public import DLMF.Painleve.SpecialSolutions
public import DLMF.Painleve.RealAsymptotics
public import DLMF.Painleve.Reductions
public import DLMF.Painleve.Combinatorics

/-! # Painlevé transcendents: DLMF Chapter 32 and Beals–Wong Chapter 15

The DLMF modules (`Defs`, `SolutionsDefs`, `Equations`, `BacklundDLMF`, `Hamiltonian`,
`Isomonodromy`, `RationalDLMF`, `ElementarySolutions`, `SpecialSolutions`, `RealAsymptotics`,
`Reductions`, `Combinatorics`) state DLMF Chapter 32 in its own normalization; see
DLMF32Acquisition.md. DLMF's PII `w'' = 2w³ + zw + α` is the Beals–Wong `PII(-α)` below
(`isPainleveIIOn_iff_isPIIOn`).

The Beals–Wong modules (`Basic`, `Backlund`, `Airy`, `LaxPair`, `Rational`, `LocalTheory`,
`Poles`, `Tau`) follow Beals–Wong Chapter 15.

The parameter convention is `u'' = 2u³ + xu - c` for `PII(c)`.

This development proves local real existence and uniqueness, the Bäcklund reflection
and integer shifts, rational solutions for every integer parameter, and meromorphic
Airy-based solutions for every half-integer parameter. It also proves the Lax
compatibility calculation, the energy derivative, a tau-quotient converse, and simple
pole/residue restrictions for solutions already known to be meromorphic.

The rational classification converse and uniqueness, global meromorphic continuation
of arbitrary solutions, Stokes/isomonodromy theory, and the real connection formulas
of Beals–Wong §15.8 are not yet formalized. The Airy scale satisfies `k³ = -1/2`;
this corrects the substitution printed on page 407.
-/
