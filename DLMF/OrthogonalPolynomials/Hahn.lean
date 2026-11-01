/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.Hahn.HahnAndMeixner
public import DLMF.OrthogonalPolynomials.Hahn.CharlierAndConnections
public import DLMF.OrthogonalPolynomials.Hahn.Orthogonality

/-!
# The Hahn class: definitions, orthogonality, differences, and generating functions

The Hahn class of DLMF §§18.19–18.23: the Hahn, Krawtchouk, Meixner, Charlier, continuous
Hahn and Meixner–Pollaczek polynomials, with their orthogonality, recurrences, difference
equations, limit relations and generating functions. Jacobi and Gegenbauer statements keep
regularity hypotheses because the hypergeometric definitions used here are not continued in
singular parameters.
-/
