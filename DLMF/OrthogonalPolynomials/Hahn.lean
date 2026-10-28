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

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/
