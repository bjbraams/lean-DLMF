/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.Differential.ClassicalEquations
public import DLMF.OrthogonalPolynomials.Differential.ChebyshevAndShifts

/-!
# Differential equations and recurrences (DLMF §§18.8–18.9)

This umbrella collects the differential equations, recurrences and derivative formulas of the
classical orthogonal polynomials (`Differential.ClassicalEquations`) and the corresponding
results for Chebyshev and shifted polynomials (`Differential.ChebyshevAndShifts`). Jacobi and
Gegenbauer statements retain regularity hypotheses because the project's hypergeometric
definitions do not implement continuation in singular parameters.
-/
