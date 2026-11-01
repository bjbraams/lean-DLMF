/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.Series.ClassicalGenerating
public import DLMF.OrthogonalPolynomials.Series.JacobiParameterSeries
public import DLMF.OrthogonalPolynomials.Series.BrafmanAndWeighted
public import DLMF.OrthogonalPolynomials.Series.AdjacentJacobi

/-!
# Generating functions, connection formulas, and linearization

Generating functions of the classical orthogonal polynomials (DLMF §18.12), and the addition,
multiplication, connection, linearization and convolution formulas of DLMF §18.18. Jacobi and
Gegenbauer statements keep regularity hypotheses because the hypergeometric definitions used
here are not continued in singular parameters.
-/
