/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.BoundsZeros.PointwiseAndZeroBounds
public import DLMF.OrthogonalPolynomials.BoundsZeros.Discriminants

/-!
# Bounds, positive sums, zeros, and leading asymptotics

This umbrella collects the inequalities, positive sums, asymptotics and zeros of the classical
orthogonal polynomials (DLMF §§18.14–18.16, `BoundsZeros.PointwiseAndZeroBounds`) and their
discriminants (DLMF 18.16.19–18.16.21, `BoundsZeros.Discriminants`). Jacobi and Gegenbauer
statements retain regularity hypotheses because the project's hypergeometric definitions do
not implement continuation in singular parameters.
-/
