/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.OrthogonalPolynomials.QFamilies.BasicIdentities
public import DLMF.OrthogonalPolynomials.QFamilies.ClassicalLimits

/-!
# The q-Hahn and Askey–Wilson classes

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
The `q`-Gegenbauer limit follows termwise from the finite `q`-Pochhammer ratio limits
and the proved coefficients of the Gegenbauer generating series.
The Askey–Wilson difference equation follows by triangular action on the paired
q-Pochhammer basis and a finite telescoping sum, retaining all stated parameters.
The q-Hahn proof reuses the finite summation-by-parts operator `DiscreteOrtho.sum_range_orthogonal` from `Hahn.lean`.
Little q-Jacobi orthogonality reuses the moment cancellations in `QOrthogonalityTools`.
Stieltjes–Wigert orthogonality uses the proved density and moment theorems from
`TauCeti.Probability.Distributions.LogNormal.Basic`, followed by Cauchy’s finite q-binomial theorem.
-/
