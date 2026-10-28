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

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
The adjacent Jacobi generating function combines the local parameter-raising relation
with Mathlib’s shifted-series API and the proved Gegenbauer generating function.
The finite Gegenbauer proofs combine the local explicit sums and recurrence with
the Mathlib contributors’ finite-sum, factorial, binomial and polynomial APIs.

The Jacobi generating function 18.12.1 (`jacobi_generating_function`) follows from the
coefficient form of the Lagrange–Bürmann formula (`Complex.lagB_hasSum_iteratedDeriv`):
`P_n^{(α,β)}(x) = [tⁿ] F(t) φ(t)ⁿ` with `φ(t) = (1 + (x+1)t/2)(1 + (x-1)t/2)` and
`F(t) = (1 + (x+1)t/2)^α (1 + (x-1)t/2)^β` (by 18.5.8), the root of `t = z φ(t)` being
`w = 2z/(1 - xz + R)`, `R = (1 - 2xz + z²)^{1/2}`. This gives the identity for small `|z|`;
it extends to `|z| < 1` because the right side is holomorphic there
(`Complex.lagB_hasSum_of_differentiableOn`). The weighted form 18.12.3
(`jacobi_weighted_generating_function`) is proved for small `|z|` by summing an absolutely
convergent double series in two ways, and then on the star-shaped domain
`{|z| < 1, |2(x+1)z/(1+z)²| < 1}` by the identity theorem, the left side having radius of
convergence at least `1` by 18.12.1.

Brafman's generating function 18.12.2_5 (`jacobi_brafman_generating_function`) follows from
Bailey's product formula for Appell's `F₄` (`DLMF.Hypergeometric.appF4_bailey`): with
`U = (1 - R - z)/2`, `V = (1 - R + z)/2` one has `U(1 - V) = (x-1)z/2`, `V(1 - U) = (x+1)z/2`,
and the antidiagonal sums of `F₄((x-1)z/2, (x+1)z/2)` are the Jacobi terms by 18.5.8. The
bound `|U|², |V|² ≤ |z|` on the unit disc (`jacB_norm_sq_le`, from `Re(R conj(1 ∓ z)) > 0`
by a connectedness argument) makes the right side holomorphic there, so the hypotheses
`|U|, |V| < 1` of the statement are redundant.
-/
