/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Elementary.Hyperbolic.IdentitiesAndSeries
public import DLMF.Elementary.Hyperbolic.Products
public import DLMF.Elementary.Hyperbolic.InverseCalculus
public import DLMF.Elementary.Hyperbolic.InverseBranches
public import DLMF.Elementary.Hyperbolic.InverseIdentities
public import DLMF.Elementary.Hyperbolic.Integrals

/-!
# Hyperbolic and inverse hyperbolic functions (DLMF §§4.28–4.41)

This acquisition retains complex arguments, principal branches, the two sides of cuts,
convergence of series/products/continued fractions, exact algebraic tables, and prose results.
Upstream coverage is recorded separately in `DLMF.Elementary.MathlibCoverage`.

Reciprocals have Lean's totalized values at poles; every meromorphic identity requiring a
finite value has its pole exclusions stated. The inverse functions below choose one value on
each cut; the other cut value is represented by a one-sided limit. Multivalued inverses are
sets of solutions, with poles excluded from the inverse equations.

The inverse-sinh and mixed inverse-sinh/inverse-cosh sums and differences use paired sinh/cosh
equations to retain branch parity. These correct our full-set acquisition interpretation;
the printed DLMF branch formulas are not claimed to be false.
The former unrestricted full-set acquisition failed at critical parameters; explicit counterexamples
and complete compatible-branch characterizations are proved below using Mathlib log/exp calculus.

The Mathlib real inverse functions `Real.arsinh`, `Real.arcosh`, `Real.artanh` are reused for
real antiderivatives. TauCeti's real tanh/artanh additions and derivative declarations are
credited in the separate upstream coverage fragment; no upstream proofs are copied here.
-/
