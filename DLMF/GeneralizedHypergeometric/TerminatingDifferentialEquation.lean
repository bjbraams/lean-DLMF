/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.DifferentialEquations

/-!
# The ordinary terminating hypergeometric differential equation

Temme, *Special Functions* (1996), Chapter 5, (5.29)–(5.30), pp. 124–125,
synopsis TEM-05-11. Lower poles beyond the retained polynomial degree are
allowed. At such parameters the finite ordinary polynomial differs from the
Gamma-product totalization of the principal continued function.
-/

@[expose] public noncomputable section
namespace DLMF.Hypergeometric

/-- A terminating ordinary polynomial solves the theta equation whenever every
retained denominator is nonzero, Temme (5.29)–(5.30), synopsis TEM-05-11.
No global lower-parameter exclusion or bound on the numbers of parameters is needed. -/
theorem generalizedHypergeometricTruncated_theta_ode (N : ℕ) (a b : Multiset ℂ)
    (hupper : -(N : ℂ) ∈ a)
    (hreg : ∀ k ≤ N, pochhammerProduct b k ≠ 0) (z : ℂ) :
    GenODESolution a b (generalizedHypergeometricTruncated N a b) z := by
  sorry

end DLMF.Hypergeometric
