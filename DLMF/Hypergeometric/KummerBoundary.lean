/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.PrincipalBranch
public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Kummer's value at minus one with ordinary boundary convergence

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§9.2, pp. 9-5–9-6, synopsis RL-9.03. Duplication rewrites Kummer's Gamma quotient
as a product of reciprocal Gamma factors, removing the apparent singularity at
even negative upper parameters. The principal continued function and the
possibly conditional natural-order series are stated separately.
-/

@[expose] public noncomputable section
open Complex Filter Finset
open scoped Topology
namespace DLMF.Hypergeometric

/-- Kummer's regularized principal value at minus one, valid for all parameters,
Rao–Lakshminarayanan §9.2, synopsis RL-9.03. The reciprocal Gamma formulation
retains the removable values of the literal Gamma quotient. -/
theorem regularizedGaussHypergeometric_neg_one_kummer (a b : ℂ) :
    regularizedGaussHypergeometric a b (1 + a - b) (-1) =
      Real.sqrt Real.pi * (2 : ℂ) ^ (-a) /
        (Gamma ((1 + a) / 2) * Gamma (1 + a / 2 - b)) := by
  sorry

/-- Natural-order convergence of Kummer's series on its full convergence half-plane,
Rao–Lakshminarayanan §9.2, synopsis RL-9.03. This includes `1/2 ≤ Re(b) < 1`,
where absolute convergence need not hold. -/
theorem tendsto_sum_gaussHypergeometricCoeff_neg_one_kummer {a b : ℂ}
    (hc : ∀ n : ℕ, 1 + a - b ≠ -(n : ℂ)) (hb : b.re < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N,
      gaussHypergeometricCoeff a b (1 + a - b) n * (-1 : ℂ) ^ n) atTop
      (𝓝 (Gamma (1 + a - b) * Real.sqrt Real.pi * (2 : ℂ) ^ (-a) /
        (Gamma ((1 + a) / 2) * Gamma (1 + a / 2 - b)))) := by
  sorry

end DLMF.Hypergeometric
