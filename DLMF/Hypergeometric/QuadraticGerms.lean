/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries
public import DLMF.Hypergeometric.Basic.GaussSeries

/-!
# The inverse square-root quadratic transformation as a coherent germ

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
(8.25)–(8.26), p. 8-8, synopsis RL-8.13. The germ at zero avoids choosing
incompatible square roots on the two sides. The finite form retains only
nonzero lower factors through the actual terminating degree.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology

namespace DLMF.Hypergeometric

/-- The inverse quadratic identity on a full complex neighborhood of zero, with
principal powers continued from the value one there.
Rao–Lakshminarayanan (8.25), synopsis RL-8.13. -/
theorem eventuallyEq_quadratic_inverse_sqrt (a b : ℂ)
    (hC : ∀ k : ℕ, 2 * b ≠ -(k : ℂ))
    (hC' : ∀ k : ℕ, b + 1 / 2 ≠ -(k : ℂ)) :
    ∀ᶠ t : ℂ in 𝓝 0,
      ordinaryHypergeometric a b (2 * b) (-4 * t / (1 - t) ^ 2) =
        (1 - t) ^ (2 * a) *
          ordinaryHypergeometric a (a + 1 / 2 - b) (b + 1 / 2) (t ^ 2) := by
  sorry

/-- The finite inverse quadratic identity after clearing its argument denominator.
Only the retained lower factors must be nonzero. The exclusion of `t=1` belongs
to the displayed rational argument, not to a branch of a power.
Rao–Lakshminarayanan (8.25)–(8.26), synopsis RL-8.13. -/
theorem generalizedHypergeometricTruncated_quadratic_inverse_sqrt (N : ℕ) (b : ℂ)
    (hC : ∀ k ≤ N, pochhammer (2 * b) k * pochhammer (b + 1 / 2) k ≠ 0)
    {t : ℂ} (ht : t ≠ 1) :
    (1 - t) ^ (2 * N) * generalizedHypergeometricTruncated N {-(N : ℂ), b} {2 * b}
        (-4 * t / (1 - t) ^ 2) =
      generalizedHypergeometricTruncated N {-(N : ℂ), -(N : ℂ) + 1 / 2 - b}
        {b + 1 / 2} (t ^ 2) := by
  sorry

end DLMF.Hypergeometric
