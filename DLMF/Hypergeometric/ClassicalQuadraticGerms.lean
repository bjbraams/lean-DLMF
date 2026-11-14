/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.GaussSeries

/-!
# The classical quadratic transformations as analytic germs

Andrews, Askey and Roy, *Special Functions*, §3.1, (3.1.1) and (3.1.3),
pp. 125–131 (synopsis AAR-3.1.1–3.1.3). Both sides use the branch equal
to one for the elementary power at zero. Compatible continuation preserves
these germ identities; disconnected simultaneous convergence regions are avoided.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace DLMF.Hypergeometric

/-- The well-poised quadratic transformation as a coherent germ at zero.
Andrews–Askey–Roy, equation (3.1.1). -/
theorem eventuallyEq_quadratic_well_poised (a b : ℂ)
    (hc : ∀ k : ℕ, 1 + a - b ≠ -(k : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      ordinaryHypergeometric a b (1 + a - b) z =
        (1 - z) ^ (-a) * ordinaryHypergeometric (a / 2) ((a + 1) / 2 - b)
          (1 + a - b) (-4 * z / (1 - z) ^ 2) := by
  sorry

/-- The doubled-lower-parameter quadratic transformation as a coherent germ at zero.
Andrews–Askey–Roy, equation (3.1.3). -/
theorem eventuallyEq_quadratic_double_lower (a b : ℂ)
    (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ))
    (hc' : ∀ k : ℕ, a + 1 / 2 ≠ -(k : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      ordinaryHypergeometric a b (2 * a) z =
        (1 - z / 2) ^ (-b) * ordinaryHypergeometric (b / 2) ((b + 1) / 2)
          (a + 1 / 2) ((z / (2 - z)) ^ 2) := by
  sorry

end DLMF.Hypergeometric
