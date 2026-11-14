/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.GaussEquation

/-!
# The infinity-solution Wronskian on its full complex branch domain

Rao and Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 1,
equations (1.58)–(1.80), pp. 1-10–1-13, synopsis RL-1.09. The exterior disk is
intersected with the principal slit plane, rather than only the right half-plane.
-/

@[expose] public noncomputable section

open Complex

namespace DLMF.Hypergeometric

/-- The infinity-pair Wronskian on the whole slit exterior disk. In the nonresonant
case `a-b∉ℤ`, its coefficient and both power factors are nonzero, giving the local
fundamental pair at every complex infinity germ on this branch.
Rao–Lakshminarayanan (1.58)–(1.80), pp. 1-10–1-13, synopsis RL-1.09. -/
theorem infinity_wronskian_slit {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, b - a + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖) (hslit : z ∈ slitPlane) :
    solutionWronskian (infinityFirst a b c) (infinityFirst b a c) z =
      (a - b) * z ^ (-c) * (z - 1) ^ (c - a - b - 1) := by
  sorry

end DLMF.Hypergeometric
