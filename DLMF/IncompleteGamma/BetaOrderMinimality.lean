/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaEndpointData

/-!
# The minimal incomplete-beta solution in a growing upper parameter

Temme, *Special Functions* (1996), Chapter 13, §13.3, Example 5, pages 340–341.
The incomplete beta solution decays relative to the constant solution of its homogeneous
three-term recurrence. This is an order asymptotic, with the argument held fixed.
-/

@[expose] public noncomputable section

open Filter Asymptotics
open scoped Topology Real

namespace DLMF.Statistical.Real

/-- The incomplete-beta equivalent for an upper parameter growing through integers.
Temme Chapter 13, Example 5, pages 340–341, synopsis TEM-13-06. -/
theorem regularizedIncompleteBeta_add_nat_isEquivalent {p q x : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hx1 : x < 1) :
    (fun n : ℕ => regularizedIncompleteBeta (p + n) q x) ~[atTop]
      (fun n : ℕ => ((x ^ ((n : ℝ) + p) * (1 - x) ^ (q - 1) *
        (n : ℝ) ^ (q - 1) / _root_.Real.Gamma q : ℝ) : ℂ)) := by
  sorry

/-- The consecutive upper-parameter ratio tends to the fixed beta argument.
Temme Chapter 13, Example 5, pages 340–341, synopsis TEM-13-06. -/
theorem tendsto_regularizedIncompleteBeta_add_nat_ratio {p q x : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ => regularizedIncompleteBeta (p + (n + 1 : ℕ)) q x /
      regularizedIncompleteBeta (p + n) q x) atTop (𝓝 (x : ℂ)) := by
  sorry

/-- Decay to zero is minimality against the constant solution of the beta recurrence.
Temme Chapter 13, Example 5, pages 340–341, synopsis TEM-13-06. -/
theorem tendsto_regularizedIncompleteBeta_add_nat_zero {p q x : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ => regularizedIncompleteBeta (p + n) q x) atTop (𝓝 0) := by
  sorry

end DLMF.Statistical.Real
