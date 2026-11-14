/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Differentiation of asymptotic equivalents under monotonicity

The monotone derivative theorem in Olver, *Asymptotics and Special Functions*,
Chapter 1, Theorem 4.1, p. 9. Real asymptotic equivalents require a regularity
condition on the derivative before differentiation is valid.
-/

@[expose] public section

open Filter Set
open scoped Topology Asymptotics Real

namespace Asymptotics

/-- Olver, Chapter 1, Theorem 4.1, p. 9: an eventually nondecreasing derivative
allows differentiation of an equivalent to `x^p`, for real `p≥1`. -/
theorem deriv_isEquivalent_rpow_of_monotone {f : ℝ → ℝ} {a p : ℝ}
    (hp : 1 ≤ p) (hf : DifferentiableOn ℝ f (Ioi a))
    (hmono : MonotoneOn (deriv f) (Ioi a))
    (hequiv : f ~[atTop] fun x => x ^ p) :
    deriv f ~[atTop] fun x => p * x ^ (p - 1) := by
  sorry

end Asymptotics
