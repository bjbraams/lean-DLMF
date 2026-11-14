/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quantitative error in an asymptotic real inverse

Olver, *Asymptotics and Special Functions*, Chapter 1, Theorem 5.1, p. 13,
synopsis O-1.07. An eventual error constant `k` transfers to any strictly
larger inverse error constant, with a common sufficiently large threshold.
-/

@[expose] public section

open Filter Asymptotics

namespace Real

/-- A continuous strictly increasing map asymptotic to the identity has a unique large
inverse, with the quantitative transferred error bound. Olver, Chapter 1,
Theorem 5.1, p. 13, synopsis O-1.07. The error power may be any fixed real number. -/
theorem existsUnique_root_and_error_le_of_isEquivalent {a k l p : ℝ}
    (ha : 0 < a) (hk : 0 ≤ k) (hkl : k < l) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici a)) (hmono : StrictMonoOn f (Set.Ici a))
    (hequiv : f ~[atTop] (fun t : ℝ => t))
    (herror : ∀ᶠ t : ℝ in atTop, |f t - t| ≤ k * t ^ (-p)) :
    ∃ U > 0, ∀ u : ℝ, U ≤ u →
      (∃! t : Set.Ici a, f t = u) ∧
        ∀ t : ℝ, a ≤ t → f t = u → |t - u| ≤ l * u ^ (-p) := by
  sorry

end Real
