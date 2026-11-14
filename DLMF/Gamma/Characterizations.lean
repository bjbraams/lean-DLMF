/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Gamma characterization by an asymptotic ratio

Andrews, Askey and Roy, *Special Functions*, Theorem 1.9.4, p. 36.
-/

@[expose] public section

open Filter

namespace DLMF.Gamma.Real

/-- The gamma functional equation and its normalized translation asymptotic characterize
Euler's gamma function without a convexity assumption. Andrews–Askey–Roy,
*Special Functions*, Theorem 1.9.4, p. 36 (synopsis AAR-1.9.3–1.9.4). -/
theorem eq_Gamma_of_tendsto_ratio {f : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x) (hone : f 1 = 1)
    (hrec : ∀ x : ℝ, 0 < x → f (x + 1) = x * f x)
    (hratio : ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => f (x + n) / ((n : ℝ) ^ x * f n)) atTop (nhds 1)) :
    ∀ x : ℝ, 0 < x → f x = Real.Gamma x := by
  sorry

end DLMF.Gamma.Real
