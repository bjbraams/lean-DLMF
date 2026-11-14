/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.RamanujanMaster

/-!
# Carlson uniqueness for Hardy's Ramanujan class

Andrews, Askey and Roy, *Special Functions*, Corollary 10.12.3,
pp. 548–549, synopsis AAR-10.12.1–10.12.8. The class is the canonical
lean-codes `Complex.RamanujanClass`; its growth controls imply Carlson's hypotheses.
-/

@[expose] public section

namespace Complex.RamanujanClass

/-- Natural-number data uniquely determine a function in Hardy's Ramanujan class on its full
half-plane. Andrews–Askey–Roy, Corollary 10.12.3, synopsis AAR-10.12.1–10.12.8.
Carlson's theorem first gives the closed right half-plane; the identity principle extends it. -/
theorem eq_zero_of_natCast_eq_zero {φ : ℂ → ℂ} {δ C P A : ℝ}
    (hφ : Complex.RamanujanClass φ δ C P A) (hzero : ∀ n : ℕ, φ n = 0) :
    ∀ z : ℂ, -δ < z.re → φ z = 0 := by
  sorry

end Complex.RamanujanClass
