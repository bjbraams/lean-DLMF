/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Monotonicity of an exponential difference quotient

The corrected exponent sign in Andrews, Askey and Roy, *Special Functions*,
Lemma 10.2.3. The parameter in the denominator is allowed to be real.
-/

@[expose] public section

namespace Real

/-- The exponential ratio is nonincreasing on the positive ray.
Andrews–Askey–Roy, *Special Functions*, Lemma 10.2.3
(synopsis AAR-10.1–10.2.4). -/
theorem antitoneOn_exp_sub_div_one_sub_exp {lam mu k : ℝ}
    (h₀ : 0 < mu - lam) (h₁ : mu - lam < k) (hsum : 1 ≤ mu + lam) :
    AntitoneOn (fun t : ℝ =>
      (exp (-mu * t) - exp (-(lam + k) * t)) / (1 - exp (-(k + 1) * t)))
      (Set.Ioi 0) := by
  sorry

end Real
