/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic

/-!
# Abel's Wronskian form for arbitrary Gauss solutions

Andrews, Askey and Roy, *Special Functions*, Lemma 3.2.6, p. 135
(synopsis AAR-3.2.3–3.2.11). The branch domain is connected and excludes both
principal logarithmic cuts. No condition on exponent differences is needed.
-/

@[expose] public section

open Complex

namespace DLMF.Hypergeometric

/-- The Wronskian of any two Gauss solutions is a constant multiple of the explicit
power factor. Andrews–Askey–Roy, *Special Functions*, Lemma 3.2.6, p. 135
(synopsis AAR-3.2.3–3.2.11). Both functions may be dependent, giving constant zero. -/
theorem exists_solutionWronskian_eq_cpow (a b c : ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hconnected : IsPreconnected U)
    (hbranch : ∀ z ∈ U, z ∈ slitPlane ∧ 1 - z ∈ slitPlane)
    (f g : ℂ → ℂ) (hf : ContDiffOn ℂ 2 f U) (hg : ContDiffOn ℂ 2 g U)
    (hfeq : ∀ z ∈ U, gaussOperator a b c f z = 0)
    (hgeq : ∀ z ∈ U, gaussOperator a b c g z = 0) :
    ∃ C : ℂ, ∀ z ∈ U,
      solutionWronskian f g z = C * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  sorry

end DLMF.Hypergeometric
