/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.GaussSeries

/-!
# A combined-index double series reduces to a Gauss function

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
(7.8)–(7.15), pp. 7-4–7-5, synopsis RL-7.02. Absolute convergence permits
regrouping by total degree, where the binomial theorem gives `(x+y)^n`.
-/

@[expose] public noncomputable section
namespace DLMF.Hypergeometric

/-- The combined-index double hypergeometric series has the Gauss sum argument,
Rao–Lakshminarayanan (7.8)–(7.15), synopsis RL-7.02. The domain is the open
absolute-convergence diamond, so `HasSum` has its usual unconditional meaning. -/
theorem hasSum_double_pochhammer_eq_ordinaryHypergeometric_add {a b c x y : ℂ}
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun mn : ℕ × ℕ =>
      pochhammer a (mn.1 + mn.2) * pochhammer b (mn.1 + mn.2) /
        (pochhammer c (mn.1 + mn.2) * mn.1.factorial * mn.2.factorial) *
          x ^ mn.1 * y ^ mn.2)
      (ordinaryHypergeometric a b c (x + y)) := by
  sorry

end DLMF.Hypergeometric
