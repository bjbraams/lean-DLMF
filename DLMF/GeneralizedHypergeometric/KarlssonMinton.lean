/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic

/-!
# The finite classical Karlsson–Minton sum

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
(7.73)–(7.93), in particular (7.80), pp. 7-15–7-17, synopsis RL-7.11.
Integral shifts have total weight `M`; all retained lower factors, rather
than every possible lower factor, are required nonzero.
-/

@[expose] public noncomputable section
namespace DLMF.Hypergeometric

/-- The terminating classical Karlsson–Minton evaluation,
Rao–Lakshminarayanan (7.80), synopsis RL-7.11. Empty parameter lists are allowed. -/
theorem generalizedHypergeometricTruncated_karlsson_minton {p : ℕ}
    (b : Fin p → ℂ) (m : Fin p → ℕ)
    (hreg : ∀ k ≤ ∑ i, m i, pochhammerProduct (parametersOfFin b) k ≠ 0) :
    generalizedHypergeometricTruncated (∑ i, m i)
      (-((∑ i, m i : ℕ) : ℂ) ::ₘ parametersOfFin (fun i => b i + (m i : ℂ)))
      (parametersOfFin b) 1 =
        (-1 : ℂ) ^ (∑ i, m i) * ((∑ i, m i : ℕ).factorial : ℂ) /
          ∏ i, pochhammer (b i) (m i) := by
  sorry

end DLMF.Hypergeometric
