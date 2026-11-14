/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.LegendreSeries

/-!
# The leading compact-uniform Legendre Darboux formula

Olver, *Asymptotics and Special Functions*, Chapter 4, §8,
pp. 127–130, synopsis O-4.12. The leading amplitude uses n rather than
an unexpanded Gamma quotient.
-/

@[expose] public noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The leading Legendre asymptotic has an absolute O(n^(-3/2)) error uniformly away from
both angular endpoints. Olver, Chapter 4, §8, synopsis O-4.12. -/
theorem legendrePolynomialP_darboux_leading_uniform {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ n ≥ A,
      ∀ θ ∈ Set.Icc δ (Real.pi - δ),
        ‖legendrePolynomialP n (Real.cos θ) -
          ((Real.sqrt (2 / (Real.pi * n * Real.sin θ)) *
            Real.cos (((n : ℝ) + 1 / 2) * θ - Real.pi / 4) : ℝ) : ℂ)‖ ≤
          C * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  sorry

end DLMF.OrthogonalPolynomials
