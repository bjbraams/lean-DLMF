/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer

/-!
# Polynomial continuation of Jacobi parameters

The finite binomial formula defines Jacobi polynomials at every complex parameter pair,
including the negative integers occurring in the `SU(2)` matrix coefficients of
Andrews, Askey and Roy, *Special Functions*, §§9.13–9.15. The hypergeometric quotient
`jacobiPolynomialP` has a different totalization at exceptional lower parameters.
-/

@[expose] public section

open DLMF.Hypergeometric

namespace DLMF.OrthogonalPolynomials

/-- Polynomial continuation of Jacobi polynomials in both parameters, using the finite
binomial sum. Andrews–Askey–Roy, *Special Functions*, §§6.3 and 9.14
(synopsis AAR-6.3.1–6.4.3 and AAR-9.11–9.16). -/
noncomputable def jacobiExtended (α β : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1),
    (pochhammer (α + n - k + 1) k / k.factorial) *
      (pochhammer (β + k + 1) (n - k) / (n - k).factorial) *
      (x - 1) ^ (n - k) * (x + 1) ^ k

/-- The finite sum defining polynomially continued Jacobi polynomials. -/
theorem jacobiExtended_def (α β : ℂ) (n : ℕ) (x : ℂ) :
    jacobiExtended α β n x = ((2 : ℂ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1),
      (pochhammer (α + n - k + 1) k / k.factorial) *
        (pochhammer (β + k + 1) (n - k) / (n - k).factorial) *
        (x - 1) ^ (n - k) * (x + 1) ^ k := rfl

/-- The degree-zero polynomially continued Jacobi polynomial is one. -/
@[simp] theorem jacobiExtended_zero (α β x : ℂ) : jacobiExtended α β 0 x = 1 := by
  simp [jacobiExtended, pochhammer]

end DLMF.OrthogonalPolynomials
