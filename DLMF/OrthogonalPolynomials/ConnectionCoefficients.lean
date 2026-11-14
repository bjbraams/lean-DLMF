/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations

/-!
# Jacobi connection coefficients with removable factors canceled

Andrews, Askey and Roy, *Special Functions*, §7.1. The all-parameter Jacobi
polynomial continuation is used for the polynomial being expanded. In the
closed coefficients, `(α+β+1)_k/(α+β+1)` is canceled before specialization.
-/

@[expose] public section

open MeasureTheory DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The Fourier coefficient of one Jacobi polynomial in a positive Jacobi-weight basis.
Andrews–Askey–Roy, *Special Functions*, Lemma 7.1.1
(synopsis AAR-7.1.1–7.1.4'). -/
def jacobiConnectionCoefficient (α β : ℝ) (γ δ : ℂ) (n k : ℕ) : ℂ :=
  (∫ x : ℝ in Set.Ioo (-1) 1,
    jacobiExtended γ δ n x * jacobiExtended α β k x *
      ((1 - x) ^ α * (1 + x) ^ β : ℝ)) /
  (∫ x : ℝ in Set.Ioo (-1) 1,
    jacobiExtended α β k x ^ 2 * ((1 - x) ^ α * (1 + x) ^ β : ℝ))

/-- The explicit Jacobi-weight integral quotient. -/
theorem jacobiConnectionCoefficient_def (α β : ℝ) (γ δ : ℂ) (n k : ℕ) :
    jacobiConnectionCoefficient α β γ δ n k =
      (∫ x : ℝ in Set.Ioo (-1) 1,
        jacobiExtended γ δ n x * jacobiExtended α β k x *
          ((1 - x) ^ α * (1 + x) ^ β : ℝ)) /
      (∫ x : ℝ in Set.Ioo (-1) 1,
        jacobiExtended α β k x ^ 2 * ((1 - x) ^ α * (1 + x) ^ β : ℝ)) := rfl

/-- The integral connection formula for every continued numerator parameter.
Andrews–Askey–Roy, *Special Functions*, Lemma 7.1.1
(synopsis AAR-7.1.1–7.1.4'). -/
theorem jacobiExtended_connection {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (γ δ : ℂ) (n : ℕ) (z : ℂ) :
    jacobiExtended γ δ n z = ∑ k ∈ Finset.range (n + 1),
      jacobiConnectionCoefficient α β γ δ n k * jacobiExtended α β k z := by
  sorry

/-- Closed connection coefficients when the first parameter is fixed, including
`α+β+1=0` by cancellation. Andrews–Askey–Roy, *Special Functions*, Theorem 7.1.2
(synopsis AAR-7.1.1–7.1.4'). -/
theorem jacobiExtended_equal_first_connection {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (δ : ℂ) (n : ℕ) (z : ℂ) :
    jacobiExtended α δ n z =
      pochhammer ((α : ℂ) + 1) n / pochhammer ((α : ℂ) + β + 2) n *
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ (n - k) * pochhammer (δ - β) (n - k) *
          (if k = 0 then 1 else
            pochhammer ((α : ℂ) + β + 2) (k - 1) * ((α : ℂ) + β + 2 * k + 1)) *
          pochhammer ((α : ℂ) + δ + n + 1) k /
          ((n - k).factorial * pochhammer ((α : ℂ) + 1) k *
            pochhammer ((α : ℂ) + β + n + 2) k)) * jacobiExtended α β k z := by
  sorry

/-- The reflected closed connection formula with the second parameter fixed.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.1.3
(synopsis AAR-7.1.1–7.1.4'). -/
theorem jacobiExtended_equal_second_connection {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (γ : ℂ) (n : ℕ) (z : ℂ) :
    jacobiExtended γ β n z =
      pochhammer ((β : ℂ) + 1) n / pochhammer ((α : ℂ) + β + 2) n *
      ∑ k ∈ Finset.range (n + 1),
        (pochhammer (γ - α) (n - k) *
          (if k = 0 then 1 else
            pochhammer ((α : ℂ) + β + 2) (k - 1) * ((α : ℂ) + β + 2 * k + 1)) *
          pochhammer ((β : ℂ) + γ + n + 1) k /
          ((n - k).factorial * pochhammer ((β : ℂ) + 1) k *
            pochhammer ((α : ℂ) + β + n + 2) k)) * jacobiExtended α β k z := by
  sorry

end DLMF.OrthogonalPolynomials
