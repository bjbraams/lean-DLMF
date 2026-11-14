/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations

/-!
# The Jacobi multiplication matrix

Multiplication by the argument is tridiagonal in the Jacobi basis. The degree-zero
coefficients have their removable factors cancelled before totalization, so the
Legendre and the `alpha+beta=-1` cases are retained. Source: Kristensson,
*Second Order Differential Equations*, Chapter 5, (5.29), p. 104.
-/

@[expose] public noncomputable section

open Complex MeasureTheory
open scoped Real

namespace DLMF.OrthogonalPolynomials.JacobiMultiplication

/-- The upper coefficient, with its removable degree-zero factor cancelled.
Kristensson, Chapter 5, (5.29), p. 104. -/
def upper (α β : ℂ) : ℕ → ℂ
  | 0 => 2 / (α + β + 2)
  | n + 1 => 2 * (n + 2) * (n + α + β + 2) /
      ((2 * n + α + β + 3) * (2 * n + α + β + 4))

/-- The regular degree-zero upper coefficient. -/
@[simp] theorem upper_zero (α β : ℂ) : upper α β 0 = 2 / (α + β + 2) := rfl

/-- The upper coefficient at positive degree. -/
theorem upper_succ (α β : ℂ) (n : ℕ) : upper α β (n + 1) =
    2 * (n + 2) * (n + α + β + 2) /
      ((2 * n + α + β + 3) * (2 * n + α + β + 4)) := rfl

/-- The diagonal coefficient, with the removable degree-zero factor cancelled.
Kristensson, Chapter 5, (5.29), p. 104. -/
def diagonal (α β : ℂ) : ℕ → ℂ
  | 0 => (β - α) / (α + β + 2)
  | n + 1 => (β ^ 2 - α ^ 2) / ((2 * n + α + β + 2) * (2 * n + α + β + 4))

/-- The regular degree-zero diagonal coefficient. -/
@[simp] theorem diagonal_zero (α β : ℂ) :
    diagonal α β 0 = (β - α) / (α + β + 2) := rfl

/-- The diagonal coefficient at positive degree. -/
theorem diagonal_succ (α β : ℂ) (n : ℕ) : diagonal α β (n + 1) =
    (β ^ 2 - α ^ 2) / ((2 * n + α + β + 2) * (2 * n + α + β + 4)) := rfl

/-- The lower coefficient vanishes at degree zero, where there is no negative-degree
polynomial. Kristensson, Chapter 5, (5.29), p. 104. -/
def lower (α β : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => 2 * (n + α + 1) * (n + β + 1) /
      ((2 * n + α + β + 2) * (2 * n + α + β + 3))

/-- There is no lower coefficient at degree zero. -/
@[simp] theorem lower_zero (α β : ℂ) : lower α β 0 = 0 := rfl

/-- The lower coefficient at positive degree. -/
theorem lower_succ (α β : ℂ) (n : ℕ) : lower α β (n + 1) =
    2 * (n + α + 1) * (n + β + 1) /
      ((2 * n + α + β + 2) * (2 * n + α + β + 3)) := rfl

end DLMF.OrthogonalPolynomials.JacobiMultiplication

namespace DLMF.OrthogonalPolynomials

/-- The first-degree continued Jacobi polynomial, at every complex parameter pair.
Kristensson, Chapter 5, §5.8.1, pp. 93–95. -/
theorem jacobiExtended_degree_one (α β z : ℂ) :
    jacobiExtended α β 1 z = (α - β + (α + β + 2) * z) / 2 := by
  norm_num [jacobiExtended, DLMF.Hypergeometric.pochhammer, Finset.sum_range_succ]
  ring

/-- Multiplication by the argument in the continued Jacobi basis. At degree zero
only the genuine denominator `alpha+beta+2` is excluded. At positive degree the
three displayed recurrence denominators are excluded; cleared identities remain
available at their zeros. Kristensson, Chapter 5, (5.29), p. 104. -/
theorem mul_jacobiExtended (α β : ℂ) (n : ℕ) (z : ℂ)
    (hden : if n = 0 then α + β + 2 ≠ 0 else
      (2 * n + α + β) * (2 * n + α + β + 1) * (2 * n + α + β + 2) ≠ 0) :
    z * jacobiExtended α β n z =
      JacobiMultiplication.upper α β n * jacobiExtended α β (n + 1) z +
      JacobiMultiplication.diagonal α β n * jacobiExtended α β n z +
      JacobiMultiplication.lower α β n * jacobiExtended α β (n - 1) z := by
  sorry

/-- The weighted multiplication matrix is tridiagonal, including all degree-zero
removable cases. The last integral is the squared norm `N_k`, whose Gamma value
is `jacobi_norm_all`. Kristensson, Chapter 5, (5.29), p. 104. -/
theorem integral_mul_jacobiExtended_mul_jacobiExtended {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n k : ℕ) :
    (∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * jacobiExtended α β n x * jacobiExtended α β k x *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) =
      (if k = n + 1 then JacobiMultiplication.upper α β n else
        if k = n then JacobiMultiplication.diagonal α β n else
          if k + 1 = n then JacobiMultiplication.lower α β n else 0) *
      ∫ x : ℝ in (-1 : ℝ)..1, jacobiExtended α β k x ^ 2 *
        (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) := by
  sorry

end DLMF.OrthogonalPolynomials
