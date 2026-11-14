/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.HeunFunctions

/-!
# Exact-degree criteria for Heun polynomials

Kristensson, *Second Order Differential Equations*, Chapter 8, §8.3, p. 146.
The leading coefficient is required to be nonzero. The accessory equation is
retained as an undivided polynomial, including at the three marked accessory
values; it is not replaced by a rational equation that excludes them.
-/

@[expose] public noncomputable section

open Set Polynomial Finset
open scoped BigOperators

namespace DLMF.Heun

/-- A canonical normalized Heun sequence terminates in degree exactly `N` precisely
when its top coefficient is nonzero, its next coefficient is zero, and one infinity
exponent is `-N`. Kristensson, Chapter 8, §8.3, p. 146. -/
theorem heunLocalCoeff_terminates_iff {A q α β c d : ℂ} (hA : A ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (N : ℕ) :
    (heunLocalCoeff A q α β c d N ≠ 0 ∧
      ∀ j : ℕ, N < j → heunLocalCoeff A q α β c d j = 0) ↔
      heunLocalCoeff A q α β c d N ≠ 0 ∧
      heunLocalCoeff A q α β c d (N + 1) = 0 ∧ (N + α) * (N + β) = 0 := by
  sorry

/-- The coefficient termination criterion is equivalent to a genuine normalized
polynomial solution of exact degree `N`. Kristensson, Chapter 8, §8.3, p. 146.
The arbitrary accessory parameter is `q`; no product factorization is assumed. -/
theorem exists_heunPolynomial_iff {A q α β c d : ℂ}
    (hA : A ≠ 0) (hA₁ : A ≠ 1) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (N : ℕ) :
    (∃ P : ℂ[X], P.natDegree = N ∧ P.coeff 0 = 1 ∧
      IsHeunSolutionOn A q α β c d (heunEpsilon α β c d)
        (fun z => P.eval z) {z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ z ≠ A}) ↔
      heunLocalCoeff A q α β c d N ≠ 0 ∧
      heunLocalCoeff A q α β c d (N + 1) = 0 ∧ (N + α) * (N + β) = 0 := by
  sorry

/-- The next local coefficient, after clearing its nonzero recurrence denominators,
is the characteristic polynomial of the canonical finite Heun matrix.
Kristensson, Chapter 8, §8.3, p. 146; DLMF 31.5.1–31.5.2. -/
theorem charpoly_heunPolyMatrix_eval_eq {A q β c d : ℂ} (hA : A ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (N : ℕ) :
    (heunPolyMatrix A β c d N).charpoly.eval q =
      (∏ j ∈ range (N + 1), heunRecurrenceR A c j) *
        heunLocalCoeff A q (-(N : ℂ)) β c d (N + 1) := by
  sorry

/-- The canonical finite determinant condition is exactly the vanishing of the next
series coefficient. Kristensson, Chapter 8, §8.3, p. 146. -/
theorem charpoly_heunPolyMatrix_isRoot_iff {A q β c d : ℂ} (hA : A ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (N : ℕ) :
    (heunPolyMatrix A β c d N).charpoly.IsRoot q ↔
      heunLocalCoeff A q (-(N : ℂ)) β c d (N + 1) = 0 := by
  sorry

/-- In degree one, the book's normalized accessory equation is polynomial and stays
valid at `h=0,1,A`. Nonzero `alpha*beta` is needed for cancellation of that factor;
without it this normalized accessory parametrization cannot represent degree one.
Kristensson, Chapter 8, §8.3, p. 146. -/
theorem heunLocalCoeff_two_eq_zero_iff_accessory_quadratic
    {A α β c d e h : ℂ} (hA : A ≠ 0) (hc : c ≠ 0) (hc₁ : c ≠ -1)
    (hexponent : α = -1 ∨ β = -1) (hproduct : α * β ≠ 0)
    (hbalance : α + β + 1 = c + d + e) :
    heunLocalCoeff A (α * β * h) α β c d 2 = 0 ↔
      (A - h) * (h - 1) * c + h * (A - h) * d + h * (1 - h) * e = 0 := by
  sorry

end DLMF.Heun
