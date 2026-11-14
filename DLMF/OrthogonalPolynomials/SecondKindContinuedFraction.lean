/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.QuadratureAndKernels
public import DLMF.OrthogonalPolynomials.ContinuedFractions

/-!
# The continuants of the orthogonal-polynomial Jacobi fraction

Andrews, Askey and Roy, *Special Functions*, Theorems 5.5.2–5.5.4, pp. 256–258
(synopsis AAR-5.5.2–5.5.6). The existing `polynomialFraction` supplies the actual
Mathlib continuants. Its first partial numerator is the total mass and all later
partial numerators are the negatives of the monic recurrence coefficients.
-/

@[expose] public section

open Polynomial MeasureTheory

namespace DLMF.OrthogonalPolynomials

/-- Numerator and denominator continuants are respectively the canonical second-kind
polynomial and the monic orthogonal polynomial. Andrews–Askey–Roy,
*Special Functions*, Theorems 5.5.2–5.5.4, pp. 256–258
(synopsis AAR-5.5.2–5.5.6). Index zero is included, with numerator zero and denominator one. -/
theorem polynomialFraction_jacobi_continuants {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (hmonic : ∀ n, (p n).Monic)
    {α β : ℕ → ℝ} (hfirst : p 1 = X - C (α 0))
    (hrec : ∀ n, p (n + 2) = (X - C (α (n + 1))) * p (n + 1) -
      C (β (n + 1)) * p n) (n : ℕ) (z : ℂ) :
    let F := polynomialFraction
      (fun j => if j = 0 then (μ.real Set.univ : ℂ) else -(β j : ℂ))
      (fun j => z - α j)
    F.nums n = (secondKindPolynomial μ (p n)).eval₂ (algebraMap ℝ ℂ) z ∧
      F.dens n = (p n).eval₂ (algebraMap ℝ ℂ) z := by
  sorry

end DLMF.OrthogonalPolynomials
