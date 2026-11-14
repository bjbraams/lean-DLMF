/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.NormsAndKernels

/-!
# Weighted least-squares projection onto polynomial spaces

Olver, *Asymptotics and Special Functions*, Chapter 2, Exercise 6.3, p. 48,
synopsis O-2.14; Andrews, Askey and Roy, *Special Functions*, §5.7.
The exact Pythagorean identity also characterizes equality and uniqueness.
-/

@[expose] public noncomputable section

open MeasureTheory Polynomial Finset

namespace DLMF.OrthogonalPolynomials

/-- Orthogonal Fourier coefficients give the unique best polynomial approximation in weighted
`L²`. The displayed error identity implies minimality and characterizes every equality case.
Olver, Chapter 2, Exercise 6.3, synopsis O-2.14; Andrews–Askey–Roy, §5.7,
synopsis AAR-5.7.1–5.7.4. -/
theorem polynomial_projection_leastSquares {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (hp : IsOrthogonalPolynomials μ p) {f : ℝ → ℝ} (hf : MemLp f 2 μ) (N : ℕ) :
    let P : ℝ[X] := ∑ j ∈ range (N + 1),
      C ((∫ x, f x * (p j).eval x ∂μ) / squaredNorm μ p j) * p j
    P.degree ≤ N ∧ ∀ Q : ℝ[X], Q.degree ≤ N →
      (∫ x, (f x - Q.eval x) ^ 2 ∂μ) = (∫ x, (f x - P.eval x) ^ 2 ∂μ) +
        (∫ x, (P.eval x - Q.eval x) ^ 2 ∂μ) ∧
      (∫ x, (f x - P.eval x) ^ 2 ∂μ) ≤ (∫ x, (f x - Q.eval x) ^ 2 ∂μ) ∧
      ((∫ x, (f x - P.eval x) ^ 2 ∂μ) = (∫ x, (f x - Q.eval x) ^ 2 ∂μ) ↔ Q = P) := by
  sorry

end DLMF.OrthogonalPolynomials
