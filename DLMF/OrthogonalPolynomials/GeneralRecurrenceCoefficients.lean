/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.NormsAndKernels

/-!
# Explicit three-term coefficients for an arbitrary orthogonal sequence

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 9, Theorem 9.4,
equations (9.10)–(9.12). The formulas use actual leading and subleading coefficients,
so no monic normalization is imposed.
-/

@[expose] public noncomputable section

open Polynomial MeasureTheory

namespace DLMF.OrthogonalPolynomials

/-- The explicit three-term recurrence of an orthogonal polynomial sequence.
Duverney Theorem 9.4, equations (9.10)–(9.12), synopsis DU-9.02. -/
theorem three_term_recurrence_explicit {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (n : ℕ) :
    C ((p (n + 1)).leadingCoeff / (p (n + 2)).leadingCoeff) * p (n + 2) =
      (X + C ((p (n + 2)).coeff (n + 1) / (p (n + 2)).leadingCoeff -
        (p (n + 1)).coeff n / (p (n + 1)).leadingCoeff)) * p (n + 1) -
      C (squaredNorm μ p (n + 1) * (p n).leadingCoeff /
        (squaredNorm μ p n * (p (n + 1)).leadingCoeff)) * p n := by
  sorry

end DLMF.OrthogonalPolynomials
