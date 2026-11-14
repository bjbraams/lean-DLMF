/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations

/-!
# Gegenbauer norms for the full orthogonality range

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 9,
equations (9.41)–(9.48), permits `-1/2<λ<0` as well as positive `λ`.
The Gamma quotient is interpreted with its actual signs, including degree zero.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.OrthogonalPolynomials

/-- The Gegenbauer squared norm for `λ>-1/2`, `λ≠0`, including negative λ and n=0.
Duverney (9.41)–(9.48), synopsis DU-9.09. -/
theorem ultrasphericalPolynomial_norm_of_nonzero {s : ℝ} (hs : -1 / 2 < s)
    (hs0 : s ≠ 0) (n : ℕ) :
    (∫ t : ℝ in (-1 : ℝ)..1, ultrasphericalPolynomial s n t ^ 2 *
      (1 - (t : ℂ) ^ 2) ^ ((s : ℂ) - 1 / 2)) =
      (2 : ℂ) ^ (1 - 2 * (s : ℂ)) * Real.pi * Gamma (n + 2 * (s : ℂ)) /
        ((n + s) * Gamma (s : ℂ) ^ 2 * n.factorial) := by
  sorry

end DLMF.OrthogonalPolynomials
