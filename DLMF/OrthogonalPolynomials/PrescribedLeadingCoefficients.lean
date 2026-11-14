/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.MeasureConstruction

/-!
# Orthogonal polynomials with prescribed leading coefficients

Olver, *Asymptotics and Special Functions*, Chapter 2, Theorem 6.1, p. 46,
synopsis O-2.12. Finite moments and infinite essential support are the intrinsic
measure hypotheses, including positive weights on nonempty intervals.
-/

@[expose] public noncomputable section

open MeasureTheory Polynomial

namespace DLMF.OrthogonalPolynomials

/-- Prescribing every nonzero leading coefficient determines a unique orthogonal family.
Olver, Chapter 2, Theorem 6.1, synopsis O-2.12; Andrews–Askey–Roy, §5.2,
synopsis AAR-5.2.2–5.2.6. -/
theorem existsUnique_orthogonal_polynomials_leadingCoeff (μ : Measure ℝ)
    (hmoments : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    (hinfinite : ∀ s : Finset ℝ, μ (s : Set ℝ)ᶜ ≠ 0)
    (κ : ℕ → ℝ) (hκ : ∀ n, κ n ≠ 0) :
    ∃! p : ℕ → ℝ[X], IsOrthogonalPolynomials μ p ∧ ∀ n, (p n).leadingCoeff = κ n := by
  sorry

end DLMF.OrthogonalPolynomials
