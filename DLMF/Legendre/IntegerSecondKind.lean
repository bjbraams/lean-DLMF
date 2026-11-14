/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Neumann
public import DLMF.Legendre.Basic.Associated

/-!
# Integer-degree second-kind Legendre functions and their polynomial part

Temme, *Special Functions* (1996), Chapter 8, equations (8.24)–(8.33),
pages 200–202. The explicit polynomial identities have no branch restriction;
Neumann's integral uses the maximal ordinary integer-degree domain, the complement
of the real interval `[-1,1]`. On the interval its symmetric principal value is Ferrers Q.
-/

@[expose] public noncomputable section

open Complex Filter Set Finset
open scoped Real Topology

namespace DLMF.Legendre

/-- The convolution expression for Temme's `W_{n-1}`, using the canonical polynomial part.
Temme (8.25)–(8.28), synopsis TEM-08-04. -/
theorem legendreQPoly_eval_eq_convolution (n : ℕ) (z : ℂ) :
    (legendreQPoly n).eval z = ∑ k ∈ Icc 1 n,
      DLMF.OrthogonalPolynomials.legendrePolynomialP (k - 1) z *
        DLMF.OrthogonalPolynomials.legendrePolynomialP (n - k) z / (k : ℂ) := by
  sorry

/-- The expansion of the polynomial part in lower Legendre polynomials.
Temme (8.29)–(8.32), synopsis TEM-08-04. -/
theorem legendreQPoly_eval_eq_legendre_sum (n : ℕ) (z : ℂ) :
    (legendreQPoly n).eval z = ∑ k ∈ range n,
      ((2 * k + 1 : ℕ) : ℂ) * (1 - (-1 : ℂ) ^ (n + k)) /
        (((n - k : ℕ) : ℂ) * ((n + k + 1 : ℕ) : ℂ)) *
          DLMF.OrthogonalPolynomials.legendrePolynomialP k z := by
  sorry

/-- Neumann's kernel is integrable throughout the complement of the closed real interval.
Temme (8.33), synopsis TEM-08-04. -/
theorem intervalIntegrable_neumann_kernel (n : ℕ) {z : ℂ}
    (hz : z ∉ ofReal '' Icc (-1 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ =>
      DLMF.OrthogonalPolynomials.legendrePolynomialP n t / (z - t))
        MeasureTheory.volume (-1) 1 := by
  sorry

/-- Neumann's representation on the full natural integer-degree domain.
Temme (8.33), synopsis TEM-08-04. -/
theorem legendreQ_nat_eq_neumann_integral (n : ℕ) {z : ℂ}
    (hz : z ∉ ofReal '' Icc (-1 : ℝ) 1) :
    legendreQ n z = (1 / 2 : ℂ) *
      ∫ t in (-1 : ℝ)..1,
        DLMF.OrthogonalPolynomials.legendrePolynomialP n t / (z - t) := by
  sorry

/-- The symmetric principal value of Neumann's integral is Ferrers Q on the cut.
Temme (8.33) and its cut interpretation, synopsis TEM-08-04. -/
theorem tendsto_neumann_principalValue_ferrersQ (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun ε : ℝ => (1 / 2 : ℂ) *
      ((∫ t in (-1 : ℝ)..(x - ε),
          DLMF.OrthogonalPolynomials.legendrePolynomialP n t / ((x : ℂ) - t)) +
        ∫ t in (x + ε)..(1 : ℝ),
          DLMF.OrthogonalPolynomials.legendrePolynomialP n t / ((x : ℂ) - t)))
      (𝓝[>] 0) (𝓝 (ferrersQ n 0 x)) := by
  sorry

end DLMF.Legendre
