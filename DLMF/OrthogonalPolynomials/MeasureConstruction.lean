/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.General
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Construction of orthonormal polynomials from a measure

Temme, *Special Functions*, Chapter 6, (6.1)–(6.5), pp. 133–135, and
Andrews, Askey and Roy, *Special Functions*, §§5.2–5.3. Infinite essential
support excludes every finite-support Gram-matrix degeneracy.
-/

@[expose] public section

open MeasureTheory

namespace DLMF.OrthogonalPolynomials

/-- All moments and infinite essential support determine one orthonormal polynomial
sequence with positive leading coefficients. Temme, *Special Functions*, Chapter 6,
(6.1)–(6.5), pp. 133–135 (synopsis TEM-06-01); Andrews–Askey–Roy, §5.2
(synopsis AAR-5.2.2–5.2.6). -/
theorem existsUnique_orthonormal_polynomials (μ : Measure ℝ)
    (hmoments : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    (hinfinite : ∀ s : Finset ℝ, μ (s : Set ℝ)ᶜ ≠ 0) :
    ∃! p : ℕ → Polynomial ℝ, IsOrthogonalPolynomials μ p ∧
      (∀ n : ℕ, ∫ x : ℝ, (p n).eval x ^ 2 ∂μ = 1) ∧
      (∀ n : ℕ, 0 < (p n).leadingCoeff) := by
  sorry

/-- Every zero of an orthogonal polynomial lies strictly inside the convex hull of the
measure's support. Temme, *Special Functions*, Theorems 6.3–6.4, pp. 137–138
(synopsis TEM-06-04); Andrews–Askey–Roy, §5.3 (synopsis AAR-5.3.2–5.4.4).
The existence of polynomials of every degree excludes finite support. -/
theorem eval_eq_zero_mem_interior_convexHull_support
    {μ : Measure ℝ} {p : ℕ → Polynomial ℝ} (hp : IsOrthogonalPolynomials μ p)
    {n : ℕ} {x : ℝ} (hx : (p n).eval x = 0) :
    x ∈ interior (convexHull ℝ μ.support) := by
  sorry

/-- The explicit recurrence of a positively normalized orthonormal family, including the
initial step. Temme, *Special Functions*, Theorem 6.1, equation (6.6), pp. 135–136
(synopsis TEM-06-02). The coefficient of the previous polynomial is a positive ratio
of consecutive leading-coefficient ratios. -/
theorem orthonormal_polynomials_recurrence
    {μ : Measure ℝ} {p : ℕ → Polynomial ℝ} (hp : IsOrthogonalPolynomials μ p)
    (hnorm : ∀ n : ℕ, ∫ x : ℝ, (p n).eval x ^ 2 ∂μ = 1)
    (hlead : ∀ n : ℕ, 0 < (p n).leadingCoeff) :
    p 1 = Polynomial.C ((p 1).leadingCoeff / (p 0).leadingCoeff) *
      (Polynomial.X - Polynomial.C (∫ x : ℝ, x * (p 0).eval x ^ 2 ∂μ)) * p 0 ∧
    ∀ n : ℕ,
      p (n + 2) = Polynomial.C ((p (n + 2)).leadingCoeff / (p (n + 1)).leadingCoeff) *
        (Polynomial.X - Polynomial.C (∫ x : ℝ, x * (p (n + 1)).eval x ^ 2 ∂μ)) *
          p (n + 1) -
        Polynomial.C ((p n).leadingCoeff * (p (n + 2)).leadingCoeff /
          (p (n + 1)).leadingCoeff ^ 2) * p n := by
  sorry

/-- Every higher-degree orthogonal polynomial has a zero between consecutive zeros of a
lower-degree one. Andrews–Askey–Roy, *Special Functions*, Theorem 5.4.3, p. 253
(synopsis AAR-5.3.2–5.4.4). The degrees need not be adjacent. -/
theorem exists_zero_between_consecutive_orthogonal_polynomial_zeros
    {μ : Measure ℝ} {p : ℕ → Polynomial ℝ} (hp : IsOrthogonalPolynomials μ p)
    {m n : ℕ} (hmn : m < n) {a b : ℝ} (hab : a < b)
    (ha : (p m).eval a = 0) (hb : (p m).eval b = 0)
    (hconsecutive : ∀ x ∈ Set.Ioo a b, (p m).eval x ≠ 0) :
    ∃ x ∈ Set.Ioo a b, (p n).eval x = 0 := by
  sorry

end DLMF.OrthogonalPolynomials
