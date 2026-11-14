/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.QuadratureAndKernels
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Gaussian quadrature derivative weights and exact remainder

Temme, *Special Functions*, Theorem 6.5, pp. 138–141. Squared norms are
retained, so the statements do not require orthonormal normalization.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace DLMF.OrthogonalPolynomials

/-- Gaussian weights expressed through consecutive orthogonal polynomials and a derivative.
Temme, *Special Functions*, Theorem 6.5 (synopsis TEM-06-05); Andrews–Askey–Roy,
§5.3 (synopsis AAR-5.3.2–5.4.4). -/
theorem gaussWeight_eq_derivative_quotient {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (hp : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : Function.Injective x) (hroot : ∀ i, (p n).eval (x i) = 0)
    (i : Fin n) :
    gaussWeight μ x i =
      -squaredNorm μ p n * (p (n + 1)).leadingCoeff /
        ((p n).leadingCoeff * (p n).derivative.eval (x i) * (p (n + 1)).eval (x i)) := by
  sorry

/-- The Gaussian quadrature error is a derivative value times the monic squared norm.
Temme, *Special Functions*, Theorem 6.5, pp. 140–141 (synopsis TEM-06-05).
For an orthonormal family this is `f^(2n)(ξ)/((2n)! κ_n²)`. -/
theorem exists_gauss_quadrature_error_eq_iteratedDeriv
    {μ : Measure ℝ} {p : ℕ → ℝ[X]} (hp : IsOrthogonalPolynomials μ p)
    {a b : ℝ} (hab : a < b) (hsupport : μ (Set.Icc a b)ᶜ = 0)
    (hpositive : ∀ c d : ℝ, a ≤ c → c < d → d ≤ b → 0 < μ (Set.Ioo c d))
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (p n).eval (x i) = 0) (hinside : ∀ i, x i ∈ Set.Ioo a b)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (2 * n) f (Set.Icc a b)) :
    ∃ ξ ∈ Set.Ioo a b,
      (∫ t : ℝ, f t ∂μ) - ∑ i : Fin n, gaussWeight μ x i * f (x i) =
        iteratedDeriv (2 * n) f ξ * squaredNorm μ p n /
          (((2 * n).factorial : ℝ) * (p n).leadingCoeff ^ 2) := by
  sorry

/-- The canonical Lagrange-integral Gaussian weights integrate every polynomial of degree
less than twice the number of nodes exactly. Temme, *Special Functions*, §6.1.2,
Theorem 6.5 (synopsis TEM-06-05); Andrews–Askey–Roy, §5.3. -/
theorem integral_eq_sum_gaussWeight {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (hp : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : Function.Injective x) (hroot : ∀ i, (p n).eval (x i) = 0)
    (q : ℝ[X]) (hq : q.degree < (2 * n : ℕ)) :
    (∫ t : ℝ, q.eval t ∂μ) = ∑ i : Fin n, gaussWeight μ x i * q.eval (x i) := by
  sorry

/-- Markov–Stieltjes inequalities are strict on both outside bounds for an atom-free
measure positive on all open subintervals. Andrews–Askey–Roy, *Special Functions*,
Theorem 5.4.4, pp. 253–256 (synopsis AAR-5.3.2–5.4.4). -/
theorem strict_markov_stieltjes_inequalities {μ : Measure ℝ} [NullSingletonClass μ]
    {p : ℕ → ℝ[X]} (hp : IsOrthogonalPolynomials μ p) {a b : ℝ} (hab : a < b)
    (hsupport : μ (Set.Icc a b)ᶜ = 0)
    (hpositive : ∀ c d : ℝ, a ≤ c → c < d → d ≤ b → 0 < μ (Set.Ioo c d))
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : StrictMono x)
    (hroot : ∀ i, (p n).eval (x i) = 0) (hinside : ∀ i, x i ∈ Set.Ioo a b) (j : Fin n) :
    (∑ i : Fin n with i < j, gaussWeight μ x i) < μ.real (Set.Icc a (x j)) ∧
      μ.real (Set.Icc a (x j)) < ∑ i : Fin n with i ≤ j, gaussWeight μ x i := by
  sorry

end DLMF.OrthogonalPolynomials
