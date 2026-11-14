/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.General
public import DLMF.OrthogonalPolynomials.Basic.NormsAndKernels
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Quadrature weights, Christoffel functions and Markov's theorem

Statements from Andrews, Askey and Roy, *Special Functions*, §§5.3–5.6,
supplementing the polynomial exactness theorem and reproducing-kernel API.
The measure is positive; `IsOrthogonalPolynomials` includes finite positive squared norms.
The second-kind polynomial uses polynomial division, so atoms cause no diagonal ambiguity.
-/

@[expose] public section

open Polynomial MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The Gaussian weight attached to node `i` is the integral of its Lagrange cardinal
polynomial. Andrews–Askey–Roy, *Special Functions*, §5.3, Theorem 5.3.2
(synopsis AAR-5.3.2–5.4.4). -/
def gaussWeight {n : ℕ} (μ : Measure ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ

/-- The defining integral for a Gaussian weight. -/
theorem gaussWeight_def {n : ℕ} (μ : Measure ℝ) (x : Fin n → ℝ) (i : Fin n) :
    gaussWeight μ x i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ := rfl

/-- A Gaussian weight is the positive squared norm of its cardinal polynomial.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.3.2, p. 249
(synopsis AAR-5.3.2–5.4.4). -/
theorem gaussWeight_eq_integral_sq {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hroot : ∀ i, (p n).eval (x i) = 0) (i : Fin n) :
    gaussWeight μ x i = ∫ t, ((Lagrange.basis Finset.univ x i).eval t) ^ 2 ∂μ ∧
      0 < gaussWeight μ x i := by
  sorry

/-- Gaussian quadrature converges on every continuous function on a compact support.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.3.3, p. 251
(synopsis AAR-5.3.2–5.4.4). Node sets have `n + 1` elements to avoid a zero-node convention. -/
theorem tendsto_gauss_quadrature {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {a b : ℝ} (hab : a < b)
    (hsupport : μ (Icc a b)ᶜ = 0) (x : (n : ℕ) → Fin (n + 1) → ℝ)
    (hx : ∀ n, Function.Injective (x n))
    (hroot : ∀ n i, (p (n + 1)).eval (x n i) = 0)
    (hmem : ∀ n i, x n i ∈ Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => ∑ i, gaussWeight μ (x n) i * f (x n i)) atTop
      (𝓝 (∫ t, f t ∂μ)) := by
  sorry

/-- Markov–Stieltjes bounds use different half-open cumulative intervals at a possible atom.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.4.4, p. 255
(synopsis AAR-5.3.2–5.4.4). -/
theorem markov_stieltjes_inequalities {μ : Measure ℝ} [IsFiniteMeasure μ]
    {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (hsupport : μ (Icc a b)ᶜ = 0) (x : Fin n → ℝ)
    (hx : StrictMono x) (hroot : ∀ i, (p n).eval (x i) = 0)
    (hmem : ∀ i, x i ∈ Ioo a b) (j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i => i < j), gaussWeight μ x i) ≤
        (μ (Ico a (x j))).toReal ∧
      (μ (Ico a (x j))).toReal ≤ (μ (Icc a (x j))).toReal ∧
      (μ (Icc a (x j))).toReal ≤
        ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), gaussWeight μ x i := by
  sorry

/-- The reciprocal Gaussian weight is the diagonal kernel of degree `n - 1`.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.6.4, p. 261
(synopsis AAR-5.6.2–5.6.5). -/
theorem gaussWeight_inv_eq_kernel {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hroot : ∀ i, (p n).eval (x i) = 0) (i : Fin n) :
    (gaussWeight μ x i)⁻¹ = christoffelDarbouxKernel μ p (n - 1) (x i) (x i) := by
  sorry

/-- The Christoffel–Darboux diagonal is the sharp squared evaluation bound on unit-norm
polynomials. Andrews–Askey–Roy, *Special Functions*, Theorem 5.6.5, p. 262
(synopsis AAR-5.6.2–5.6.5). Equality is attained by the two normalized kernel polynomials. -/
theorem kernel_evaluation_extremum {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (n : ℕ) (x : ℝ) :
    (∀ q : ℝ[X], q.degree ≤ n → (∫ t, q.eval t ^ 2 ∂μ) = 1 →
      q.eval x ^ 2 ≤ christoffelDarbouxKernel μ p n x x) ∧
    ∃ q : ℝ[X], q.degree ≤ n ∧ (∫ t, q.eval t ^ 2 ∂μ) = 1 ∧
      q.eval x ^ 2 = christoffelDarbouxKernel μ p n x x ∧
      ∀ r : ℝ[X], r.degree ≤ n → (∫ t, r.eval t ^ 2 ∂μ) = 1 →
        r.eval x ^ 2 = christoffelDarbouxKernel μ p n x x → r = q ∨ r = -q := by
  sorry

/-- The second-kind polynomial `Q` is the coefficientwise integral of the polynomial
divided difference of `P`. Andrews–Askey–Roy, *Special Functions*, §5.5, Theorem 5.5.4
(synopsis AAR-5.5.2–5.5.6). This normalization gives `Q₀ = 0` and, for monic `P₁`,
`Q₁ = μ(ℝ)`. -/
def secondKindPolynomial (μ : Measure ℝ) (P : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range P.natDegree,
    C (∫ t, (P /ₘ (X - C t)).coeff k ∂μ) * X ^ k

/-- The coefficientwise definition of the second-kind polynomial. -/
theorem secondKindPolynomial_def (μ : Measure ℝ) (P : ℝ[X]) :
    secondKindPolynomial μ P = ∑ k ∈ Finset.range P.natDegree,
      C (∫ t, (P /ₘ (X - C t)).coeff k ∂μ) * X ^ k := rfl

/-- A constant polynomial has zero second-kind polynomial. Andrews–Askey–Roy,
*Special Functions*, §5.5, p. 257 (synopsis AAR-5.5.2–5.5.6). -/
@[simp] theorem secondKindPolynomial_C (μ : Measure ℝ) (c : ℝ) :
    secondKindPolynomial μ (C c) = 0 := by
  simp [secondKindPolynomial]

/-- A monic linear polynomial has constant second-kind polynomial equal to the measure's
mass. Andrews–Askey–Roy, *Special Functions*, §5.5, p. 257
(synopsis AAR-5.5.2–5.5.6). The totalized identity also holds for infinite measures. -/
theorem secondKindPolynomial_X_sub_C (μ : Measure ℝ) (a : ℝ) :
    secondKindPolynomial μ (X - C a) = C (μ.real Set.univ) := by
  simp [secondKindPolynomial, Polynomial.coeff_divByMonic_X_sub_C]

/-- Evaluating the second-kind polynomial integrates the continuously extended divided
difference. Andrews–Askey–Roy, *Special Functions*, Theorem 5.5.4, p. 257
(synopsis AAR-5.5.2–5.5.6). -/
theorem eval_secondKindPolynomial {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (n : ℕ) (z : ℝ) :
    (secondKindPolynomial μ (p n)).eval z =
      ∫ t, ((p n) /ₘ (X - C t)).eval z ∂μ := by
  sorry

/-- The second-kind polynomials satisfy the same monic recurrence from index one onward.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.5.4, p. 257
(synopsis AAR-5.5.2–5.5.6). -/
theorem secondKindPolynomial_recurrence {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (hmonic : ∀ n, (p n).Monic)
    {α β : ℕ → ℝ}
    (hrec : ∀ n, p (n + 2) = (X - C (α (n + 1))) * p (n + 1) -
      C (β (n + 1)) * p n) (n : ℕ) :
    secondKindPolynomial μ (p (n + 2)) =
      (X - C (α (n + 1))) * secondKindPolynomial μ (p (n + 1)) -
        C (β (n + 1)) * secondKindPolynomial μ (p n) := by
  sorry

/-- Partial fractions for the ratio of second-kind and first-kind polynomials.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.5.5, p. 258
(synopsis AAR-5.5.2–5.5.6). -/
theorem secondKindPolynomial_div_eq_sum {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hroot : ∀ i, (p n).eval (x i) = 0)
    {z : ℂ} (hz : ∀ i, z ≠ (x i : ℂ)) :
    (secondKindPolynomial μ (p n)).eval₂ (algebraMap ℝ ℂ) z /
        (p n).eval₂ (algebraMap ℝ ℂ) z =
      ∑ i, (gaussWeight μ x i : ℂ) / (z - (x i : ℂ)) := by
  sorry

/-- Markov's theorem: the rational second-kind approximants converge locally uniformly
to the Cauchy transform off the compact support interval.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.5.6, p. 258
(synopsis AAR-5.5.2–5.5.6). -/
theorem tendstoLocallyUniformlyOn_secondKindPolynomial_div
    {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    {a b : ℝ} (hab : a < b) (hsupport : μ (Icc a b)ᶜ = 0) :
    TendstoLocallyUniformlyOn
      (fun n z => (secondKindPolynomial μ (p n)).eval₂ (algebraMap ℝ ℂ) z /
        (p n).eval₂ (algebraMap ℝ ℂ) z)
      (fun z => ∫ t : ℝ, (z - (t : ℂ))⁻¹ ∂μ) atTop
      {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re} := by
  sorry

end DLMF.OrthogonalPolynomials
