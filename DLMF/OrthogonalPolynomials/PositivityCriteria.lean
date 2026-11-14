/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Positivity criteria for Laguerre, Jacobi and Gegenbauer polynomials

Andrews, Askey and Roy, *Special Functions*, §§7.2, 7.4–7.6. The real-variable
statements take real parts of the existing complex-normalized polynomial functions.
The integral and kernel statements retain their convergence conditions.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Real Topology

noncomputable section

namespace DLMF.OrthogonalPolynomials.Real

/-- The triple Laguerre integral with an exponential decay parameter.
Andrews–Askey–Roy, *Special Functions*, §7.2, pp. 363–371
(synopsis AAR-7.2.1–7.2.7). -/
def laguerreTripleIntegral (α decay : ℝ) (k m n : ℕ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0,
    x ^ α * Real.exp (-decay * x) *
      (laguerrePolynomialL α k x).re * (laguerrePolynomialL α m x).re *
      (laguerrePolynomialL α n x).re

/-- The defining integral of the triple Laguerre product. -/
theorem laguerreTripleIntegral_def (α decay : ℝ) (k m n : ℕ) :
    laguerreTripleIntegral α decay k m n =
      ∫ x : ℝ in Set.Ioi 0, x ^ α * Real.exp (-decay * x) *
        (laguerrePolynomialL α k x).re * (laguerrePolynomialL α m x).re *
        (laguerrePolynomialL α n x).re := rfl

/-- The polynomial-binomial coefficient inequality underlying Laguerre positivity.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.2.1, p. 363
(synopsis AAR-7.2.1–7.2.7). -/
theorem sum_binomial_triple_nonneg {α β γ : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hαγ : α ≤ γ) (m n : ℕ) :
    0 ≤ ∑ k ∈ range (min m n + 1),
      Ring.choose ((m - k : ℕ) + β) (m - k) *
        Ring.choose ((n - k : ℕ) + γ) (n - k) * Ring.choose ((k : ℝ) - α - 2) k := by
  sorry

/-- Nonnegativity of the Laguerre triple product with decay three.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.2.2, p. 364
(synopsis AAR-7.2.1–7.2.7). -/
theorem laguerreTripleIntegral_three_nonneg {α : ℝ} (hα : -1 / 2 ≤ α)
    (k m n : ℕ) : 0 ≤ laguerreTripleIntegral α 3 k m n := by
  sorry

/-- Strict positivity of the Laguerre triple product with decay three for nonnegative
parameter. Andrews–Askey–Roy, *Special Functions*, Theorem 7.2.2, p. 364
(synopsis AAR-7.2.1–7.2.7). -/
theorem laguerreTripleIntegral_three_pos {α : ℝ} (hα : 0 ≤ α)
    (k m n : ℕ) : 0 < laguerreTripleIntegral α 3 k m n := by
  sorry

/-- Every Laguerre coefficient of an exponentially damped Laguerre polynomial is positive.
Andrews–Askey–Roy, *Special Functions*, Lemma 7.2.3, p. 365
(synopsis AAR-7.2.1–7.2.7). -/
theorem integral_damped_laguerre_mul_pos {α ε : ℝ} (hα : -1 < α) (hε : 0 < ε)
    (m n : ℕ) :
    0 < ∫ x : ℝ in Set.Ioi 0, x ^ α * Real.exp (-(1 + ε) * x) *
      (laguerrePolynomialL α m x).re * (laguerrePolynomialL α n x).re := by
  sorry

/-- Sarmanov's characterization: coefficients of a nonnegative Laguerre product kernel
are moments of a finite measure on `[0,1]`. Andrews–Askey–Roy, *Special Functions*,
Theorem 7.2.5, pp. 366–367 (synopsis AAR-7.2.1–7.2.7). Absolute local uniform
convergence specifies an ordinary function kernel, rather than a distribution. -/
theorem exists_measure_moments_of_laguerre_kernel_nonneg {α : ℝ} (hα : -1 < α)
    (a : ℕ → ℝ)
    (hsum : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → Summable (fun n =>
      a n * (laguerrePolynomialL α n x).re * (laguerrePolynomialL α n y).re /
        (laguerrePolynomialL α n 0).re))
    (huniform : TendstoLocallyUniformlyOn
      (fun N (xy : ℝ × ℝ) => ∑ n ∈ range N,
        |a n * (laguerrePolynomialL α n xy.1).re * (laguerrePolynomialL α n xy.2).re /
          (laguerrePolynomialL α n 0).re|)
      (fun xy => ∑' n, |a n * (laguerrePolynomialL α n xy.1).re *
        (laguerrePolynomialL α n xy.2).re / (laguerrePolynomialL α n 0).re|)
      atTop {xy : ℝ × ℝ | 0 ≤ xy.1 ∧ 0 ≤ xy.2})
    (hpositive : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      0 ≤ ∑' n, a n * (laguerrePolynomialL α n x).re *
        (laguerrePolynomialL α n y).re / (laguerrePolynomialL α n 0).re) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ n : ℕ, a n = ∫ r : ℝ, r ^ n ∂ρ := by
  sorry

/-- The sharp lower-parameter threshold for triple Laguerre positivity with decay two.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.2.6, p. 368
(synopsis AAR-7.2.1–7.2.7). -/
theorem laguerreTripleIntegral_two_nonneg {α : ℝ}
    (hα : (-5 + Real.sqrt 17) / 2 ≤ α) (k m n : ℕ) :
    0 ≤ laguerreTripleIntegral α 2 k m n ∧
      (laguerreTripleIntegral α 2 k m n = 0 ↔
        α = (-5 + Real.sqrt 17) / 2 ∧ k = 1 ∧ m = 1 ∧ n = 1) := by
  sorry

/-- Koornwinder's scaled Laguerre positivity integral.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.2.7, p. 370
(synopsis AAR-7.2.1–7.2.7). -/
theorem integral_laguerre_scaled_triple_nonneg {α a b : ℝ}
    (hα : 0 ≤ α) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (k m n : ℕ) :
    0 ≤ ∫ x : ℝ in Set.Ioi 0, x ^ α * Real.exp (-x) *
      (laguerrePolynomialL α k (a * x)).re * (laguerrePolynomialL α m (b * x)).re *
      (laguerrePolynomialL α n x).re := by
  sorry

/-- Positive normalized Gegenbauer partial sums.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.4.1, p. 381
(synopsis AAR-7.4.1–7.6.4). -/
theorem sum_normalized_gegenbauer_pos {ν θ : ℝ} (hν : 1 / 2 ≤ ν)
    (hθ : 0 ≤ θ) (hθπ : θ < Real.pi) (n : ℕ) :
    0 < ∑ k ∈ range (n + 1),
      (ultrasphericalPolynomial ν k (Real.cos θ)).re /
        (ultrasphericalPolynomial ν k 1).re := by
  sorry

/-- Askey–Gasper positivity in the Jacobi form used by the de Branges application.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.4.2, p. 382
(synopsis AAR-7.4.1–7.6.4). -/
theorem sum_jacobi_zero_second_parameter_pos {α x : ℝ} (hα : -1 < α)
    (hx : -1 < x) (hx1 : x ≤ 1) (n : ℕ) :
    0 < ∑ k ∈ range (n + 1), (jacobiPolynomialP α 0 k x).re := by
  sorry

/-- Increasing equal Jacobi parameters converts a nonzero nonnegative polynomial sum
to a strictly positive sum in the open interval.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.5.2, p. 385
(synopsis AAR-7.4.1–7.6.4). -/
theorem sum_normalized_jacobi_pos_of_parameter_lt {α β : ℝ}
    (hα : -1 < α) (hαβ : α < β) (n : ℕ) (a : ℕ → ℝ)
    (hne : ∃ k ≤ n, a k ≠ 0)
    (hpositive : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 →
      0 ≤ ∑ k ∈ range (n + 1), a k * (jacobiPolynomialP α α k x).re /
        (jacobiPolynomialP α α k 1).re)
    {y : ℝ} (hy : y ∈ Set.Ioo (-1) 1) :
    0 < ∑ k ∈ range (n + 1), a k * (jacobiPolynomialP β β k y).re /
      (jacobiPolynomialP β β k 1).re := by
  sorry

/-- Positivity of the Cesàro mean of order `2ν+1` of the Gegenbauer reproducing kernel.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.6.1, p. 387
(synopsis AAR-7.4.1–7.6.4). -/
theorem gegenbauer_cesaro_kernel_nonneg {ν x : ℝ} (hν : 0 < ν)
    (hx : x ∈ Set.Icc (-1) 1) (n : ℕ) :
    0 ≤ ∑ k ∈ range (n + 1),
      ((ascPochhammer ℝ (n - k)).eval (2 * ν + 2) / (n - k).factorial) *
        ((k + ν) / ν) * (ultrasphericalPolynomial ν k x).re := by
  sorry

/-- Exponential damping turns nonnegative Laguerre coefficients of a nonzero weighted
`L²` function into strictly positive coefficients. Andrews–Askey–Roy,
*Special Functions*, Corollary 7.2.4, p. 366 (synopsis AAR-7.2.1–7.2.7).
The weighted `L²` setting gives the convergent orthogonal expansion. -/
theorem integral_damped_laguerre_mul_function_pos {α ε : ℝ}
    (hα : -1 < α) (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : MemLp f 2 ((volume.restrict (Set.Ioi 0)).withDensity
      (fun x : ℝ => ENNReal.ofReal (x ^ α * Real.exp (-x)))))
    (hne : ¬ f =ᵐ[((volume.restrict (Set.Ioi 0)).withDensity
      (fun x : ℝ => ENNReal.ofReal (x ^ α * Real.exp (-x))))] 0)
    (hcoeff : ∀ n : ℕ,
      0 ≤ ∫ x : ℝ in Set.Ioi 0,
        f x * (laguerrePolynomialL α n x).re * x ^ α * Real.exp (-x)) (n : ℕ) :
    0 < ∫ x : ℝ in Set.Ioi 0,
      Real.exp (-ε * x) * f x * (laguerrePolynomialL α n x).re * x ^ α * Real.exp (-x) := by
  sorry

end DLMF.OrthogonalPolynomials.Real
