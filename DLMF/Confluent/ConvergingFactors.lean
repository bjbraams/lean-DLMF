/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic
public import DLMFMathlib.Algebra.Polynomial.DerivativeResolvent
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Growing-index converging factors for Tricomi U

Olver, *Asymptotics and Special Functions*, Chapter 14, §5,
pp. 531–536, synopsis O-14.04. The exact remainder quotient, beta-Taylor
integral, differential equation, polynomial coefficient algorithm and actual uniform
expansion are separate statements. Nonnegative integral b has an exact finite sum
and is excluded from a quotient whose omitted term vanishes.
-/

@[expose] public noncomputable section
open Complex Polynomial MeasureTheory Set DLMF.Hypergeometric
namespace DLMF.Confluent.TricomiConvergingFactor

/-- The omitted term in U(a,a+b+1,z). Olver, Chapter 14, §5. -/
def omittedTerm (a b z : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * pochhammer a n * pochhammer (-b) n / (n.factorial * z ^ (a + n))

/-- The exact remainder divided by its first omitted term. Olver §5.
Application theorems impose a>0 and exclude nonnegative integral b. -/
def value (a b : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (kummerU a (a + b + 1) z - ∑ s ∈ Finset.range n, omittedTerm a b z s) /
    omittedTerm a b z n

/-- The coefficient of n^(-1) in the shifted differential equation.
Olver, Chapter 14, §5, pp. 531–536. -/
def firstPerturbation (a b q : ℂ) (p : ℂ[X]) : ℂ[X] :=
  C 2 * X * p.derivative.derivative +
    (C (b - a + 1) - C (2 + 2 * q) * X) * p.derivative + (C (a - b) + C q * X) * p

/-- The coefficient of n^(-2) in the shifted differential equation. Olver §5. -/
def secondPerturbation (a b q : ℂ) (p : ℂ[X]) : ℂ[X] :=
  X ^ 2 * p.derivative.derivative +
    (C (b - a + 1) * X - C q * X ^ 2) * p.derivative - C (a * b) * p

/-- The effective polynomial coefficient algorithm obtained from the exact ODE.
Olver, Chapter 14, §5. Its leading operator is (1-D)(1+q-D). -/
def coefficient (a b q : ℂ) (n : ℕ) : ℂ[X] :=
  if n = 0 then C (q / (1 + q)) else
    derivativeResolvent 1 (derivativeResolvent (1 + q)
      ((if n = 1 then C q * X else -secondPerturbation a b q (coefficient a b q (n - 2))) -
        firstPerturbation a b q (coefficient a b q (n - 1))))
termination_by n

/-- The defining omitted term. -/
theorem omittedTerm_def (a b z : ℂ) (n : ℕ) : omittedTerm a b z n =
    (-1 : ℂ) ^ n * pochhammer a n * pochhammer (-b) n / (n.factorial * z ^ (a + n)) := rfl

/-- The defining exact remainder quotient. -/
theorem value_def (a b : ℂ) (n : ℕ) (z : ℂ) : value a b n z =
    (kummerU a (a + b + 1) z - ∑ s ∈ Finset.range n, omittedTerm a b z s) /
      omittedTerm a b z n := rfl

/-- The first perturbing polynomial operator. -/
theorem firstPerturbation_def (a b q : ℂ) (p : ℂ[X]) : firstPerturbation a b q p =
    C 2 * X * p.derivative.derivative +
      (C (b - a + 1) - C (2 + 2 * q) * X) * p.derivative +
        (C (a - b) + C q * X) * p := rfl

/-- The second perturbing polynomial operator. -/
theorem secondPerturbation_def (a b q : ℂ) (p : ℂ[X]) : secondPerturbation a b q p =
    X ^ 2 * p.derivative.derivative +
      (C (b - a + 1) * X - C q * X ^ 2) * p.derivative - C (a * b) * p := rfl

/-- The zero-th coefficient is the constant q/(1+q). -/
theorem coefficient_zero (a b q : ℂ) : coefficient a b q 0 = C (q / (1 + q)) := by
  rw [coefficient, ite_eq_left rfl]

/-- Every later polynomial is computed by finite differential resolvents. -/
theorem coefficient_succ (a b q : ℂ) (n : ℕ) : coefficient a b q (n + 1) =
    derivativeResolvent 1 (derivativeResolvent (1 + q)
      ((if n + 1 = 1 then C q * X else
        -secondPerturbation a b q (coefficient a b q (n + 1 - 2))) -
          firstPerturbation a b q (coefficient a b q n))) := by
  rw [coefficient, ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel]

/-- The exact beta-Taylor remainder integral, initially in the right half-plane.
Olver, Chapter 14, §5, pp. 531–536. -/
theorem value_eq_beta_remainder_integral {a : ℝ} (ha : 0 < a) {b : ℂ}
    (hb : ∀ k : ℕ, b ≠ (k : ℂ)) {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : 0 < z.re) :
    value a b n z = (n : ℂ) * z ^ ((a : ℂ) + n) / Gamma ((a : ℂ) + n) *
      ∫ t in Ioi (0 : ℝ), exp (-z * t) * (t : ℂ) ^ ((a : ℂ) + n - 1) *
        ∫ v in (0 : ℝ)..1,
          (1 - (v : ℂ)) ^ (n - 1) * (1 + (t : ℂ) * v) ^ (b - n) := by
  sorry

/-- The exact converging-factor second-order equation. Olver, Chapter 14, §5. -/
theorem value_differential_equation {a : ℝ} (ha : 0 < a) {b : ℂ}
    (hb : ∀ k : ℕ, b ≠ (k : ℂ)) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * iteratedDeriv 2 (value a b n) z +
      z * (b - a - 2 * n + 1 - z) * deriv (value a b n) z +
        (((n : ℂ) + a) * (n - b) + n * z) * value a b n z = n * z := by
  sorry

/-- The first two source polynomials, valid for arbitrary a,b and q≠-1.
Olver, Chapter 14, §5, pp. 531–536. -/
theorem first_coefficients (a b : ℂ) {q : ℂ} (hq : 1 + q ≠ 0) :
    coefficient a b q 0 = C (1 - (1 + q)⁻¹) ∧
      coefficient a b q 1 = C ((1 + q)⁻¹ * (1 - (1 + q)⁻¹)) *
        (X + C (b - a + 1 + (1 + q)⁻¹)) := by
  sorry

/-- The full uniform growing-index expansion. Olver, Chapter 14, §5,
pp. 531–536. Complex b is allowed away from termination. -/
theorem exists_uniform_growing_index_remainder_le {a : ℝ} (ha : 0 < a) {b : ℂ}
    (hb : ∀ k : ℕ, b ≠ (k : ℂ)) {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hδπ : δ < Real.pi) (N : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ A → ∀ θ ∈ Icc (-Real.pi + δ) (Real.pi - δ),
        ‖value a b n (((n : ℂ) + ζ) * exp (I * θ)) -
          ∑ s ∈ Finset.range N, (coefficient a b (exp (I * θ)) s).eval ζ / (n : ℂ) ^ s‖ ≤
            M / (n : ℝ) ^ N := by
  sorry

end DLMF.Confluent.TricomiConvergingFactor
