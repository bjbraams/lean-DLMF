/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Basic
public import DLMFMathlib.Algebra.Polynomial.DerivativeResolvent
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Growing-index converging factors for E1

Olver, *Asymptotics and Special Functions*, Chapter 14, §3,
pp. 523–526, synopsis O-14.02. The value is the exact remainder divided
by its nonzero first omitted term; the index-growing uniform expansion is a
separate theorem from the exact differential equation.
-/

@[expose] public noncomputable section
open Complex Polynomial MeasureTheory Set
namespace DLMF.Confluent.ExponentialConvergingFactor

/-- The first omitted E1 term after n terms. Olver, Chapter 14, §3. -/
def omittedTerm (n : ℕ) (z : ℂ) : ℂ := (-1 : ℂ) ^ n * n.factorial / z ^ (n + 1)

/-- The exact E1 converging factor, intended for z in the principal slit plane.
Olver, Chapter 14, §3, pp. 523–526. -/
def value (n : ℕ) (z : ℂ) : ℂ :=
  (exp z * expIntegralE 1 z - ∑ s ∈ Finset.range n, omittedTerm s z) / omittedTerm n z

/-- The effective polynomial recursion for every growing-index coefficient.
Olver, Chapter 14, §3, pp. 523–526. The parameter q is exp(i*theta). -/
def coefficient (q : ℂ) : ℕ → ℂ[X]
  | 0 => C (q / (1 + q))
  | n + 1 => derivativeResolvent (1 + q)
      ((if n = 0 then C q * X else 0) -
        (1 + C q * X) * coefficient q n + X * (coefficient q n).derivative)

/-- The defining omitted term. -/
theorem omittedTerm_def (n : ℕ) (z : ℂ) :
    omittedTerm n z = (-1 : ℂ) ^ n * n.factorial / z ^ (n + 1) := rfl

/-- The exact quotient defining the E1 converging factor. -/
theorem value_def (n : ℕ) (z : ℂ) : value n z =
    (exp z * expIntegralE 1 z - ∑ s ∈ Finset.range n, omittedTerm s z) / omittedTerm n z :=
  rfl

/-- The constant polynomial coefficient. -/
theorem coefficient_zero (q : ℂ) : coefficient q 0 = C (q / (1 + q)) := rfl

/-- The finite differential-resolvent recursion. -/
theorem coefficient_succ (q : ℂ) (n : ℕ) : coefficient q (n + 1) =
    derivativeResolvent (1 + q) ((if n = 0 then C q * X else 0) -
      (1 + C q * X) * coefficient q n + X * (coefficient q n).derivative) := rfl

/-- The exact normalized E1 remainder integral. Olver, Chapter 14, §3.
The rotated path is parametrized by its principal argument, so it remains on
one coherent branch over the full slit plane. -/
theorem value_eq_rotated_integral (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    value n z = z ^ (n + 1) * exp (-I * arg z) ^ (n + 1) / n.factorial *
      ∫ t in Ioi (0 : ℝ), exp (-(‖z‖ * t : ℝ)) * (t : ℂ) ^ n /
        (1 + exp (-I * arg z) * t) := by
  sorry

/-- The exact first-order equation for every fixed truncation index.
Olver, Chapter 14, §3, pp. 523–526. -/
theorem value_differential_equation (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    (1 + (n + 1 : ℂ) / z) * value n z - deriv (value n) z = 1 := by
  sorry

/-- The first two coefficient polynomials, with a=1/(1+q).
Olver, Chapter 14, §3, pp. 523–526. -/
theorem first_coefficients {q : ℂ} (hq : 1 + q ≠ 0) :
    coefficient q 0 = C (1 - (1 + q)⁻¹) ∧
      coefficient q 1 = C ((1 + q)⁻¹ * (1 - (1 + q)⁻¹)) *
        (X + C (-1 + (1 + q)⁻¹)) := by
  sorry

/-- The stated polynomial differential equations uniquely fix the full sequence.
Olver, Chapter 14, §3, pp. 523–526. -/
theorem coefficient_unique {q : ℂ} (hq : 1 + q ≠ 0) {y : ℕ → ℂ[X]}
    (hzero : C (1 + q) * y 0 - (y 0).derivative = C q)
    (hnext : ∀ n : ℕ, C (1 + q) * y (n + 1) - (y (n + 1)).derivative =
      (if n = 0 then C q * X else 0) - (1 + C q * X) * y n + X * (y n).derivative) :
    y = coefficient q := by
  sorry

/-- The complete growing-index expansion is uniform for bounded complex zeta
and every proper closed argument sector. Olver, Chapter 14, §3, pp. 523–526. -/
theorem exists_uniform_growing_index_remainder_le {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hδπ : δ < Real.pi) (N : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ A → ∀ θ ∈ Icc (-Real.pi + δ) (Real.pi - δ),
        ‖value n (((n : ℂ) + ζ) * exp (I * θ)) -
          ∑ s ∈ Finset.range N, (coefficient (exp (I * θ)) s).eval ζ / (n : ℂ) ^ s‖ ≤
            M / (n : ℝ) ^ N := by
  sorry

end DLMF.Confluent.ExponentialConvergingFactor
