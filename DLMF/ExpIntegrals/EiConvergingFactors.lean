/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Basic
public import DLMF.ExpIntegrals.Continuation
public import DLMF.Gamma.SaddleCoordinates
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Ei converging factors and the pole-subtracted saddle algorithm

Olver, *Asymptotics and Special Functions*, Chapter 14, §4,
pp. 527–530, synopsis O-14.03. The actual inverse Gamma saddle coordinate
is reused. Its simple pole is subtracted before forming the even Gaussian moments,
and the complete normalization is expanded by a formal exponential.
-/

@[expose] public noncomputable section
open Complex Polynomial MeasureTheory Set
open scoped Topology
open DLMF.Core
namespace DLMF.Confluent.EiConvergingFactor

/-- The omitted positive Ei term. Olver, Chapter 14, §4, pp. 527–530. -/
def omittedTerm (n : ℕ) (x : ℝ) : ℝ := n.factorial / x ^ (n + 1)

/-- The exact Ei remainder divided by its first omitted term, for x>0.
Olver, Chapter 14, §4, pp. 527–530. -/
def value (n : ℕ) (x : ℝ) : ℝ :=
  (Real.exp (-x) * Real.expIntegralEi x - ∑ s ∈ Finset.range n, omittedTerm s x) /
    omittedTerm n x

/-- The regularized amplitude of the signed Gaussian saddle coordinate.
Olver, Chapter 14, §4. The value at zero removes the -1/s pole. -/
def regularizedAmplitude (ζ s : ℝ) : ℝ :=
  if s = 0 then ζ - 1 / 3 else
    Real.exp (-ζ * (DLMF.Gamma.Real.gammaSaddleInverse s - 1)) *
      deriv DLMF.Gamma.Real.gammaSaddleInverse s /
        (1 - DLMF.Gamma.Real.gammaSaddleInverse s) + 1 / s

/-- Coefficients of the logarithm of the Gaussian/Stirling prefactor.
Olver, Chapter 14, §4. The zero constant is required for formal substitution. -/
def normalizationLogCoefficient (ζ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    (-1 : ℝ) ^ j * ζ ^ (j + 1) / (j + 1) +
      (-1 : ℝ) ^ (j + 1) * ζ ^ j / j - (bernoulli (j + 1) : ℝ) / (j * (j + 1))

/-- The reciprocal-Stirling normalization coefficients, by formal exponential.
Olver, Chapter 14, §4, pp. 527–530. -/
def normalizationCoefficient (ζ : ℝ) (j : ℕ) : ℝ :=
  PowerSeries.coeff j ((PowerSeries.exp ℝ).subst
    (PowerSeries.mk (normalizationLogCoefficient ζ)))

/-- The complete effective coefficient algorithm: pole-subtracted even saddle
moments convolved with the reciprocal-Stirling prefactor. Olver, Chapter 14, §4. -/
def coefficient (j : ℕ) (ζ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), normalizationCoefficient ζ (j - k) *
    iteratedDeriv (2 * k) (regularizedAmplitude ζ) 0 / ((2 : ℝ) ^ k * k.factorial)

/-- The defining positive omitted term. -/
theorem omittedTerm_def (n : ℕ) (x : ℝ) : omittedTerm n x = n.factorial / x ^ (n + 1) := rfl

/-- The exact defining Ei quotient. -/
theorem value_def (n : ℕ) (x : ℝ) : value n x =
    (Real.exp (-x) * Real.expIntegralEi x - ∑ s ∈ Finset.range n, omittedTerm s x) /
      omittedTerm n x := rfl

/-- The defining pole-subtracted amplitude. -/
theorem regularizedAmplitude_def (ζ s : ℝ) : regularizedAmplitude ζ s =
    if s = 0 then ζ - 1 / 3 else
      Real.exp (-ζ * (DLMF.Gamma.Real.gammaSaddleInverse s - 1)) *
        deriv DLMF.Gamma.Real.gammaSaddleInverse s /
          (1 - DLMF.Gamma.Real.gammaSaddleInverse s) + 1 / s := rfl

/-- The defining formal normalization logarithm. -/
theorem normalizationLogCoefficient_def (ζ : ℝ) (j : ℕ) :
    normalizationLogCoefficient ζ j = if j = 0 then 0 else
      (-1 : ℝ) ^ j * ζ ^ (j + 1) / (j + 1) +
        (-1 : ℝ) ^ (j + 1) * ζ ^ j / j - (bernoulli (j + 1) : ℝ) / (j * (j + 1)) := rfl

/-- The defining formal exponential coefficient. -/
theorem normalizationCoefficient_def (ζ : ℝ) (j : ℕ) : normalizationCoefficient ζ j =
    PowerSeries.coeff j ((PowerSeries.exp ℝ).subst
      (PowerSeries.mk (normalizationLogCoefficient ζ))) := rfl

/-- The defining finite Gaussian convolution. -/
theorem coefficient_def (j : ℕ) (ζ : ℝ) : coefficient j ζ =
    ∑ k ∈ Finset.range (j + 1), normalizationCoefficient ζ (j - k) *
      iteratedDeriv (2 * k) (regularizedAmplitude ζ) 0 / ((2 : ℝ) ^ k * k.factorial) := rfl

/-- The exact upper-bank E1/Ei multiplier. Olver, Chapter 14, §4, pp. 527–530. -/
theorem upper_bank_multiplier {x : ℝ} (hx : 0 < x) :
    -(Real.exp (-x) : ℂ) * expIntE1OnLog ((Real.log x : ℂ) + I * Real.pi) =
      (Real.exp (-x) * Real.expIntegralEi x : ℝ) + I * Real.pi * Real.exp (-x) := by
  sorry

/-- The exact principal-value remainder, with ordinary pole cancellation.
Olver, Chapter 14, §4, pp. 527–530. -/
theorem hasPrincipalValueIoi_value (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasPrincipalValueIoi (fun t : ℝ =>
      ((Real.exp (-x * t) * t ^ n / (1 - t) : ℝ) : ℂ)) 0 1
      ((value n x * n.factorial / x ^ (n + 1) : ℝ) : ℂ) := by
  sorry

/-- The exact fixed-index Ei converging-factor differential equation.
Olver, Chapter 14, §4, pp. 527–530. -/
theorem value_differential_equation (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x * deriv (value n) x + (x - n - 1) * value n x = x := by
  sorry

/-- The exact adjacent-index relation. Olver, Chapter 14, §4, pp. 527–530. -/
theorem value_succ (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (n + 1 : ℝ) * value (n + 1) x = x * value n x - x := by
  sorry

/-- The subtracted saddle amplitude is analytic at its removable point.
Olver, Chapter 14, §4, pp. 527–530. -/
theorem analyticAt_regularizedAmplitude_zero (ζ : ℝ) :
    AnalyticAt ℝ (regularizedAmplitude ζ) 0 := by
  sorry

/-- The exact Gaussian saddle representation after subtracting the odd pole.
Olver, Chapter 14, §4, pp. 527–530. -/
theorem value_eq_gaussian_integral {n : ℕ} (hn : 1 ≤ n) {ζ : ℝ} (hx : 0 < n + ζ) :
    value n (n + ζ) = Real.exp (-(n + ζ)) * (n + ζ) ^ (n + 1) / n.factorial *
      ∫ s : ℝ, Real.exp (-(n : ℝ) * s ^ 2 / 2) * regularizedAmplitude ζ s := by
  sorry

/-- The initial polynomial is zeta-1/3. Olver, Chapter 14, §4, pp. 527–530. -/
theorem coefficient_zero (ζ : ℝ) : coefficient 0 ζ = ζ - 1 / 3 := by
  sorry

/-- The saddle algorithm produces a polynomial at every order.
Olver, Chapter 14, §4, pp. 527–530. -/
theorem exists_polynomial_coefficient (j : ℕ) :
    ∃ p : ℝ[X], ∀ ζ : ℝ, coefficient j ζ = p.eval ζ := by
  sorry

/-- The full growing-index Ei expansion is uniform for bounded real zeta.
Olver, Chapter 14, §4, pp. 527–530. -/
theorem exists_uniform_growing_index_remainder_le {A : ℝ} (hA : 0 ≤ A) (N : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ ζ ∈ Icc (-A) A, |value n (n + ζ) -
        ∑ s ∈ Finset.range N, coefficient s ζ / (n : ℝ) ^ s| ≤ M / (n : ℝ) ^ N := by
  sorry

end DLMF.Confluent.EiConvergingFactor
