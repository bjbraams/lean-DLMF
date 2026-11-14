/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMFMathlib.Analysis.Complex.Joukowski
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Jacobi-polynomial expansions for Heun's equation

Kristensson, *Second Order Differential Equations*, §8.4, (8.8)–(8.16),
Lemmas 8.1–8.3 and Theorem 8.2. The polynomial basis is the terminating Mathlib
series `ordinaryHypergeometric (-n) (n + c + d - 1) c z`, used directly.
The accessory parameter is `q = a * b * h`; the general project Heun equation
continues to use the unrestricted accessory parameter `q`.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology BigOperators Real

noncomputable section

namespace DLMF.Heun.JacobiExpansion

/-- Kristensson, (8.10), p. 148: the coefficient of the next basis polynomial
in multiplication by `z`, including the separately normalized index zero. -/
def upperCoefficient (c d : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then -c / (c + d) else
    -((n : ℂ) + c + d - 1) * (n + c) /
      ((2 * n + c + d - 1) * (2 * n + c + d))

/-- Kristensson, (8.10): the diagonal multiplication coefficient. -/
def diagonalCoefficient (c d : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then c / (c + d) else
    1 / 2 + (c + d - 2) * (c - d) /
      (2 * (2 * n + c + d - 2) * (2 * n + c + d))

/-- Kristensson, (8.10): the coefficient of the previous basis polynomial. -/
def lowerCoefficient (c d : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else -((n : ℂ) * (n + d - 1)) /
    ((2 * n + c + d - 1) * (2 * n + c + d - 2))

/-- Kristensson, (8.11): the upper coefficient for `z(z-1) d/dz`. -/
def derivativeUpperCoefficient (c d : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) * upperCoefficient c d n

/-- Kristensson, (8.11): the diagonal coefficient for `z(z-1) d/dz`. -/
def derivativeDiagonalCoefficient (c d : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) * (n + c + d - 1) * (c - d) /
    ((2 * n + c + d - 2) * (2 * n + c + d))

/-- Kristensson, (8.11): the lower coefficient for `z(z-1) d/dz`. -/
def derivativeLowerCoefficient (c d : ℂ) (n : ℕ) : ℂ :=
  -((n : ℂ) + c + d - 1) * lowerCoefficient c d n

/-- The explicit multiplication coefficients, Kristensson, (8.10). -/
theorem multiplication_coefficients_def (c d : ℂ) (n : ℕ) :
    upperCoefficient c d n = (if n = 0 then -c / (c + d) else
      -((n : ℂ) + c + d - 1) * (n + c) /
        ((2 * n + c + d - 1) * (2 * n + c + d))) ∧
    diagonalCoefficient c d n = (if n = 0 then c / (c + d) else
      1 / 2 + (c + d - 2) * (c - d) /
        (2 * (2 * n + c + d - 2) * (2 * n + c + d))) ∧
    lowerCoefficient c d n = (if n = 0 then 0 else -((n : ℂ) * (n + d - 1)) /
      ((2 * n + c + d - 1) * (2 * n + c + d - 2))) := ⟨rfl, rfl, rfl⟩

/-- The explicit differential coefficients, Kristensson, (8.11). -/
theorem derivative_coefficients_def (c d : ℂ) (n : ℕ) :
    derivativeUpperCoefficient c d n = (n : ℂ) * upperCoefficient c d n ∧
    derivativeDiagonalCoefficient c d n = (if n = 0 then 0 else
      (n : ℂ) * (n + c + d - 1) * (c - d) /
        ((2 * n + c + d - 2) * (2 * n + c + d))) ∧
    derivativeLowerCoefficient c d n =
      -((n : ℂ) + c + d - 1) * lowerCoefficient c d n := ⟨rfl, rfl, rfl⟩

/-- Kristensson, (8.10), pp. 147–148: multiplication by `z` in the normalized
Jacobi basis. This identity applies on the whole complex plane, since the series terminate. -/
theorem mul_basis {c d : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (n : ℕ)
    (hden : n = 0 ∨ (2 * (n : ℂ) + c + d - 1) * (2 * n + c + d - 2) *
      (2 * n + c + d) ≠ 0) (hcd : c + d ≠ 0) (z : ℂ) :
    let y := fun j : ℕ => ordinaryHypergeometric (-(j : ℂ)) (j + c + d - 1) c z
    z * y n = upperCoefficient c d n * y (n + 1) +
      diagonalCoefficient c d n * y n + lowerCoefficient c d n * y (n - 1) := by
  sorry

/-- Kristensson, (8.11), pp. 147–148: the tridiagonal action of `z(z-1) d/dz`
on the normalized Jacobi basis. -/
theorem mul_deriv_basis {c d : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (n : ℕ)
    (hden : n = 0 ∨ (2 * (n : ℂ) + c + d - 1) * (2 * n + c + d - 2) *
      (2 * n + c + d) ≠ 0) (hcd : c + d ≠ 0) (z : ℂ) :
    let y := fun j : ℕ => ordinaryHypergeometric (-(j : ℂ)) (j + c + d - 1) c
    z * (z - 1) * deriv (y n) z =
      derivativeUpperCoefficient c d n * y (n + 1) z +
      derivativeDiagonalCoefficient c d n * y n z +
      derivativeLowerCoefficient c d n * y (n - 1) z := by
  sorry

/-- Kristensson, Lemma 8.1, pp. 148–151: the ratio asymptotic of the normalized
Jacobi polynomials outside the focal segment, including eventual nonvanishing. -/
theorem basis_ratio_asymptotic {c d z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : z ∉ segment ℝ (0 : ℂ) 1)
    (hden : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℂ) + c + d - 1) *
      (2 * n + c + d - 2) * (2 * n + c + d) ≠ 0) :
    let y := fun n : ℕ => ordinaryHypergeometric (-(n : ℂ)) (n + c + d - 1) c z
    let s := Complex.Joukowski.outerInverse z
    (∀ᶠ n in atTop, y n ≠ 0) ∧
      (fun n => y (n + 1) / y n - s - s * (1 - 2 * c) / (2 * n))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
  sorry

/-- The two-term Jacobi-basis ratio expansion is uniform on every compact set
off the focal segment, and its denominators are uniformly eventually nonzero.
Kristensson, Chapter 8, Lemma 8.1, pp. 148–151. -/
theorem basis_ratio_asymptotic_uniform {c d : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hden : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℂ) + c + d - 1) *
      (2 * n + c + d - 2) * (2 * n + c + d) ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) (hsegment : K ⊆ (segment ℝ (0 : ℂ) 1)ᶜ) :
    let y := fun n : ℕ => fun z : ℂ =>
      ordinaryHypergeometric (-(n : ℂ)) (n + c + d - 1) c z
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ z ∈ K,
      y n z ≠ 0 ∧
        ‖y (n + 1) z / y n z - Complex.Joukowski.outerInverse z -
          Complex.Joukowski.outerInverse z * (1 - 2 * c) / (2 * n)‖ ≤
            C / (n : ℝ) ^ 2 := by
  sorry

/-- Kristensson, Lemma 8.2, pp. 151–153: the lower-row denominator of the
coefficient recurrence for a Heun expansion in normalized Jacobi polynomials. -/
def recurrenceDenominator (a b c d e : ℂ) (n : ℕ) : ℂ :=
  e * derivativeLowerCoefficient c d (n + 1) +
    (a * b + ((n : ℂ) + 1) * (n + c + d)) * lowerCoefficient c d (n + 1)

/-- Kristensson, Lemma 8.2: the leading recurrence coefficient `E_n`. -/
def recurrenceFirstCoefficient (A h a b c d e : ℂ) (n : ℕ) : ℂ :=
  -(e * derivativeDiagonalCoefficient c d n +
      (a * b + (n : ℂ) * (n + c + d - 1)) * diagonalCoefficient c d n -
        a * b * h - A * n * (n + c + d - 1)) / recurrenceDenominator a b c d e n

/-- Kristensson, Lemma 8.2: the trailing recurrence coefficient `F_n`, for `n≥1`. -/
def recurrenceSecondCoefficient (a b c d e : ℂ) (n : ℕ) : ℂ :=
  -(e * derivativeUpperCoefficient c d (n - 1) +
      (a * b + ((n : ℂ) - 1) * (n + c + d - 2)) * upperCoefficient c d (n - 1)) /
        recurrenceDenominator a b c d e n

/-- The denominator formula for the Jacobi coefficient recurrence, Kristensson,
Lemma 8.2. -/
theorem recurrenceDenominator_def (a b c d e : ℂ) (n : ℕ) :
    recurrenceDenominator a b c d e n = e * derivativeLowerCoefficient c d (n + 1) +
      (a * b + ((n : ℂ) + 1) * (n + c + d)) * lowerCoefficient c d (n + 1) := rfl

/-- The first coefficient formula for the Jacobi recurrence, Kristensson, Lemma 8.2. -/
theorem recurrenceFirstCoefficient_def (A h a b c d e : ℂ) (n : ℕ) :
    recurrenceFirstCoefficient A h a b c d e n =
      -(e * derivativeDiagonalCoefficient c d n +
        (a * b + (n : ℂ) * (n + c + d - 1)) * diagonalCoefficient c d n -
          a * b * h - A * n * (n + c + d - 1)) / recurrenceDenominator a b c d e n := rfl

/-- The second coefficient formula for the Jacobi recurrence, Kristensson, Lemma 8.2. -/
theorem recurrenceSecondCoefficient_def (a b c d e : ℂ) (n : ℕ) :
    recurrenceSecondCoefficient a b c d e n =
      -(e * derivativeUpperCoefficient c d (n - 1) +
        (a * b + ((n : ℂ) - 1) * (n + c + d - 2)) * upperCoefficient c d (n - 1)) /
          recurrenceDenominator a b c d e n := rfl

/-- Kristensson, Lemma 8.2: a locally uniformly convergent Jacobi expansion solves
Heun's equation exactly when its coefficients obey the displayed recurrence and initial
row. The open neighborhood contains the whole focal segment, so coefficient comparison
uses the Jacobi orthogonality interval. -/
theorem isHeunSolutionOn_iff_recurrence {A h a b c d e : ℂ} {k : ℕ → ℂ}
    {u : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hseg : segment ℝ (0 : ℂ) 1 ⊆ U)
    (hc : 0 < c.re) (hd : 0 < d.re) (hA : 1 < ‖A‖)
    (hbalance : a + b + 1 = c + d + e)
    (hden : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℂ) + c + d - 1) *
      (2 * n + c + d - 2) * (2 * n + c + d) ≠ 0)
    (hD : ∀ n, recurrenceDenominator a b c d e n ≠ 0)
    (hconv : TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N,
      k n * ordinaryHypergeometric (-(n : ℂ)) (n + c + d - 1) c z) u atTop U) :
    IsHeunSolutionOn A (a * b * h) a b c d e u (U \ {0, 1, A}) ↔
      k 1 = recurrenceFirstCoefficient A h a b c d e 0 * k 0 ∧
        ∀ n, 1 ≤ n → k (n + 1) = recurrenceFirstCoefficient A h a b c d e n * k n +
          recurrenceSecondCoefficient a b c d e n * k (n - 1) := by
  sorry

/-- Kristensson, Lemma 8.2: the explicit first coefficient of the Jacobi expansion. -/
theorem recurrenceFirstCoefficient_zero (A h a b c d e : ℂ)
    (hcd : c + d ≠ 0) (hd : d ≠ 0) (hcd1 : c + d + 1 ≠ 0)
    (hden : (e - 1) * (c + d) - a * b ≠ 0) :
    recurrenceFirstCoefficient A h a b c d e 0 =
      -(a * b * (c + d + 1) * (c - h * (c + d))) /
        (d * ((e - 1) * (c + d) - a * b)) := by
  sorry

/-- Kristensson, Lemma 8.2: the first two asymptotic terms of the two coefficient
functions for the Jacobi expansion recurrence. -/
theorem recurrence_coefficients_asymptotic (A h a b c d e : ℂ) :
    (fun n => recurrenceFirstCoefficient A h a b c d e n -
      (2 - 4 * A) - (1 - 2 * A) * (2 * c + 2 * e - 5) / n)
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) ∧
    (fun n => recurrenceSecondCoefficient a b c d e n + 1 + (2 * c + 2 * e - 5) / n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
  sorry

/-- Kristensson, Lemma 8.3: the two possible ratio asymptotics of a nonterminating
Jacobi expansion coefficient sequence. The recurrence coefficients are nonzero as in the
Poincaré–Perron hypotheses. -/
theorem coefficient_ratio_asymptotic {A h a b c d e : ℂ} {k : ℕ → ℂ}
    (hA : A ∉ segment ℝ (0 : ℂ) 1)
    (hD : ∀ n, 1 ≤ n → recurrenceDenominator a b c d e n ≠ 0)
    (hF : ∀ n, 1 ≤ n → recurrenceSecondCoefficient a b c d e n ≠ 0)
    (hk : ∀ n, 1 ≤ n → k (n + 1) = recurrenceFirstCoefficient A h a b c d e n * k n +
      recurrenceSecondCoefficient a b c d e n * k (n - 1))
    (hne : ∃ᶠ n in atTop, k n ≠ 0) :
    ∃ t : ℂ, (t = Complex.Joukowski.outerInverse A ∨
      t = (Complex.Joukowski.outerInverse A)⁻¹) ∧
      (∀ᶠ n in atTop, k n ≠ 0) ∧
      (fun n => k (n + 1) / k n - t -
        t * (2 * c + 2 * e - 5) * ((1 - 2 * A) * t - 1) / ((t ^ 2 - 1) * n))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
  sorry

/-- Kristensson, Theorem 8.2: the minimal Jacobi expansion converges absolutely
inside the ellipse through the singularity `A`, off the focal segment. -/
theorem summable_of_ratio_lt {c d z t : ℂ} {k : ℕ → ℂ}
    (hc : ∀ j : ℕ, c ≠ -(j : ℂ)) (hz : z ∉ segment ℝ (0 : ℂ) 1)
    (hden : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℂ) + c + d - 1) *
      (2 * n + c + d - 2) * (2 * n + c + d) ≠ 0)
    (hk : ∀ᶠ n in atTop, k n ≠ 0)
    (hratio : Tendsto (fun n => k (n + 1) / k n) atTop (𝓝 t))
    (hlt : ‖t * Complex.Joukowski.outerInverse z‖ < 1) :
    Summable (fun n => ‖k n * ordinaryHypergeometric (-(n : ℂ))
      (n + c + d - 1) c z‖) := by
  sorry

/-- Kristensson, Theorem 8.2: the Jacobi expansion diverges outside its ellipse;
in particular a generic coefficient solution diverges everywhere off the focal segment. -/
theorem not_summable_of_ratio_gt {c d z t : ℂ} {k : ℕ → ℂ}
    (hc : ∀ j : ℕ, c ≠ -(j : ℂ)) (hz : z ∉ segment ℝ (0 : ℂ) 1)
    (hden : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℂ) + c + d - 1) *
      (2 * n + c + d - 2) * (2 * n + c + d) ≠ 0)
    (hk : ∀ᶠ n in atTop, k n ≠ 0)
    (hratio : Tendsto (fun n => k (n + 1) / k n) atTop (𝓝 t))
    (hlt : 1 < ‖t * Complex.Joukowski.outerInverse z‖) :
    ¬Summable (fun n => k n * ordinaryHypergeometric (-(n : ℂ))
      (n + c + d - 1) c z) := by
  sorry

/-- Kristensson, Theorem 8.2: the term-ratio magnitude on the convergence ellipse
has first correction `(Re e - 2)/n`. -/
theorem norm_term_ratio_boundary {c d e z t : ℂ} {k : ℕ → ℂ}
    (hc : ∀ j : ℕ, c ≠ -(j : ℂ)) (hz : z ∉ segment ℝ (0 : ℂ) 1)
    (hden : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℂ) + c + d - 1) *
      (2 * n + c + d - 2) * (2 * n + c + d) ≠ 0)
    (hk : ∀ᶠ n in atTop, k n ≠ 0)
    (hratio : (fun n => k (n + 1) / k n - t - t * (2 * c + 2 * e - 5) / (2 * n))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)))
    (hboundary : ‖t * Complex.Joukowski.outerInverse z‖ = 1) :
    let v := fun n => k n * ordinaryHypergeometric (-(n : ℂ)) (n + c + d - 1) c z
    (fun n => ‖v (n + 1)‖ / ‖v n‖ - 1 - (e.re - 2) / n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
  sorry

/-- Kristensson, Theorem 8.2: absolute boundary convergence of a nonterminating
Jacobi expansion when `Re e < 1`. -/
theorem summable_boundary {c d e z t : ℂ} {k : ℕ → ℂ}
    (hc : ∀ j : ℕ, c ≠ -(j : ℂ)) (hz : z ∉ segment ℝ (0 : ℂ) 1)
    (he : e.re < 1)
    (hden : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℂ) + c + d - 1) *
      (2 * n + c + d - 2) * (2 * n + c + d) ≠ 0)
    (hk : ∀ᶠ n in atTop, k n ≠ 0)
    (hratio : (fun n => k (n + 1) / k n - t - t * (2 * c + 2 * e - 5) / (2 * n))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)))
    (hboundary : ‖t * Complex.Joukowski.outerInverse z‖ = 1) :
    Summable (fun n => ‖k n * ordinaryHypergeometric (-(n : ℂ))
      (n + c + d - 1) c z‖) := by
  sorry

end DLMF.Heun.JacobiExpansion
