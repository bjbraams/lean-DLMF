/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Majorants for Frobenius coefficient sequences

The coefficient estimates in Kristensson, *Second Order Differential Equations*,
Chapter 2, Lemmas 2.7–2.9. Theorems are expressed directly in terms of the
coefficient equations, so they apply to any construction of the Frobenius recursion.
-/

@[expose] public section

open scoped BigOperators

namespace Complex

/-- Kristensson, Lemma 2.7, p. 15: shifting an indicial root factors the indicial
polynomial as `n (n + α₁ - α₂)`. -/
theorem frobenius_indicial_shift {p q α₁ α₂ : ℂ}
    (hsum : α₁ + α₂ = 1 - p) (hprod : α₁ * α₂ = q) (n : ℂ) :
    (α₁ + n) * (α₁ + n - 1) + p * (α₁ + n) + q = n * (n + α₁ - α₂) := by
  rw [← hprod]
  linear_combination (α₁ + n) * hsum

/-- Kristensson, Lemma 2.8, pp. 15–16: a geometric majorant for the Frobenius
coefficients belonging to a root of largest real part. -/
theorem norm_frobenius_coefficient_le {p q a : ℕ → ℂ} {α₁ α₂ : ℂ} {M r : ℝ}
    (hM : 1 < M) (hr : 0 < r) (ha₀ : a 0 = 1)
    (hsum : α₁ + α₂ = 1 - p 0) (hprod : α₁ * α₂ = q 0)
    (horder : α₂.re ≤ α₁.re)
    (hp : ∀ n, 1 ≤ n → ‖p n‖ ≤ M / r ^ n)
    (hq : ∀ n, 1 ≤ n → ‖α₁ * p n + q n‖ ≤ M / r ^ n)
    (hrec : ∀ n, 1 ≤ n →
      ((α₁ + n) * (α₁ + n - 1) + p 0 * (α₁ + n) + q 0) * a n =
        -∑ j ∈ Finset.range n, a j * ((α₁ + j) * p (n - j) + q (n - j))) :
    ∀ n, ‖a n‖ ≤ M ^ n / r ^ n := by
  sorry

/-- Kristensson, Lemma 2.9, pp. 16–17: the second nonresonant Frobenius recursion
also admits a geometric majorant, after enlarging the coefficient bound. -/
theorem exists_norm_frobenius_coefficient_le {p q a : ℕ → ℂ} {α₁ α₂ : ℂ} {M r : ℝ}
    (hM : 0 < M) (hr : 0 < r) (ha₀ : a 0 = 1)
    (hsum : α₁ + α₂ = 1 - p 0) (hprod : α₁ * α₂ = q 0)
    (hnonres : ∀ n : ℕ, 1 ≤ n → α₁ - α₂ ≠ n)
    (hp : ∀ n, 1 ≤ n → ‖p n‖ ≤ M / r ^ n)
    (hq : ∀ n, 1 ≤ n → ‖α₂ * p n + q n‖ ≤ M / r ^ n)
    (hrec : ∀ n, 1 ≤ n →
      ((α₂ + n) * (α₂ + n - 1) + p 0 * (α₂ + n) + q 0) * a n =
        -∑ j ∈ Finset.range n, a j * ((α₂ + j) * p (n - j) + q (n - j))) :
    ∃ M' : ℝ, 1 < M' ∧ ∀ n, ‖a n‖ ≤ M' ^ n / r ^ n := by
  sorry

/-- Kristensson, Lemmas 2.8–2.9 and Theorem 2.3: a geometric coefficient majorant
gives absolute convergence on the corresponding open disc. -/
theorem summable_frobenius_of_geometric_majorant {a : ℕ → ℂ} {M r : ℝ}
    (hM : 0 < M) (hr : 0 < r) (ha : ∀ n, ‖a n‖ ≤ M ^ n / r ^ n)
    {z : ℂ} (hz : ‖z‖ < r / M) : Summable (fun n => a n * z ^ n) := by
  have hratio : M * ‖z‖ / r < 1 := by
    rw [div_lt_one hr]
    have h := (lt_div_iff₀ hM).1 hz
    nlinarith
  refine (hasSum_geometric_of_lt_one (by positivity : 0 ≤ M * ‖z‖ / r)
    hratio).summable.of_norm_bounded fun n => ?_
  rw [norm_mul, norm_pow]
  calc
    ‖a n‖ * ‖z‖ ^ n ≤ (M ^ n / r ^ n) * ‖z‖ ^ n := by
      exact mul_le_mul_of_nonneg_right (ha n) (by positivity)
    _ = (M * ‖z‖ / r) ^ n := by rw [div_pow, mul_pow]; ring

end Complex
