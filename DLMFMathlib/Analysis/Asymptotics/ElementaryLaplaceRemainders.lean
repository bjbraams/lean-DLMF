/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Exact elementary Laplace remainders

Olver, *Asymptotics and Special Functions*, Chapter 1, §1, pp. 1–4,
synopsis O-1.01. Finite identities and first-omitted-term bounds remain
meaningful even when the associated full factorial series diverges.
-/

@[expose] public section

open MeasureTheory Filter

namespace Real

/-- The cosine Laplace integral has an exact finite geometric remainder.
Olver, Chapter 1, §1, pp. 1–2, synopsis O-1.01. Its value is the already known
`s/(s²+1)`; the finite identity is valid at every positive `s`. -/
theorem integral_exp_neg_mul_cos_eq_sum_add {x : ℝ} (hx : 0 < x) (N : ℕ) :
    let F := ∫ t : ℝ in Set.Ioi 0, exp (-x * t) * cos t
    F = (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k / x ^ (2 * k + 1)) +
      (-1 : ℝ) ^ N / x ^ (2 * N) * F := by
  sorry

/-- The factorial Laplace prototype has an exact signed integral remainder strictly
between zero and the first omitted term. Olver, Chapter 1, §1, pp. 2–4,
synopsis O-1.01. The assertion includes truncation index zero. -/
theorem integral_exp_neg_mul_div_one_add_remainder {x : ℝ} (hx : 0 < x) (N : ℕ) :
    let G := ∫ t : ℝ in Set.Ioi 0, exp (-x * t) / (1 + t)
    let R := G - ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * k.factorial / x ^ (k + 1)
    IntegrableOn (fun t : ℝ => exp (-x * t) * t ^ N / (1 + t)) (Set.Ioi 0) ∧
      R = (-1 : ℝ) ^ N * ∫ t : ℝ in Set.Ioi 0, exp (-x * t) * t ^ N / (1 + t) ∧
      0 < (-1 : ℝ) ^ N * R ∧ (-1 : ℝ) ^ N * R < N.factorial / x ^ (N + 1) := by
  sorry

/-- At every fixed positive argument the factorial Laplace terms grow without bound.
Olver, Chapter 1, §1, pp. 2–4, synopsis O-1.01. Consequently the full formal
series cannot converge, despite its strictly controlled finite remainders. -/
theorem tendsto_factorial_div_pow_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => (N.factorial : ℝ) / x ^ (N + 1)) atTop atTop := by
  sorry

end Real
