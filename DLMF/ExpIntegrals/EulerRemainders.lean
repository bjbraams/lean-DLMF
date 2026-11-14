/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.ConvergingFactors
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Signed once- and twice-Euler-transformed E1 remainders

Olver, *Asymptotics and Special Functions*, Chapter 14, §7,
(7.05)–(7.07), pp. 541–543, synopsis O-14.07. The second expansion
reexpands the residual denominator about t=3. Even truncation indices keep
both centered powers nonnegative, giving the exact factors two and four.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace DLMF.Confluent.ExponentialEulerRemainder

/-- The original signed E1 integral remainder. Olver (7.05). -/
def value (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n / (1 + t)

/-- A term of the first denominator expansion about t=1. Olver (7.06). -/
def firstTerm (n j : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + j) / 2 ^ (j + 1) *
    ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n * (t - 1) ^ j

/-- The first transformed residual. Olver (7.07). -/
def firstError (n m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + m) / 2 ^ m *
    ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n * (t - 1) ^ m / (1 + t)

/-- A term of the second Euler expansion, centered at t=3.
Olver, Chapter 14, §7.3, pp. 542–543. -/
def secondTerm (n m j : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + m + j) / 2 ^ (m + 2 * j + 2) *
    ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n * (t - 1) ^ m * (t - 3) ^ j

/-- The residual after two finite Euler transformations. Olver §7.3. -/
def secondError (n m l : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + m + l) / 2 ^ (m + 2 * l) *
    ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * t) * t ^ n * (t - 1) ^ m * (t - 3) ^ l / (1 + t)

/-- The defining original remainder integral. -/
theorem value_def (n : ℕ) (x : ℝ) : value n x =
    (-1 : ℝ) ^ n * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n / (1 + t) := rfl

/-- The defining first transformed term. -/
theorem firstTerm_def (n j : ℕ) (x : ℝ) : firstTerm n j x =
    (-1 : ℝ) ^ (n + j) / 2 ^ (j + 1) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n * (t - 1) ^ j := rfl

/-- The defining first transformed residual. -/
theorem firstError_def (n m : ℕ) (x : ℝ) : firstError n m x =
    (-1 : ℝ) ^ (n + m) / 2 ^ m *
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n * (t - 1) ^ m / (1 + t) := rfl

/-- The defining second transformed term. -/
theorem secondTerm_def (n m j : ℕ) (x : ℝ) : secondTerm n m j x =
    (-1 : ℝ) ^ (n + m + j) / 2 ^ (m + 2 * j + 2) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ n * (t - 1) ^ m * (t - 3) ^ j := rfl

/-- The defining second transformed residual. -/
theorem secondError_def (n m l : ℕ) (x : ℝ) : secondError n m l x =
    (-1 : ℝ) ^ (n + m + l) / 2 ^ (m + 2 * l) *
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-x * t) * t ^ n * (t - 1) ^ m * (t - 3) ^ l / (1 + t) := rfl

/-- The exact finite first transformation. Olver, Chapter 14, (7.06)–(7.07). -/
theorem value_eq_sum_firstTerm_add_error (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    value n x = (∑ j ∈ Finset.range m, firstTerm n j x) + firstError n m x := by
  sorry

/-- Each transformed term is an explicit finite binomial sum of Gamma moments.
Olver, Chapter 14, (7.06), pp. 542–543. -/
theorem firstTerm_eq_finite_factorial_sum (n j : ℕ) {x : ℝ} (hx : 0 < x) :
    firstTerm n j x = (-1 : ℝ) ^ (n + j) / 2 ^ (j + 1) *
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (-1 : ℝ) ^ (j - k) *
        (n + k).factorial / x ^ (n + k + 1) := by
  sorry

/-- At an even first truncation the residual has the first omitted term's sign
and at most twice its magnitude. Olver, Chapter 14, §7.3. -/
theorem firstError_sign_and_abs_le (n : ℕ) {m : ℕ} (hm : Even m)
    {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1 : ℝ) ^ n * firstError n m x ∧
      |firstError n m x| ≤ 2 * |firstTerm n m x| := by
  sorry

/-- The second finite transformation of the actual first residual.
Olver, Chapter 14, §7.3, pp. 542–543. -/
theorem firstError_eq_sum_secondTerm_add_error (n m l : ℕ) {x : ℝ} (hx : 0 < x) :
    firstError n m x = (∑ j ∈ Finset.range l, secondTerm n m j x) +
      secondError n m l x := by
  sorry

/-- At two even truncations the second residual has the omitted term's sign
and at most four times its magnitude. Olver, Chapter 14, §7.3, pp. 542–543. -/
theorem secondError_sign_and_abs_le (n : ℕ) {m l : ℕ} (hm : Even m) (hl : Even l)
    {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1 : ℝ) ^ n * secondError n m l x ∧
      |secondError n m l x| ≤ 4 * |secondTerm n m l x| := by
  sorry

end DLMF.Confluent.ExponentialEulerRemainder
