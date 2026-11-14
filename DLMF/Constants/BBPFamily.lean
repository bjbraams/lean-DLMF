/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Polylog
public import DLMF.Constants.BBP

/-!
# BBP series with polynomial numerators

The general integral algorithm and root-of-unity evaluation in Duverney,
*An Introduction to Hypergeometric Functions*, Chapter 8, equations
(8.79), (8.92)–(8.95), and (8.98)–(8.99). Coefficients may be complex;
the real-coefficient formulas in the source follow by inclusion.
-/

@[expose] public noncomputable section

open Complex Finset MeasureTheory
open scoped Real

namespace DLMF.Constants

/-- A BBP series grouped in arithmetic progressions, with radix `a`, length `h`,
and order `n`. The intended domain is `|a|≥2`, `h≥2`, `n≥1`; outside it this is
Lean's totalized sum. Duverney (8.79), synopsis DU-8.18. -/
def bbpSeries (a : ℤ) (h n : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑' k : ℕ, (a : ℂ) ^ (-(k : ℤ)) *
    ∑ l ∈ Icc 1 (h - 1), b l / ((h * k + l : ℕ) : ℂ) ^ n

/-- The defining BBP series. Duverney (8.79), synopsis DU-8.18. -/
theorem bbpSeries_def (a : ℤ) (h n : ℕ) (b : ℕ → ℂ) :
    bbpSeries a h n b = ∑' k : ℕ, (a : ℂ) ^ (-(k : ℤ)) *
      ∑ l ∈ Icc 1 (h - 1), b l / ((h * k + l : ℕ) : ℂ) ^ n := rfl

/-- Absolute convergence of the grouped BBP series.
Duverney (8.79), synopsis DU-8.18. -/
theorem summable_bbpSeries {a : ℤ} (ha : 2 ≤ |a|) {h n : ℕ}
    (hh : 2 ≤ h) (hn : 1 ≤ n) (b : ℕ → ℂ) :
    Summable (fun k : ℕ => (a : ℂ) ^ (-(k : ℤ)) *
      ∑ l ∈ Icc 1 (h - 1), b l / ((h * k + l : ℕ) : ℂ) ^ n) := by
  sorry

/-- The unit-interval algorithm for BBP series.
Duverney (8.92)–(8.95), synopsis DU-8.18. -/
theorem bbpSeries_eq_integral {a : ℤ} (ha : 2 ≤ |a|) {h n : ℕ}
    (hh : 2 ≤ h) (hn : 1 ≤ n) (b : ℕ → ℂ) :
    bbpSeries a h n b = (-1 : ℂ) ^ (n - 1) / (n - 1).factorial *
      ∫ x in (0 : ℝ)..1, (a : ℂ) *
        (∑ l ∈ Icc 1 (h - 1), b l * (x : ℂ) ^ (l - 1)) *
          (Real.log x : ℂ) ^ (n - 1) / ((a : ℂ) - (x : ℂ) ^ h) := by
  sorry

/-- Root-of-unity evaluation of a BBP series. All the polylogarithm arguments
have modulus below one; the formula holds for every chosen `h`th root of `a`.
Duverney (8.98)–(8.99), synopsis DU-8.19. -/
theorem bbpSeries_eq_sum_polylog {a : ℤ} (ha : 2 ≤ |a|) {h n : ℕ}
    (hh : 2 ≤ h) (hn : 1 ≤ n) (b : ℕ → ℂ) {ω : ℂ} (hω : ω ^ h = a) :
    bbpSeries a h n b = (h : ℂ)⁻¹ * ∑ j ∈ range h,
      (∑ l ∈ Icc 1 (h - 1), b l * (ω * exp (2 * π * I * j / h)) ^ l) *
        DLMF.Zeta.polylog n ((ω * exp (2 * π * I * j / h))⁻¹) := by
  sorry

end DLMF.Constants
