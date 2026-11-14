/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Additive
public import Mathlib.NumberTheory.Divisors
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Representations by the form x²+2y²

The additional binary quadratic representation formula in Andrews, Askey and Roy,
*Special Functions*, Theorem 10.6.1. Signs are counted and coordinates are ordered.
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace DLMF.NumberTheory

/-- The number of signed ordered integer representations by x²+2y².
Andrews–Askey–Roy, *Special Functions*, Theorem 10.6.1
(synopsis AAR-10.4.1–10.6.1). -/
def sumSquareTwiceSquareCount (n : ℕ) : ℕ :=
  Nat.card {v : ℤ × ℤ // v.1 ^ 2 + 2 * v.2 ^ 2 = n}

/-- The representation-type cardinal defining the count. -/
theorem sumSquareTwiceSquareCount_def (n : ℕ) :
    sumSquareTwiceSquareCount n =
      Nat.card {v : ℤ × ℤ // v.1 ^ 2 + 2 * v.2 ^ 2 = n} := rfl

/-- The representation type of a fixed nonnegative integer is finite.
Andrews–Askey–Roy, *Special Functions*, Theorem 10.6.1
(synopsis AAR-10.4.1–10.6.1). -/
theorem finite_sumSquareTwiceSquare_representations (n : ℕ) :
    Finite {v : ℤ × ℤ // v.1 ^ 2 + 2 * v.2 ^ 2 = n} := by
  sorry

/-- Zero has one signed ordered representation. Andrews–Askey–Roy,
*Special Functions*, §10.6 (synopsis AAR-10.4.1–10.6.1). -/
theorem sumSquareTwiceSquareCount_zero : sumSquareTwiceSquareCount 0 = 1 := by
  sorry

/-- The divisor-class formula for x²+2y².
Andrews–Askey–Roy, *Special Functions*, Theorem 10.6.1
(synopsis AAR-10.4.1–10.6.1). -/
theorem sumSquareTwiceSquareCount_eq_divisor_classes {n : ℕ} (hn : 1 ≤ n) :
    (sumSquareTwiceSquareCount n : ℤ) =
      2 * (((n.divisors.filter fun d => d % 8 = 1).card : ℤ) +
        (n.divisors.filter fun d => d % 8 = 3).card -
        (n.divisors.filter fun d => d % 8 = 5).card -
        (n.divisors.filter fun d => d % 8 = 7).card) := by
  sorry

/-- Jacobi's four-square divisor formula with all multiples of four excluded.
Andrews–Askey–Roy, *Special Functions*, Theorem 10.6.1, synopsis AAR-10.4.1–10.6.1.
Signs and coordinate order are both counted by the canonical `sumSquaresCount`. -/
theorem sumSquaresCount_four_eq_sum_divisors_not_dvd_four {n : ℕ} (hn : 1 ≤ n) :
    sumSquaresCount 4 n = 8 * ∑ d ∈ n.divisors.filter (fun d => ¬4 ∣ d), d := by
  sorry

end DLMF.NumberTheory
