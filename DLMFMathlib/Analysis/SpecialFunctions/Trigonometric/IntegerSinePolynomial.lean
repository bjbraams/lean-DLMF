/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Integer polynomials for odd multiples of sine

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 1, Lemma 1.15,
constructs a polynomial with integer coefficients taking `sin x` to `sin((2k+1)x)`.
The explicit binomial formula also records its degree and its first derivative at zero.
-/

@[expose] public noncomputable section

open Finset

namespace Polynomial

/-- The integer polynomial realizing an odd multiple of sine.
Duverney Chapter 1, Lemma 1.15, synopsis DU-1.12. -/
def integerSinePolynomial (k : ℕ) : ℤ[X] :=
  ∑ j ∈ range (k + 1), C ((-1 : ℤ) ^ j * ((2 * k + 1).choose (2 * j + 1) : ℤ)) *
    X ^ (2 * j + 1) * (1 - X ^ 2) ^ (k - j)

/-- The finite binomial formula for the odd sine polynomial.
Duverney Chapter 1, Lemma 1.15, synopsis DU-1.12. -/
theorem integerSinePolynomial_def (k : ℕ) :
    integerSinePolynomial k = ∑ j ∈ range (k + 1),
      C ((-1 : ℤ) ^ j * ((2 * k + 1).choose (2 * j + 1) : ℤ)) *
        X ^ (2 * j + 1) * (1 - X ^ 2) ^ (k - j) := rfl

/-- The exact degree of the odd sine polynomial.
Duverney Chapter 1, Lemma 1.15, synopsis DU-1.12. -/
theorem natDegree_integerSinePolynomial (k : ℕ) :
    (integerSinePolynomial k).natDegree = 2 * k + 1 := by
  sorry

/-- The odd sine polynomial vanishes at zero.
Duverney Chapter 1, Lemma 1.15, synopsis DU-1.12. -/
theorem integerSinePolynomial_eval_zero (k : ℕ) :
    (integerSinePolynomial k).eval 0 = 0 := by
  simp [integerSinePolynomial, eval_finsetSum]

/-- Its derivative at zero is the odd multiplier.
Duverney Chapter 1, Lemma 1.15, synopsis DU-1.12. -/
theorem derivative_integerSinePolynomial_eval_zero (k : ℕ) :
    (integerSinePolynomial k).derivative.eval 0 = (2 * k + 1 : ℤ) := by
  sorry

/-- Evaluation at `sin x` gives the sine of the odd multiple.
Duverney Chapter 1, Lemma 1.15, synopsis DU-1.12. -/
theorem integerSinePolynomial_eval_sin (k : ℕ) (x : ℝ) :
    (integerSinePolynomial k).eval₂ (Int.castRingHom ℝ) (Real.sin x) =
      Real.sin ((2 * k + 1) * x) := by
  sorry

end Polynomial
