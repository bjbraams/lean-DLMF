/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Algebra.Polynomial.FiniteDifference
public import DLMFMathlib.RingTheory.Binomial
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Newton's finite expansion in binomial polynomials

The polynomial form of the Gregory–Newton formula at arbitrary scalar arguments,
as in Duverney, *An Introduction to Hypergeometric Functions*, Exercise 3.18,
equation (3.65). The coefficients are the iterated forward differences at zero.
-/

@[expose] public noncomputable section

open Finset

namespace Polynomial

/-- Newton's binomial expansion for a polynomial over a field of characteristic zero.
Duverney Chapter 3, Exercise 3.18, (3.65), synopsis DU-3.20. -/
theorem eval_eq_sum_fwdDiff_mul_choose {K : Type*} [Field K] [CharZero K]
    (P : K[X]) {N : ℕ} (hP : P.natDegree ≤ N) (x : K) :
    P.eval x = ∑ k ∈ range (N + 1),
      (fwdDiff (1 : K))^[k] (fun y => P.eval y) 0 * Ring.choose x k := by
  sorry

end Polynomial
