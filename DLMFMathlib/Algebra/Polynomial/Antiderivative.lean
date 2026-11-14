/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Polynomial antiderivatives

* `Polynomial.exists_derivative_eq`: differentiation is surjective over a
  characteristic-zero field.

The proof integrates monomials and uses polynomial induction.
-/

public section

open Polynomial

namespace Polynomial

/-- Every polynomial over a characteristic-zero field has a polynomial antiderivative. -/
lemma exists_derivative_eq {K : Type*} [Field K] [CharZero K] (P : K[X]) :
    ∃ Q : K[X], derivative Q = P := by
  induction P using Polynomial.induction_on' with
  | add P R hP hR =>
    obtain ⟨Q, hQ⟩ := hP
    obtain ⟨S, hS⟩ := hR
    exact ⟨Q + S, by rw [derivative_add, hQ, hS]⟩
  | monomial n a =>
    refine ⟨C (a / (n + 1 : K)) * X ^ (n + 1), ?_⟩
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow,
      Nat.add_sub_cancel, ← mul_assoc, ← C_mul]
    have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    rw [Nat.cast_add, Nat.cast_one, div_mul_cancel₀ a hn, C_mul_X_pow_eq_monomial]

end Polynomial
