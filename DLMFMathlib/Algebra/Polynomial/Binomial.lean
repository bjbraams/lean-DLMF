/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-!
# Binomial polynomials

Mathlib's `Ring.choose (X : K[X]) k` provides the binomial polynomial over a
characteristic-zero field. These polynomials have integral values at natural numbers,
the usual forward difference recurrence, and span the polynomial ring.

* `Polynomial.eval_choose_X_natCast`: natural values.
* `Polynomial.comp_choose_X_add_one_sub`: the forward difference.
* `Polynomial.choose_X_eq_C_mul_descPochhammer`: the factorial formula.
* `Polynomial.exists_sum_C_mul_choose_X`: finite spanning.

The proof uses Mathlib's native `Ring.choose` API, polynomial sequences and their bases.
-/

public noncomputable section

open Finset
open scoped Nat

namespace Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The binomial polynomial evaluated at a natural number is the corresponding
binomial coefficient. -/
lemma eval_choose_X_natCast (k j : ℕ) :
    (Ring.choose (X : K[X]) k).eval (j : K) = (j.choose k : K) := by
  have h := Ring.map_choose (Polynomial.evalRingHom (j : K)) (X : K[X]) k
  simpa only [coe_evalRingHom, eval_X, Ring.choose_natCast] using h

/-- The forward difference of a binomial polynomial is the preceding polynomial. -/
lemma comp_choose_X_add_one_sub (k : ℕ) :
    (Ring.choose (X : K[X]) (k + 1)).comp (X + 1) - Ring.choose X (k + 1) = Ring.choose X k := by
  have h := Ring.map_choose (Polynomial.compRingHom (X + 1 : K[X])) (X : K[X]) (k + 1)
  simp only [coe_compRingHom_apply, X_comp, Ring.choose_succ_succ] at h
  linear_combination h

/-- The binomial polynomial is the falling factorial divided by its factorial. -/
lemma choose_X_eq_C_mul_descPochhammer (k : ℕ) :
    Ring.choose (X : K[X]) k = C (1 / (k ! : K)) * descPochhammer K k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Nat.cast_injective (R := K)))
  rintro _ ⟨j, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_choose_X_natCast, eval_mul, eval_C,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  have hz : (k ! : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- Every polynomial over a characteristic-zero field is a finite linear combination
of binomial polynomials. -/
lemma exists_sum_C_mul_choose_X (P : K[X]) :
    ∃ (N : ℕ) (c : ℕ → K), P = ∑ k ∈ range N, C (c k) * Ring.choose (X : K[X]) k := by
  have hdeg (k : ℕ) : (Ring.choose (X : K[X]) k).degree = k := by
    rw [choose_X_eq_C_mul_descPochhammer, degree_C_mul
      (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))),
      degree_eq_natDegree (monic_descPochhammer K k).ne_zero, descPochhammer_natDegree]
  let S : Sequence K := ⟨fun k => Ring.choose (X : K[X]) k, hdeg⟩
  let b := S.basis fun k => isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (by
    intro h
    dsimp only [S] at h
    have he := hdeg k
    rw [h, degree_zero] at he
    exact WithBot.bot_ne_coe he))
  let c := b.repr P
  obtain ⟨N, hN⟩ := c.support.exists_nat_subset_range
  refine ⟨N, c, ?_⟩
  have he : (∑ k ∈ c.support, C (c k) * Ring.choose (X : K[X]) k) = P := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, c, b, Sequence.basis_eq_self,
      S, smul_eq_C_mul] using b.linearCombination_repr P
  rw [← he]
  apply sum_subset hN
  intro k _ hk
  simp only [Finsupp.notMem_support_iff.mp hk, map_zero, zero_mul]

end Polynomial
