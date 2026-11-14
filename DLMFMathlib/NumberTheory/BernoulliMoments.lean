/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.Pochhammer
import DLMFMathlib.Algebra.Polynomial.CentralFactorial
import Mathlib.Algebra.Polynomial.Basis
import DLMFMathlib.Algebra.Polynomial.Antiderivative
import DLMFMathlib.Algebra.Polynomial.FiniteDifference
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-!
# Bernoulli moments in factorial bases

Bernoulli numbers define a linear functional on polynomials whose value on a forward
difference is the derivative at zero. A discrete antiderivative evaluates the mixed
rising and falling factorial moments as `(-1)ʲ k! j! / (k+j+1)`.

* `Polynomial.exists_linearMap_pow_eq_bernoulli`: existence over a characteristic-zero field.
* `Polynomial.exists_linearMap_pow_eq_regularized_bernoulli`: regularized moment averaging.
* `Polynomial.apply_ascPochhammer_mul_descPochhammer`: the mixed factorial moments.
* `Polynomial.eval_ascPochhammer_add_one_mul_eval_descPochhammer`: the factorial product.

The construction uses Mathlib's monomial basis and `sum_bernoulli`. The discrete primitive
uses the falling-factorial difference and root-derivative APIs from
`DLMFMathlib.Algebra.Polynomial.CentralFactorial`.
-/

public noncomputable section

open Finset Polynomial
open scoped Nat

namespace Polynomial

/-- A rising factorial at `x + 1` times a falling factorial at `x` is a shifted
falling factorial. -/
lemma eval_ascPochhammer_add_one_mul_eval_descPochhammer {R : Type*} [CommRing R]
    (k j : ℕ) (x : R) :
    (ascPochhammer R k).eval (x + 1) * (descPochhammer R j).eval x =
      (descPochhammer R (k + j)).eval (x + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast,
      show (k + 1) + j = (k + j) + 1 by omega,
      show x + ((k + 1 : ℕ) : R) = (x + k) + 1 by push_cast; ring,
      descPochhammer_eval_succ_add_one]
    linear_combination (x + k + 1) * ih

/-- A linear functional whose forward differences evaluate to the derivative at zero
has factorial mixed moments `(-1)ʲ k! j! / (k + j + 1)`. -/
lemma apply_ascPochhammer_mul_descPochhammer {K : Type*} [Field K] [CharZero K]
    (L : K[X] →ₗ[K] K) (hL : ∀ Q : K[X], L (Q.comp (X + 1) - Q) = (derivative Q).eval 0)
    (k j : ℕ) :
    L ((ascPochhammer K k).comp (X + 1) * descPochhammer K j) =
      (-1 : K) ^ j * (k ! : K) * (j ! : K) / (k + j + 1) := by
  let P : K[X] := (ascPochhammer K k).comp (X + 1) * descPochhammer K j
  let Q : K[X] := C (1 / (k + j + 1 : K)) * (descPochhammer K (k + j + 1)).comp (X + C (k : K))
  have hk : (k + j + 1 : K) ≠ 0 := by exact_mod_cast (by omega : k + j + 1 ≠ 0)
  have hstep (x : K) : Q.eval (x + 1) - Q.eval x = P.eval x := by
    simp only [Q, P, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one]
    rw [show x + 1 + (k : K) = (x + k) + 1 by ring, ← mul_sub,
      descPochhammer_eval_add_one_sub,
      eval_ascPochhammer_add_one_mul_eval_descPochhammer]
    push_cast
    field_simp [hk]
  have he : P = Q.comp (X + 1) - Q := by
    apply Polynomial.funext
    intro x
    simpa only [eval_sub, eval_comp, eval_add, eval_X, eval_one] using (hstep x).symm
  rw [show (ascPochhammer K k).comp (X + 1) * descPochhammer K j = P from rfl, he, hL]
  simp only [Q, derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
    derivative_add, derivative_X, derivative_C, add_zero, one_mul,
    eval_mul, eval_C, eval_comp, eval_add, eval_X, zero_add]
  rw [eval_derivative_descPochhammer_natCast (by omega : k < k + j + 1),
    show k + j + 1 - k - 1 = j by omega]
  ring

/-- Over every characteristic-zero field, a linear functional has Bernoulli numbers as
its power moments and takes a forward difference to the derivative at zero. -/
lemma exists_linearMap_pow_eq_bernoulli {K : Type*} [Field K] [CharZero K] :
    ∃ L : K[X] →ₗ[K] K,
    (∀ n, L (X ^ n) = (_root_.bernoulli n : K)) ∧
      ∀ Q : K[X], L (Q.comp (X + 1) - Q) = (derivative Q).eval 0 := by
  let L : K[X] →ₗ[K] K := (basisMonomials K).constr K (fun n => (_root_.bernoulli n : K))
  have hX (n : ℕ) : L (X ^ n) = (_root_.bernoulli n : K) := by
    have h := (basisMonomials K).constr_basis K (fun n => (_root_.bernoulli n : K)) n
    simpa only [coe_basisMonomials, monomial_one_right_eq_X_pow, L] using h
  refine ⟨L, hX, ?_⟩
  have hpow (n : ℕ) : L ((X + 1) ^ n) =
      ∑ k ∈ range (n + 1), (n.choose k : K) * (_root_.bernoulli k : K) := by
    have he : (X + 1 : K[X]) ^ n = ∑ k ∈ range (n + 1), (n.choose k) • (X : K[X]) ^ k := by
      rw [add_pow]
      apply sum_congr rfl
      intro k _
      rw [one_pow, mul_one, nsmul_eq_mul]
      ring
    rw [he, map_sum]
    apply sum_congr rfl
    intro k _
    rw [map_nsmul, hX, nsmul_eq_mul]
  have hs (n : ℕ) : (∑ k ∈ range n, (n.choose k : K) * (_root_.bernoulli k : K)) =
      if n = 1 then 1 else 0 := by
    have h := congrArg (fun q : ℚ => (q : K)) (_root_.sum_bernoulli n)
    push_cast at h
    split_ifs at h ⊢ <;> simpa only [Rat.cast_one, Rat.cast_zero] using h
  intro Q
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [add_comp, map_sub, map_add, eval_add] at hP hQ ⊢
    linear_combination hP + hQ
  | monomial n a =>
    rw [monomial_comp, ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, ← smul_eq_C_mul,
      map_sub, map_smul, map_smul, hpow, hX]
    rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul,
      derivative_smul, derivative_X_pow, eval_smul, eval_mul, eval_C, eval_pow, eval_X]
    rw [smul_add, add_sub_cancel_right, hs]
    rcases n with _|n
    · simp
    rcases n with _|n <;> simp

/-- The Bernoulli difference identity implies its polynomial multiplication identity. -/
lemma apply_sum_comp_mul_X_add_natCast {K : Type*} [Field K] [CharZero K]
    (B : K[X] →ₗ[K] K)
    (hB : ∀ Q : K[X], B (Q.comp (X + 1) - Q) = (derivative Q).eval 0)
    (a : ℕ) (P : K[X]) :
    B (∑ j ∈ range a, P.comp (C (a : K) * X + C (j : K))) = (a : K) * B P := by
  obtain ⟨Q, _, _, hQ⟩ := exists_eval_add_one_sub_eval_eq P (le_refl P.natDegree)
  have hdiff : Q.comp (X + 1) - Q = P := by
    apply Polynomial.funext
    intro x
    simpa only [eval_sub, eval_comp, eval_add, eval_X, eval_one] using hQ x
  have hscale : (∑ j ∈ range a, P.comp (C (a : K) * X + C (j : K))) =
      (Q.comp (C (a : K) * X)).comp (X + 1) - Q.comp (C (a : K) * X) := by
    apply Polynomial.funext
    intro x
    simp only [eval_finsetSum, eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_sub,
      eval_one]
    have ht := Finset.sum_range_sub (fun j : ℕ => Q.eval ((a : K) * x + j)) a
    have he : ∀ j ∈ range a, P.eval ((a : K) * x + j) =
        Q.eval ((a : K) * x + (j + 1 : ℕ)) - Q.eval ((a : K) * x + j) := by
      intro j _
      rw [← hQ ((a : K) * x + j)]
      congr 2
      push_cast
      ring
    rw [sum_congr rfl he, ht]
    simp only [Nat.cast_zero, add_zero]
    congr 2
    ring
  rw [hscale, hB, ← hdiff, hB]
  simp only [derivative_comp, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_X, mul_one, eval_mul, eval_comp, eval_C, eval_X, mul_zero]

/-- Translating a Bernoulli moment functional by a natural number sums the
values of the derivative at the intervening integers. -/
lemma apply_comp_X_add_natCast_sub {K : Type*} [Field K] [CharZero K]
    (B : K[X] →ₗ[K] K)
    (hB : ∀ Q : K[X], B (Q.comp (X + 1) - Q) = (derivative Q).eval 0)
    (j : ℕ) (Q : K[X]) :
    B (Q.comp (X + C (j : K))) - B Q = ∑ i ∈ range j, (derivative Q).eval (i : K) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ← ih]
    have hd := hB (Q.comp (X + C (j : K)))
    have hc : (Q.comp (X + C (j : K))).comp (X + 1) = Q.comp (X + C ((j + 1 : ℕ) : K)) := by
      rw [comp_assoc]
      congr 1
      simp only [add_comp, X_comp, C_comp]
      push_cast
      simp only [map_add, map_one]
      ring
    rw [hc, map_sub] at hd
    simp only [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero,
      one_mul, eval_comp, eval_add, eval_X, eval_C, zero_add] at hd
    linear_combination hd

/-- The regularized Bernoulli moments form a linear functional satisfying an
integer averaging identity. -/
lemma exists_linearMap_pow_eq_regularized_bernoulli {K : Type*} [Field K] [CharZero K] (a : ℕ) :
    ∃ L : K[X] →ₗ[K] K,
      (∀ n, L (X ^ n) = (1 - (a : K) ^ (n + 1)) * (_root_.bernoulli (n + 1) : K) / (n + 1)) ∧
      ∀ P : K[X], (∑ j ∈ range a, L (P.comp (X + C (j : K)))) =
        ∑ j ∈ range a, ∑ i ∈ range j, P.eval (i : K) := by
  obtain ⟨B, hBX, hBD⟩ := exists_linearMap_pow_eq_bernoulli (K := K)
  let L : K[X] →ₗ[K] K := (basisMonomials K).constr K fun n =>
    (1 - (a : K) ^ (n + 1)) * (_root_.bernoulli (n + 1) : K) / (n + 1)
  have hLX (n : ℕ) : L (X ^ n) =
      (1 - (a : K) ^ (n + 1)) * (_root_.bernoulli (n + 1) : K) / (n + 1) := by
    have h := (basisMonomials K).constr_basis K (fun n =>
      (1 - (a : K) ^ (n + 1)) * (_root_.bernoulli (n + 1) : K) / (n + 1)) n
    simpa only [coe_basisMonomials, monomial_one_right_eq_X_pow, L] using h
  have hLD (Q : K[X]) : L (derivative Q) = B Q - B (Q.comp (C (a : K) * X)) := by
    induction Q using Polynomial.induction_on' with
    | add P Q hP hQ =>
      simp only [map_add, add_comp] at hP hQ ⊢
      linear_combination hP + hQ
    | monomial n c =>
      rcases n with _ | n
      · simp
      · rw [← C_mul_X_pow_eq_monomial, derivative_mul, derivative_C, zero_mul, zero_add,
          derivative_X_pow, Nat.add_sub_cancel, ← mul_assoc, ← C_mul, ← smul_eq_C_mul,
          map_smul, hLX]
        simp only [smul_eq_mul, mul_comp, C_comp, pow_comp, X_comp, mul_pow]
        rw [← mul_assoc, ← C_pow, ← C_mul, ← smul_eq_C_mul, map_smul, hBX,
          ← smul_eq_C_mul, map_smul, hBX]
        simp only [smul_eq_mul]
        have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
        field_simp
        push_cast
        ring
  refine ⟨L, hLX, fun P => ?_⟩
  obtain ⟨Q, hQ⟩ := Polynomial.exists_derivative_eq P
  have hc (j : ℕ) : P.comp (X + C (j : K)) = derivative (Q.comp (X + C (j : K))) := by
    rw [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul, hQ]
  simp_rw [hc, hLD]
  rw [sum_sub_distrib, ← map_sum, ← map_sum]
  have hcomp : (∑ j ∈ range a, (Q.comp (X + C (j : K))).comp (C (a : K) * X)) =
      ∑ j ∈ range a, Q.comp (C (a : K) * X + C (j : K)) := by
    apply sum_congr rfl
    intro j _
    rw [comp_assoc]
    simp only [add_comp, X_comp, C_comp]
  rw [hcomp, apply_sum_comp_mul_X_add_natCast B hBD, map_sum]
  have ht (j : ℕ) : B (Q.comp (X + C (j : K))) = B Q + ∑ i ∈ range j, P.eval (i : K) := by
    have h := apply_comp_X_add_natCast_sub B hBD j Q
    rw [hQ] at h
    linear_combination h
  simp_rw [ht]
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  ring

end Polynomial
