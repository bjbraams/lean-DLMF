/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Sequence
import DLMFMathlib.Algebra.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Even central factorial polynomials

The polynomial `evenCentralFactorial R k` is `∏_{j < k} (X² - j²)`. Its even-degree
expansion coefficients are central forward differences divided by factorials.
An explicit discrete antiderivative also gives its derivative at the origin.

* `Polynomial.X_pow_two_mul_eq_sum_evenCentralFactorial`: the central-difference expansion.
* `Polynomial.exists_evenCentralFactorial_discreteAntiderivative`: a discrete primitive.
* `Finset.sum_neg_one_pow_mul_choose_mul_sub_pow_even`: fold an even central difference.

These proofs use Mathlib's polynomial-sequence basis, descending Pochhammer polynomials,
and polynomial forward-difference APIs.
-/

public noncomputable section

open Finset
open scoped Nat

namespace Polynomial

/-- The even central factorial `∏_{j < k} (X² - j²)` over a commutative ring. -/
@[expose] def evenCentralFactorial (R : Type*) [CommRing R] (k : ℕ) : R[X] :=
  ∏ j ∈ range k, (X ^ 2 - C ((j : R) ^ 2))

/-- Unfold the product defining the even central factorial. -/
lemma evenCentralFactorial_def (R : Type*) [CommRing R] (k : ℕ) :
    evenCentralFactorial R k = ∏ j ∈ range k, (X ^ 2 - C ((j : R) ^ 2)) := rfl

/-- The zeroth even central factorial is one. -/
@[simp] lemma evenCentralFactorial_zero (R : Type*) [CommRing R] :
    evenCentralFactorial R 0 = 1 := by simp [evenCentralFactorial_def]

/-- The product recurrence for even central factorials. -/
lemma evenCentralFactorial_succ (R : Type*) [CommRing R] (k : ℕ) :
    evenCentralFactorial R (k + 1) = evenCentralFactorial R k * (X ^ 2 - C ((k : R) ^ 2)) := by
  simp only [evenCentralFactorial_def, prod_range_succ]

/-- The even central factorial of index `k` vanishes at `0, …, k - 1`. -/
lemma eval_evenCentralFactorial_natCast_of_lt {R : Type*} [CommRing R] {r k : ℕ}
    (hrk : r < k) : (evenCentralFactorial R k).eval (r : R) = 0 := by
  simp only [evenCentralFactorial_def, eval_prod, eval_sub, eval_pow, eval_X, eval_C]
  exact prod_eq_zero (mem_range.mpr hrk) (sub_self _)

/-- Every even central factorial is invariant under negating its argument. -/
lemma eval_evenCentralFactorial_neg {R : Type*} [CommRing R] (k : ℕ) (x : R) :
    (evenCentralFactorial R k).eval (-x) = (evenCentralFactorial R k).eval x := by
  simp only [evenCentralFactorial_def, eval_prod, eval_sub, eval_pow, eval_X, eval_C, neg_sq]

/-- Every even central factorial is monic over a nontrivial commutative ring. -/
lemma monic_evenCentralFactorial (R : Type*) [CommRing R] [Nontrivial R] (k : ℕ) :
    (evenCentralFactorial R k).Monic := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [evenCentralFactorial_succ]
    exact ih.mul (monic_X_pow_sub_C _ (by decide))

/-- The even central factorial of index `k` has degree `2k`. -/
lemma natDegree_evenCentralFactorial (R : Type*) [CommRing R] [IsDomain R] (k : ℕ) :
    (evenCentralFactorial R k).natDegree = 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [evenCentralFactorial_succ,
      natDegree_mul (monic_evenCentralFactorial R k).ne_zero
        (monic_X_pow_sub_C ((k : R) ^ 2) (by decide : 2 ≠ 0)).ne_zero,
      ih, natDegree_X_pow_sub_C ((k : R) ^ 2)]
    omega

/-- Shift the descending factorial recurrence by one. -/
lemma descPochhammer_eval_succ_add_one {R : Type*} [CommRing R] (m : ℕ) (x : R) :
    (descPochhammer R (m + 1)).eval (x + 1) = (x + 1) * (descPochhammer R m).eval x := by
  rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_X, eval_one]
  simp only [add_sub_cancel_right]

/-- The forward difference of a descending factorial. -/
lemma descPochhammer_eval_add_one_sub {R : Type*} [CommRing R] (m : ℕ) (x : R) :
    (descPochhammer R (m + 1)).eval (x + 1) - (descPochhammer R (m + 1)).eval x =
      (m + 1 : R) * (descPochhammer R m).eval x := by
  rw [descPochhammer_eval_succ_add_one, descPochhammer_succ_eval]
  ring

/-- An even central factorial is a centered descending factorial times its variable. -/
lemma eval_evenCentralFactorial_succ_eq_mul_descPochhammer {R : Type*} [CommRing R]
    (k : ℕ) (x : R) :
    (evenCentralFactorial R (k + 1)).eval x =
      x * (descPochhammer R (2 * k + 1)).eval (x + k) := by
  induction k with
  | zero => simp [evenCentralFactorial_succ, pow_two]
  | succ k ih =>
    rw [evenCentralFactorial_succ, eval_mul, eval_sub, eval_pow, eval_X, eval_C, ih,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega,
      show x + ((k + 1 : ℕ) : R) = (x + k) + 1 by push_cast; ring,
      descPochhammer_eval_succ_add_one]
    rw [descPochhammer_succ_eval (2 * k + 1)]
    push_cast
    ring

/-- A descending factorial at minus one is a signed factorial. -/
lemma descPochhammer_eval_neg_one {R : Type*} [CommRing R] (m : ℕ) :
    (descPochhammer R m).eval (-1) = (-1) ^ m * (m ! : R) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ, pow_succ]
    push_cast
    ring

/-- The derivative of a descending factorial at one of its simple integer roots. -/
lemma eval_derivative_descPochhammer_natCast {R : Type*} [CommRing R] {m r : ℕ}
    (hrm : r < m) :
    (derivative (descPochhammer R m)).eval (r : R) =
      (-1) ^ (m - r - 1) * (r ! : R) * ((m - r - 1)! : R) := by
  induction m generalizing r with
  | zero => omega
  | succ m ih =>
    rw [descPochhammer_succ_left, derivative_mul, derivative_X, one_mul,
      derivative_comp, derivative_sub, derivative_X, derivative_one, sub_zero, one_mul,
      eval_add, eval_mul, eval_comp, eval_sub, eval_X, eval_one]
    cases r with
    | zero =>
      simp only [Nat.cast_zero, zero_sub, zero_mul, add_zero, Nat.sub_zero,
        Nat.add_sub_cancel, Nat.factorial_zero, Nat.cast_one, mul_one]
      exact descPochhammer_eval_neg_one (R := R) m
    | succ r =>
      have hrm' : r < m := by omega
      rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        descPochhammer_eval_natCast_of_lt hrm', zero_add,
        eval_comp, eval_sub, eval_X, eval_one, add_sub_cancel_right, ih hrm', Nat.factorial_succ]
      push_cast
      ring

/-- Every even monomial is a finite linear combination of even central factorials. -/
lemma exists_sum_C_mul_evenCentralFactorial {K : Type*} [CommRing K] [IsDomain K] (n : ℕ) :
    ∃ c : ℕ →₀ K, (X : K[X]) ^ (2 * n) =
      ∑ k ∈ c.support, C (c k) * evenCentralFactorial K k := by
  let A : ℕ → K[X] := fun k => ∏ j ∈ range k, (X - C ((j : K) ^ 2))
  have hA : ∀ k, (A k).Monic ∧ (A k).natDegree = k := by
    intro k
    induction k with
    | zero => simp [A]
    | succ k ih =>
      dsimp only [A] at ih ⊢
      rw [prod_range_succ]
      refine ⟨ih.1.mul (monic_X_sub_C _), ?_⟩
      rw [natDegree_mul ih.1.ne_zero (monic_X_sub_C _).ne_zero, ih.2, natDegree_X_sub_C]
  let S : Sequence K := ⟨A, fun k => by
    rw [degree_eq_natDegree (hA k).1.ne_zero, (hA k).2]⟩
  let b := S.basis (fun k => by
    rw [show (S k).leadingCoeff = 1 from (hA k).1.leadingCoeff]
    exact isUnit_one)
  let c := b.repr ((X : K[X]) ^ n)
  refine ⟨c, ?_⟩
  have hp : ∑ k ∈ c.support, C (c k) * A k = (X : K[X]) ^ n := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, c, b, Sequence.basis_eq_self,
      S, smul_eq_C_mul] using
      b.linearCombination_repr ((X : K[X]) ^ n)
  have hcomp := congrArg (fun P : K[X] => P.comp (X ^ 2)) hp
  simp only [sum_comp, mul_comp, C_comp, A, prod_comp, sub_comp, X_comp,
    pow_comp, ← pow_mul] at hcomp
  simpa only [Nat.mul_comm, evenCentralFactorial_def] using hcomp.symm

/-- An even central factorial has a discrete primitive with an explicit derivative at zero. -/
lemma exists_evenCentralFactorial_discreteAntiderivative {K : Type*} [Field K] [CharZero K]
    (k : ℕ) : ∃ Q : K[X],
      (∀ x : K, Q.eval (x + 1) - Q.eval x = (evenCentralFactorial K (k + 1)).eval x) ∧
      (derivative Q).eval 0 =
        (-1) ^ (k + 2) * (k ! : K) * ((k + 1)! : K) / (2 * (2 * k + 3)) := by
  let H : K[X] := (descPochhammer K (2 * k + 2)).comp (X + C (k : K))
  let Q : K[X] := C (1 / (2 * (k : K) + 3)) *
    (descPochhammer K (2 * k + 3)).comp (X + C (k : K)) + C (1 / 2 : K) * H
  refine ⟨Q, ?_, ?_⟩
  · intro x
    simp only [Q, H, eval_add, eval_mul, eval_C, eval_comp, eval_X]
    have h1 := descPochhammer_eval_add_one_sub (2 * k + 2) (x + (k : K))
    have h2 := descPochhammer_eval_add_one_sub (2 * k + 1) (x + (k : K))
    have hk1 : (2 * (k : K) + 3) ≠ 0 := by exact_mod_cast (by omega : 2 * k + 3 ≠ 0)
    calc
      _ = (1 / (2 * (k : K) + 3)) *
          ((descPochhammer K (2 * k + 3)).eval ((x + k) + 1) -
            (descPochhammer K (2 * k + 3)).eval (x + k)) +
          (1 / 2) * ((descPochhammer K (2 * k + 2)).eval ((x + k) + 1) -
            (descPochhammer K (2 * k + 2)).eval (x + k)) := by
        rw [show x + 1 + (k : K) = (x + k) + 1 by ring]
        ring
      _ = (1 / (2 * (k : K) + 3)) * (2 * k + 3) *
          (descPochhammer K (2 * k + 2)).eval (x + k) +
          (1 / 2) * (2 * k + 2) * (descPochhammer K (2 * k + 1)).eval (x + k) := by
        convert congrArg₂ (fun u v : K => 1 / (2 * (k : K) + 3) * u + (1 / 2) * v) h1 h2 using 1
        push_cast
        ring
      _ = (evenCentralFactorial K (k + 1)).eval x := by
        rw [eval_evenCentralFactorial_succ_eq_mul_descPochhammer,
          show 2 * k + 2 = (2 * k + 1) + 1 by omega, descPochhammer_succ_eval]
        push_cast
        field_simp [hk1]
        ring
  · simp only [Q, H, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul,
      eval_add, eval_mul, eval_C, eval_comp, eval_add, eval_X, zero_add]
    rw [eval_derivative_descPochhammer_natCast (by omega : k < 2 * k + 3),
      eval_derivative_descPochhammer_natCast (by omega : k < 2 * k + 2),
      show 2 * k + 3 - k - 1 = k + 2 by omega,
      show 2 * k + 2 - k - 1 = k + 1 by omega,
      show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ, pow_succ]
    push_cast
    have hk : (2 * (k : K) + 3) ≠ 0 := by exact_mod_cast (by omega : 2 * k + 3 ≠ 0)
    field_simp [hk]
    ring

/-- Central forward differences are diagonal on the even central factorial basis. -/
lemma fwdDiff_iter_evenCentralFactorial {K : Type*} [CommRing K] [IsDomain K] (k m : ℕ) :
    (fwdDiff 1)^[2 * k] (evenCentralFactorial K m).eval (-(k : K)) =
      if m = k then ((2 * k)! : K) else 0 := by
  rcases lt_trichotomy m k with hmk | hmk | hkm
  · rw [fwdDiff_iter_eq_zero_of_degree_lt (by
      rw [natDegree_evenCentralFactorial (R := K)]
      omega)]
    simp [ne_of_lt hmk]
  · subst m
    have h := congrFun (evenCentralFactorial K k).fwdDiff_iter_degree_eq_factorial (-(k : K))
    rw [natDegree_evenCentralFactorial, (monic_evenCentralFactorial K k).leadingCoeff] at h
    simpa only [Pi.smul_apply, Pi.natCast_apply, one_smul, ↓reduceIte] using h
  · rw [fwdDiff_iter_eq_sum_shift]
    simp only [nsmul_eq_mul, mul_one]
    rw [ite_eq_right (ne_of_gt hkm)]
    refine sum_eq_zero fun i hi => ?_
    have hik : i ≤ 2 * k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hz : (evenCentralFactorial K m).eval (-(k : K) + i) = 0 := by
      by_cases hik' : i ≤ k
      · rw [show -(k : K) + i = -((k - i : ℕ) : K) by rw [Nat.cast_sub hik']; ring,
          eval_evenCentralFactorial_neg]
        exact eval_evenCentralFactorial_natCast_of_lt (by omega : k - i < m)
      · rw [show -(k : K) + i = ((i - k : ℕ) : K) by rw [Nat.cast_sub (by omega)]; ring]
        exact eval_evenCentralFactorial_natCast_of_lt (by omega : i - k < m)
    rw [hz, smul_zero]

/-- Expand an even monomial in even central factorials using central forward differences. -/
lemma X_pow_two_mul_eq_sum_evenCentralFactorial {K : Type*} [Field K] [CharZero K]
    (n : ℕ) : (X : K[X]) ^ (2 * n) =
      ∑ k ∈ range (n + 1), C (((fwdDiff 1)^[2 * k] (fun x : K => x ^ (2 * n))
        (-(k : K))) / ((2 * k)! : K)) * evenCentralFactorial K k := by
  obtain ⟨c, hc⟩ := exists_sum_C_mul_evenCentralFactorial (K := K) n
  have hcoef (k : ℕ) : (fwdDiff 1)^[2 * k] (fun x : K => x ^ (2 * n)) (-(k : K)) =
      c k * ((2 * k)! : K) := by
    have he : (fun x : K => x ^ (2 * n)) =
        ∑ j ∈ c.support, c j • (evenCentralFactorial K j).eval := by
      funext x
      rw [Finset.sum_apply]
      have h := congrArg (Polynomial.eval x) hc
      simpa only [eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, sum_apply,
        Pi.smul_apply, smul_eq_mul] using h
    rw [he, fwdDiff_iter_finsetSum, Finset.sum_apply]
    simp only [fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul,
      fwdDiff_iter_evenCentralFactorial]
    rw [sum_eq_single k]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hk
      simp [Finsupp.notMem_support_iff.mp hk]
  have hzero {k : ℕ} (hnk : n < k) : c k = 0 := by
    have h := hcoef k
    rw [fwdDiff_iter_pow_eq_zero_of_lt (by omega), Pi.zero_apply] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [hc]
  have hsub : ∑ k ∈ c.support, C (c k) * evenCentralFactorial K k =
      ∑ k ∈ range (n + 1), C (c k) * evenCentralFactorial K k := by
    apply sum_subset
    · intro k hk
      have hck : c k ≠ 0 := Finsupp.mem_support_iff.mp hk
      exact mem_range.mpr (by by_contra h; exact hck (hzero (by omega)))
    · intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk, map_zero, zero_mul]
  rw [hsub]
  apply sum_congr rfl
  intro k _
  rw [hcoef, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]

end Polynomial

namespace Finset

/-- Fold the central difference of an even positive power into its positive arguments. -/
lemma sum_neg_one_pow_mul_choose_mul_sub_pow_even {R : Type*} [CommRing R] (n k : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range (2 * k + 1), (-1 : R) ^ (2 * k - i) * ((2 * k).choose i : R) *
      ((i : R) - k) ^ (2 * n) = 2 * (-1) ^ k * ∑ j ∈ Icc 1 k, (-1 : R) ^ j *
        ((2 * k).choose (k - j) : R) * (j : R) ^ (2 * n) := by
  rw [show 2 * k + 1 = k + (k + 1) by ring, sum_range_add, sum_range_succ', ← sum_range_reflect,
    sum_Icc_one_eq_sum_range_add_one, mul_sum]
  simp only [Nat.cast_add, add_zero, sub_self, zero_pow (show 2 * n ≠ 0 by omega), mul_zero,
    add_zero]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < k := mem_range.mp hj
  rw [show 2 * k - (k - 1 - j) = (k - j - 1) + 2 * (j + 1) by omega,
    show 2 * k - (k + (j + 1)) = k - j - 1 by omega,
    show (2 * k).choose (k + (j + 1)) = (2 * k).choose (k - 1 - j) by
      rw [← Nat.choose_symm (show k - 1 - j ≤ 2 * k by omega)]; congr 1; omega,
    show k - (j + 1) = k - 1 - j by omega]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  rw [pow_add, pow_mul]
  have e1 : ((k : R) - 1 - j - k) ^ (2 * n) = ((j : R) + 1) ^ (2 * n) := by
    rw [show (k : R) - 1 - j - k = -((j : R) + 1) by ring, neg_pow, pow_mul]; norm_num
  have e2 : ((k : R) + (j + 1) - k) = (j : R) + 1 := by ring
  rw [e1, e2]
  have e3 : (-1 : R) ^ k = (-1) ^ (k - j - 1) * (-1) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e3]
  have e4 : (-1 : R) ^ (j * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  ring_nf
  rw [e4]
  ring

end Finset
