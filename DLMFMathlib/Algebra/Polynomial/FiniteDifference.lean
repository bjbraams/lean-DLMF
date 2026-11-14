/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Discrete antiderivatives and polynomial extrapolation

* `Polynomial.exists_eval_add_one_sub_eval_eq` constructs a discrete antiderivative over a
  characteristic-zero field, with a degree bound and prescribed value at zero.
* `Polynomial.eval_natCast_eq_sum_choose_mul_eval` extrapolates a polynomial from consecutive
  integer arguments using binomial coefficients over any commutative ring.

* `Polynomial.eval_natCast_eq_sum_neg_natCast` gives a symmetric version using negative
  arguments and zeros at consecutive positive arguments.

The proofs use Mathlib's Bernoulli polynomial difference equation, Gregory–Newton formula,
and alternating partial binomial sum `Int.alternating_sum_range_choose_eq_choose`.
-/

public section

open Finset

namespace Polynomial

/-- The `n`-th Bernoulli polynomial has degree at most `n`. -/
lemma natDegree_bernoulli_le (n : ℕ) : (bernoulli n).natDegree ≤ n := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [coeff_bernoulli, ite_eq_right (by omega)]

/-- Every polynomial over a characteristic-zero field has a discrete antiderivative that
vanishes at zero and whose degree is at most one greater. -/
theorem exists_eval_add_one_sub_eval_eq {K : Type*} [Field K] [CharZero K]
    (P : K[X]) {d : ℕ} (hP : P.natDegree ≤ d) :
    ∃ Q : K[X], Q.eval 0 = 0 ∧ Q.natDegree ≤ d + 1 ∧
      ∀ x : K, Q.eval (x + 1) - Q.eval x = P.eval x := by
  let B : ℕ → K[X] := fun i => (bernoulli (i + 1)).map (algebraMap ℚ K)
  let Q : K[X] := ∑ i ∈ range (d + 1), C (P.coeff i / (i + 1 : K)) * (B i - C ((B i).eval 0))
  refine ⟨Q, ?_, ?_, ?_⟩
  · simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_sub, sub_self, mul_zero,
      sum_const_zero]
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (natDegree_C_mul_le _ _).trans ?_
    have hib : (B i).natDegree ≤ i + 1 :=
      natDegree_map_le.trans (natDegree_bernoulli_le (i + 1))
    have hid : i ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
    exact (natDegree_sub_le _ _).trans (max_le (by omega) (by simp))
  · intro x
    have hB : ∀ i : ℕ, (B i).eval (x + 1) - (B i).eval x = (i + 1 : K) * x ^ i := by
      intro i
      have hb := congrArg (Polynomial.map (algebraMap ℚ K))
        (bernoulli_comp_one_add_X (i + 1))
      simp only [nsmul_eq_mul, Nat.add_sub_cancel] at hb
      have he := congrArg (Polynomial.eval x) hb
      simp only [Polynomial.map_comp, Polynomial.map_add,
        Polynomial.map_one, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_natCast,
        Polynomial.map_pow, eval_add, eval_comp, eval_one, eval_X, eval_mul,
        eval_natCast, eval_pow, Nat.cast_add, Nat.cast_one] at he
      dsimp only [B]
      rw [add_comm x]
      linear_combination he
    simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_sub, ← sum_sub_distrib]
    have ht : ∀ i ∈ range (d + 1), P.coeff i / (i + 1 : K) *
        ((B i).eval (x + 1) - (B i).eval 0) -
        P.coeff i / (i + 1 : K) * ((B i).eval x - (B i).eval 0) = P.coeff i * x ^ i := by
      intro i _
      rw [show P.coeff i / (i + 1 : K) * ((B i).eval (x + 1) - (B i).eval 0) -
          P.coeff i / (i + 1 : K) * ((B i).eval x - (B i).eval 0) =
          P.coeff i / (i + 1 : K) * ((B i).eval (x + 1) - (B i).eval x) by ring, hB]
      have hi : (i : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero i
      field_simp
    rw [sum_congr rfl ht]
    rw [eval_eq_sum_range]
    symm
    refine sum_subset (range_subset_range.mpr (by omega)) fun i hi hi' => ?_
    have hdi : P.natDegree < i := by simp only [mem_range] at hi hi'; omega
    rw [coeff_eq_zero_of_natDegree_lt hdi, zero_mul]

/-- Polynomial extrapolation from the values at `0, …, m`, expressed through binomial
coefficients, at any natural point strictly greater than `m`. -/
theorem eval_natCast_eq_sum_choose_mul_eval {R : Type*} [CommRing R] (P : R[X])
    {m x : ℕ} (hP : P.natDegree ≤ m) (hmx : m < x) :
    P.eval (x : R) = ∑ i ∈ range (m + 1), (-1 : R) ^ (m - i) * (x.choose i : R) *
      ((x - i - 1).choose (m - i) : R) * P.eval (i : R) := by
  have hn := shift_eq_sum_fwdDiff_iter (1 : R) (fun y => P.eval y) x 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at hn
  have ht : ∑ k ∈ range (m + 1), (x.choose k : R) *
      (fwdDiff 1)^[k] (fun y => P.eval y) 0 =
      ∑ k ∈ range (x + 1), (x.choose k : R) *
        (fwdDiff 1)^[k] (fun y => P.eval y) 0 := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k _ hk
    have hmk : m < k := by simp only [mem_range] at hk; omega
    rw [fwdDiff_iter_eq_zero_of_degree_lt (hP.trans_lt hmk)]
    simp
  rw [← ht] at hn
  rw [hn]
  simp_rw [fwdDiff_iter_eq_sum_shift, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, mul_sum]
  rw [sum_comm' (t' := range (m + 1)) (s' := fun i => Icc i m)
    (fun k i => by simp only [mem_range, mem_Icc]; omega)]
  refine sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hterm : ∀ k ∈ Icc i m,
      (x.choose k : R) * ((-1 : R) ^ (k - i) * (k.choose i : R) * P.eval (i : R)) =
      ((-1 : R) ^ (k - i) * ((x - i).choose (k - i) : R)) *
        ((x.choose i : R) * P.eval (i : R)) := by
    intro k hk
    have hik : i ≤ k := (mem_Icc.mp hk).1
    have hc : (x.choose k : R) * (k.choose i : R) =
        (x.choose i : R) * ((x - i).choose (k - i) : R) := by
      simpa only [Nat.cast_mul] using
        congrArg (Nat.cast : ℕ → R) (Nat.choose_mul (n := x) hik)
    calc (x.choose k : R) * ((-1 : R) ^ (k - i) * (k.choose i : R) * P.eval (i : R))
        = (-1) ^ (k - i) * ((x.choose k : R) * (k.choose i : R)) * P.eval (i : R) := by ring
      _ = _ := by rw [hc]; ring
  rw [sum_congr rfl hterm, ← sum_mul,
    show Icc i m = Ico i (m + 1) by ext k; simp only [mem_Icc, mem_Ico]; omega,
    sum_Ico_eq_sum_range,
    show m + 1 - i = (m - i) + 1 by omega]
  simp only [Nat.add_sub_cancel_left]
  have hs : ∑ k ∈ range (m - i + 1), (-1 : R) ^ k * ((x - i).choose k : R) =
      (-1) ^ (m - i) * ((x - i - 1).choose (m - i) : R) := by
    have h := Int.alternating_sum_range_choose_eq_choose (n := x - i - 1) (m := m - i)
    rw [show x - i - 1 + 1 = x - i by omega] at h
    have hR := congrArg (Int.cast : ℤ → R) h
    push_cast at hR
    exact hR
  rw [hs]
  ring

/-- A polynomial of degree at most `2k` that vanishes at `1, …, k` is determined by
its values at `0, -1, …, -k`; this formula evaluates it at any natural argument greater
than `k`. -/
lemma eval_natCast_eq_sum_neg_natCast {R : Type*} [CommRing R] (P : R[X])
    {k n : ℕ} (hP : P.natDegree ≤ 2 * k) (hkn : k < n)
    (hzero : ∀ i ∈ Icc 1 k, P.eval (i : R) = 0) :
    P.eval (n : R) = ∑ j ∈ range (k + 1), (-1 : R) ^ (k + j) *
      ((n + k).choose (k - j) : R) * ((n - 1 + j).choose (k + j) : R) *
        P.eval (-(j : R)) := by
  let Q : R[X] := P.comp (X - C (k : R))
  have hQ : Q.natDegree ≤ 2 * k := by
    have hlinear : (X - C (k : R)).natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (max_le natDegree_X_le (by simp))
    calc Q.natDegree ≤ P.natDegree * (X - C (k : R)).natDegree := natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hlinear
      _ ≤ 2 * k := by simpa only [mul_one] using hP
  have ht := eval_natCast_eq_sum_choose_mul_eval Q hQ (by omega : 2 * k < n + k)
  simp only [Q, eval_comp, eval_sub, eval_X, eval_C] at ht
  have harg : ((n + k : ℕ) : R) - k = n := by push_cast; ring
  rw [harg, show 2 * k + 1 = (k + 1) + k by omega, sum_range_add] at ht
  have hz : ∑ i ∈ range k, (-1 : R) ^ (2 * k - (k + 1 + i)) *
      ((n + k).choose (k + 1 + i) : R) *
      ((n + k - (k + 1 + i) - 1).choose (2 * k - (k + 1 + i)) : R) *
      P.eval (((k + 1 + i : ℕ) : R) - k) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have harg' : ((k + 1 + i : ℕ) : R) - k = (i + 1 : ℕ) := by push_cast; ring
    rw [harg', hzero (i + 1) (by simp only [mem_Icc, mem_range] at hi ⊢; omega), mul_zero]
  rw [hz, add_zero] at ht
  rw [ht, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show k + 1 - 1 - j = k - j by omega,
    show 2 * k - (k - j) = k + j by omega,
    show n + k - (k - j) - 1 = n - 1 + j by omega]
  have harg' : ((k - j : ℕ) : R) - k = -(j : R) := by
    rw [Nat.cast_sub hjk]; ring
  rw [harg']

end Polynomial
