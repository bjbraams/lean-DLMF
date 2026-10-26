/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Properties
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Bernoulli and Euler numbers and polynomials: explicit formulas (DLMF §24.6)

DLMF §24.6.p1: the identities hold for `n = 1, 2, …`; 24.6.7, 24.6.8, 24.6.10 and 24.6.12 also
for `n = 0`. Each statement below carries exactly that range (24.6.9 is stated for all `n`,
which is stronger than DLMF: with Lean's `0⁰ = 1` it also holds for `n = 0`). All formulas were
checked in exact rational arithmetic for `n ≤ 11`; the small cases excluded by DLMF fail.
Powers `jⁿ` with `j = 0` use `0⁰ = 1`, as the printed sums require.
-/

@[expose] public section

noncomputable section

open Polynomial (aeval X C)
open Finset
open scoped Nat Polynomial

namespace DLMF.BernoulliEuler

/-! ### Helpers: finite differences and Newton series -/

/-- The `N`-th finite difference of a polynomial of degree `< N` vanishes:
`∑_{k=0}^{N} (-1)ᵏ (N choose k) P(k) = 0`. -/

theorem q24a_alt_sum_poly_eq_zero (c : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (N + 1), (-1 : ℂ) ^ k * (N.choose k : ℂ) *
      ∑ i ∈ range N, c i * (k : ℂ) ^ i = 0 := by
  have h := congrFun (fwdDiff_iter_sum_mul_pow_eq_zero (R := ℂ) (n := N) c) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one] at h
  have : ∑ k ∈ range (N + 1), (-1 : ℂ) ^ k * (N.choose k : ℂ) * ∑ i ∈ range N, c i * (k : ℂ) ^ i =
      (-1) ^ N * ∑ k ∈ range (N + 1), (((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) •
        ∑ i ∈ range N, c i * (k : ℂ) ^ i) := by
    rw [mul_sum]; refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [zsmul_eq_mul]; push_cast
    rw [← mul_assoc, ← mul_assoc, ← pow_add, show N + (N - k) = k + 2 * (N - k) by omega, pow_add,
      pow_mul]
    norm_num
  rw [this, h, mul_zero]
/-- Variant for a function given by a polynomial of degree `< N` at the integers. -/

theorem q24a_alt_sum_eq_zero_of_poly (f : ℕ → ℂ) (c : ℕ → ℂ) (N : ℕ)
    (hf : ∀ k, f k = ∑ i ∈ range N, c i * (k : ℂ) ^ i) :
    ∑ k ∈ range (N + 1), (-1 : ℂ) ^ k * (N.choose k : ℂ) * f k = 0 := by
  simp only [hf]; exact q24a_alt_sum_poly_eq_zero c N
/-- `∑_{j=0}^{k} (-1)ʲ (k choose j) (x + j)ᵐ = 0` for `m < k`. -/

theorem q24a_alt_sum_pow_eq_zero (x : ℂ) {m k : ℕ} (hmk : m < k) :
    ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * (x + j) ^ m = 0 := by
  refine q24a_alt_sum_eq_zero_of_poly _
    (fun i => if i ≤ m then (m.choose i : ℂ) * x ^ (m - i) else 0) k
    fun j => ?_
  rw [add_comm, add_pow]
  rw [← sum_range_add_sum_Ico _ (show m + 1 ≤ k by omega)]
  rw [sum_eq_zero (s := Ico (m + 1) k) (fun i hi => by
    have := (mem_Ico.mp hi).1; simp [show ¬ i ≤ m by omega]), add_zero]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  simp only [hi', ↓reduceIte]; ring
/-- Alternating binomial sums as iterated forward differences. -/

theorem q24a_alt_sum_eq_fwdDiff (f : ℂ → ℂ) (k : ℕ) (x : ℂ) :
    ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * f (x + j) =
      (-1) ^ k * (fwdDiff 1)^[k] f x := by
  rw [fwdDiff_iter_eq_sum_shift, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]; push_cast
  rw [← mul_assoc, ← mul_assoc, ← pow_add, show k + (k - j) = j + 2 * (k - j) by omega, pow_add,
    pow_mul]
  norm_num
/-- `Δᵏf(x+1) = Δᵏ⁺¹f(x) + Δᵏf(x)`. -/

theorem q24a_fwdDiff_iter_add_one (f : ℂ → ℂ) (k : ℕ) (x : ℂ) :
    (fwdDiff 1)^[k] f (x + 1) = (fwdDiff 1)^[k + 1] f x + (fwdDiff 1)^[k] f x := by
  rw [Function.iterate_succ_apply', fwdDiff]; ring

/-- The alternating sums `c(k, m) = ∑_{j=0}^{k} (-1)ʲ (k choose j) jᵐ` (`= (-1)ᵏ k! S(m, k)`). -/
noncomputable def q24a_c (k m : ℕ) : ℂ :=
  ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * (j : ℂ) ^ m

/-- `c(k, m) = 0` for `m < k`. -/

theorem q24a_c_eq_zero {k m : ℕ} (h : m < k) : q24a_c k m = 0 := by
  have := q24a_alt_sum_pow_eq_zero 0 h
  simpa [q24a_c] using this

/-- Extending a binomial-weighted sum beyond `k`. -/

theorem q24a_sum_choose_extend (a : ℕ → ℂ) {k M : ℕ} (h : k + 1 ≤ M) :
    ∑ j ∈ range (k + 1), (k.choose j : ℂ) * a j = ∑ j ∈ range M, (k.choose j : ℂ) * a j := by
  refine sum_subset (range_subset_range.mpr h) fun j _ hj => ?_
  rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]; simp

/-- Hockey stick: `∑_{k<N} (k choose j) = (N choose j+1)`. -/

theorem q24a_sum_range_choose (N j : ℕ) :
    ∑ k ∈ range N, (k.choose j : ℂ) = (N.choose (j + 1) : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Nat.choose_succ_succ]; push_cast; ring

/-- Pascal recursion for `c`: `∑_j (-1)ʲ (k choose j)(j+1)ᴺ = c(k, N) - c(k+1, N)`. -/

theorem q24a_c_shift (k N : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * ((j : ℂ) + 1) ^ N =
      q24a_c k N - q24a_c (k + 1) N := by
  have h1 := q24a_alt_sum_eq_fwdDiff (fun y => y ^ N) k (0 + 1)
  have h2 := q24a_alt_sum_eq_fwdDiff (fun y => y ^ N) k 0
  have h3 := q24a_alt_sum_eq_fwdDiff (fun y => y ^ N) (k + 1) 0
  rw [q24a_fwdDiff_iter_add_one] at h1
  simp only [zero_add] at h1 h2 h3
  simp only [q24a_c]
  rw [show ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * ((j : ℂ) + 1) ^ N =
    ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * (1 + (j : ℂ)) ^ N by
      simp only [add_comm (1 : ℂ)], h1, h2, h3, pow_succ]
  ring

/-- Newton's `log(1 + Δ) = D` at `0`: `∑_{k=1}^{N} c(k, N)/k = -[N = 1]` for `N ≥ 1`. -/

theorem q24a_sum_c_div (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ range N, q24a_c (k + 1) N / (k + 1) = if N = 1 then -1 else 0 := by
  have hext : ∀ k ∈ range N, q24a_c (k + 1) N / (k + 1) =
      ∑ j ∈ range (N + 1), (-1 : ℂ) ^ j * (j : ℂ) ^ N * ((k + 1).choose j / (k + 1)) := by
    intro k hk
    have hk' := mem_range.mp hk
    rw [q24a_c, sum_div]
    have := q24a_sum_choose_extend (k := k + 1) (M := N + 1)
      (fun j => (-1 : ℂ) ^ j * (j : ℂ) ^ N / ((k : ℂ) + 1)) (by omega)
    rw [show ∑ j ∈ range (k + 1 + 1), (-1 : ℂ) ^ j * ((k + 1).choose j : ℂ) * (j : ℂ) ^ N /
        ((k : ℂ) + 1) = ∑ j ∈ range (k + 1 + 1), ((k + 1).choose j : ℂ) *
        ((-1 : ℂ) ^ j * (j : ℂ) ^ N / ((k : ℂ) + 1)) from sum_congr rfl fun j _ => by ring, this]
    exact sum_congr rfl fun j _ => by ring
  rw [sum_congr rfl hext, sum_comm, sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (show N ≠ 0 by omega), mul_zero, zero_mul, sum_const_zero,
    add_zero]
  have hj : ∀ i ∈ range N, ∑ k ∈ range N, (-1 : ℂ) ^ (i + 1) * (((i + 1 : ℕ) : ℂ)) ^ N *
      (((k + 1).choose (i + 1) : ℂ) / ((k : ℂ) + 1)) =
      (-1 : ℂ) ^ (i + 1) * (N.choose (i + 1) : ℂ) * (((i + 1 : ℕ) : ℂ)) ^ (N - 1) := by
    intro i _
    have hc : ∀ k ∈ range N, ((k + 1).choose (i + 1) : ℂ) / ((k : ℂ) + 1) =
        (k.choose i : ℂ) / ((i : ℂ) + 1) := by
      intro k _
      have := congrArg (Nat.cast : ℕ → ℂ) (Nat.add_one_mul_choose_eq k i)
      push_cast at this
      have hk1 : (k : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
      have hi1 : (i : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero i
      field_simp
      linear_combination (-1 : ℂ) * this
    rw [← mul_sum, sum_congr rfl hc, ← sum_div, q24a_sum_range_choose]
    have hi1 : ((i + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [show N = N - 1 + 1 by omega, pow_succ]
    rw [show N - 1 + 1 - 1 = N - 1 by omega]
    push_cast at hi1 ⊢
    field_simp
    ring
  rw [sum_congr rfl hj]
  -- this is `c(N, N-1)` minus its `j = 0` term
  have h0 := q24a_c_eq_zero (k := N) (m := N - 1) (by omega)
  rw [q24a_c, sum_range_succ'] at h0
  simp only [Nat.cast_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at h0
  rcases Nat.lt_or_ge 1 N with h | h
  · simp only [show N ≠ 1 by omega, ↓reduceIte]
    rw [zero_pow (by omega), add_zero] at h0
    rw [← h0]
  · obtain rfl : N = 1 := by omega
    simp

/-- `∑_{m<N} (N choose m) c(k, m) = -c(k+1, N)`. -/

theorem q24a_sum_choose_c (k N : ℕ) :
    ∑ m ∈ range N, (N.choose m : ℂ) * q24a_c k m = -q24a_c (k + 1) N := by
  rw [show -q24a_c (k + 1) N = (q24a_c k N - q24a_c (k + 1) N) - q24a_c k N by ring,
    ← q24a_c_shift]
  conv_lhs => simp only [q24a_c, mul_sum]
  rw [sum_comm, q24a_c, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := add_pow (j : ℂ) 1 N
  rw [sum_range_succ] at h
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one] at h
  rw [h, mul_add, add_sub_cancel_right, mul_sum]
  exact sum_congr rfl fun m _ => by ring

/-- The Newton-series values `β_m = ∑_{k ≤ m} c(k, m)/(k+1)`. -/
noncomputable def q24a_beta (m : ℕ) : ℂ := ∑ k ∈ range (m + 1), q24a_c k m / (k + 1)

/-- The range of `β_m` may be extended. -/

theorem q24a_beta_extend {m M : ℕ} (h : m + 1 ≤ M) :
    q24a_beta m = ∑ k ∈ range M, q24a_c k m / (k + 1) := by
  refine sum_subset (range_subset_range.mpr h) fun k _ hk => ?_
  rw [q24a_c_eq_zero (by simpa using hk), zero_div]

/-- `β` satisfies the Bernoulli recurrence `∑_{m<N} (N choose m) β_m = [N = 1]`. -/

theorem q24a_sum_choose_beta (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ range N, (N.choose m : ℂ) * q24a_beta m = if N = 1 then 1 else 0 := by
  rw [sum_congr rfl fun m hm => by rw [q24a_beta_extend (M := N) (by simpa using hm)]]
  simp only [mul_sum]
  rw [sum_comm]
  have : ∀ k ∈ range N, ∑ m ∈ range N, (N.choose m : ℂ) * (q24a_c k m / (k + 1)) =
      -(q24a_c (k + 1) N / (k + 1)) := by
    intro k _
    rw [← neg_div, ← q24a_sum_choose_c, sum_div]
    exact sum_congr rfl fun m _ => by ring
  rw [sum_congr rfl this, sum_neg_distrib, q24a_sum_c_div N hN]
  split_ifs <;> simp

/-- `β_n = Bₙ`. -/

theorem q24a_beta_eq (n : ℕ) : q24a_beta n = bernoulli n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1 := q24a_sum_choose_beta (n + 1) (by omega)
    have h2 := sum_bernoulli (n + 1)
    have h2' : ∑ k ∈ range (n + 1), ((n + 1).choose k : ℂ) * (bernoulli k : ℂ) =
        if n + 1 = 1 then 1 else 0 := by
      have := congrArg (Rat.cast : ℚ → ℂ) h2; push_cast at this; rw [this]
      by_cases h : n = 0 <;> simp [h]
    rw [sum_range_succ, Nat.choose_succ_self_right] at h1 h2'
    have : ∑ x ∈ range n, ((n + 1).choose x : ℂ) * q24a_beta x =
        ∑ x ∈ range n, ((n + 1).choose x : ℂ) * (bernoulli x : ℂ) :=
      sum_congr rfl fun m hm => by rw [ih m (mem_range.mp hm)]
    rw [this] at h1
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_left_cancel₀ hn (by linear_combination h1 - h2')

/-- `∑_{k=0}^{n+1} (-1)ᵏ (n+1 choose k) Eₙ(x + k) = 0`. -/
theorem q24a_alt_sum_eulerPolyE (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 2), (-1 : ℂ) ^ k * ((n + 1).choose k : ℂ) * eulerPolyE n (x + k) = 0 := by
  refine q24a_alt_sum_eq_zero_of_poly _ (fun i => (n.choose (n - i) : ℂ) * eulerPolyE (n - i) x)
    (n + 1) fun j => ?_
  rw [eulerPolyE_add, ← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega, Nat.sub_sub_self hi']

/-- `∑_{k=0}^{n+1} (-1)ᵏ (n+1 choose k) Bₙ(x + k) = 0`. -/
theorem q24a_alt_sum_bernoulliPolyB (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 2), (-1 : ℂ) ^ k * ((n + 1).choose k : ℂ) * bernoulliPolyB n (x + k) = 0 := by
  refine q24a_alt_sum_eq_zero_of_poly _
    (fun i => (n.choose (n - i) : ℂ) * bernoulliPolyB (n - i) x) (n + 1) fun j => ?_
  rw [bernoulliPolyB_add, ← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega, Nat.sub_sub_self hi']

/-- Reindexing `Icc 1 n` to `range n`. -/
theorem q24a_sum_Icc_one' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- **Euler polynomials as a Newton series**: `Eₘ(x) = ∑_{k=0}^{m} 2⁻ᵏ ∑_{j=0}^{k} (-1)ʲ
(k choose j) (x + j)ᵐ`. -/
theorem q24a_eulerPolyE_newton (m : ℕ) (x : ℂ) :
    eulerPolyE m x = ∑ k ∈ range (m + 1), 1 / (2 : ℂ) ^ k *
      ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * (x + j) ^ m := by
  set g : ℂ → ℂ := fun y => y ^ m
  have hQ : ∀ z, ∑ k ∈ range (m + 1), 1 / (2 : ℂ) ^ k *
      ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * (z + j) ^ m =
      ∑ k ∈ range (m + 1), (-1 / 2 : ℂ) ^ k * (fwdDiff 1)^[k] g z := by
    intro z; refine sum_congr rfl fun k _ => ?_
    rw [q24a_alt_sum_eq_fwdDiff g k z, div_pow, one_div]; ring
  rw [hQ]
  set Qp : ℂ[X] := ∑ k ∈ range (m + 1), Polynomial.C ((-1 / 2 : ℂ) ^ k) *
    ∑ j ∈ range (k + 1), Polynomial.C ((((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) : ℤ) : ℂ)) *
      (X + Polynomial.C (j : ℂ)) ^ m
  have hQp : ∀ z, Qp.eval z = ∑ k ∈ range (m + 1), (-1 / 2 : ℂ) ^ k * (fwdDiff 1)^[k] g z := by
    intro z
    simp only [Qp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    refine sum_congr rfl fun k _ => ?_
    rw [fwdDiff_iter_eq_sum_shift]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  set Ep : ℂ[X] := (Polynomial.euler m).map (algebraMap ℚ ℂ)
  have hEp : ∀ z, Ep.eval z = eulerPolyE m z := fun z => (b24a_aeval_eq_eval_map _ z).symm
  have hzero : Qp - Ep = 0 := by
    refine b24a_eq_zero_of_add_add_self (h := 1) one_ne_zero fun z => ?_
    simp only [Polynomial.eval_sub, hQp, hEp]
    have h1 := eulerPolyE_add_one_add m z
    have h2 : ∑ k ∈ range (m + 1), (-1 / 2 : ℂ) ^ k * (fwdDiff 1)^[k] g (z + 1) +
        ∑ k ∈ range (m + 1), (-1 / 2 : ℂ) ^ k * (fwdDiff 1)^[k] g z = 2 * z ^ m := by
      rw [← sum_add_distrib]
      have : ∀ k ∈ range (m + 1), (-1 / 2 : ℂ) ^ k * (fwdDiff 1)^[k] g (z + 1) +
          (-1 / 2 : ℂ) ^ k * (fwdDiff 1)^[k] g z =
          2 * ((-1 / 2 : ℂ) ^ k * (fwdDiff 1)^[k] g z -
            (-1 / 2 : ℂ) ^ (k + 1) * (fwdDiff 1)^[k + 1] g z) := by
        intro k _; rw [q24a_fwdDiff_iter_add_one, pow_succ]; ring
      rw [sum_congr rfl this, ← mul_sum, sum_range_sub']
      have h0 : (fwdDiff 1)^[m + 1] g = 0 := fwdDiff_iter_pow_eq_zero_of_lt (Nat.lt_succ_self m)
      rw [h0]; simp [g]
    linear_combination h2 - h1
  have := congrArg (Polynomial.eval x) hzero
  rw [Polynomial.eval_sub, hQp, hEp, Polynomial.eval_zero] at this
  linear_combination -this

/-- Faulhaber: `∑_{j=1}^{k-1} jᴺ = k ∑_{e=0}^{N} cₑ kᵉ`, `cₑ = B_{N-e} (N+1 choose N-e)/(N+1)`,
`N ≥ 1`. -/
theorem r24a_sum_pow_eq_mul_poly {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ∑ j ∈ Icc 1 (k - 1), (j : ℚ) ^ N = k * ∑ e ∈ range (N + 1),
      bernoulli (N - e) * ((N + 1).choose (N - e) : ℚ) / (N + 1) * (k : ℚ) ^ e := by
  have h1 : ∑ j ∈ Icc 1 (k - 1), (j : ℚ) ^ N = ∑ j ∈ range k, (j : ℚ) ^ N := by
    rcases k with _ | m
    · simp
    · rw [sum_range_succ', q24a_sum_Icc_one]; simp [show N ≠ 0 by omega]
  rw [h1, sum_range_pow, ← sum_range_reflect, mul_sum]
  refine sum_congr rfl fun e he => ?_
  have he' : e ≤ N := Nat.lt_succ_iff.mp (mem_range.mp he)
  rw [show N + 1 - 1 - e = N - e by omega, show N + 1 - (N - e) = e + 1 by omega, pow_succ]
  ring

/-- **DLMF 24.6.1**: `B₂ₙ = ∑_{k=2}^{2n+1} ((-1)^{k-1}/k) (2n+1 choose k) ∑_{j=1}^{k-1} j^{2n}`,
`n ≥ 1`. -/
@[dlmf 24.6.E1]
theorem bernoulli_two_mul_eq_explicit₁ {n : ℕ} (hn : 1 ≤ n) :
    bernoulli (2 * n) = ∑ k ∈ Icc 2 (2 * n + 1), ((-1 : ℚ) ^ (k - 1) / k) *
      ((2 * n + 1).choose k : ℚ) * ∑ j ∈ Icc 1 (k - 1), (j : ℚ) ^ (2 * n) := by
  set N := 2 * n with hNdef
  have hN : 1 ≤ N := by omega
  set c : ℕ → ℚ := fun e => bernoulli (N - e) * ((N + 1).choose (N - e) : ℚ) / (N + 1)
  set F : ℕ → ℚ := fun k => ∑ e ∈ range (N + 1), c e * (k : ℚ) ^ e
  have hz : ∑ k ∈ range (N + 1 + 1), (-1 : ℚ) ^ k * ((N + 1).choose k : ℚ) * F k = 0 := by
    have := q24a_alt_sum_eq_zero_of_poly (fun k => ((F k : ℚ) : ℂ)) (fun e => (c e : ℂ)) (N + 1)
      (fun k => by simp only [F]; push_cast; rfl)
    exact_mod_cast this
  have hF0 : F 0 = bernoulli N := by
    simp only [F, c]
    rw [sum_eq_single 0 (fun e _ he => by simp [he]) (by simp)]
    simp only [Nat.sub_zero, pow_zero, mul_one, Nat.choose_succ_self_right]
    push_cast; field_simp
  rw [sum_range_succ', hF0] at hz
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul] at hz
  -- the target, over `Icc 1 (N+1)`
  have hIcc : Icc 1 (N + 1) = insert 1 (Icc 2 (N + 1)) := by
    ext k; simp only [mem_Icc, mem_insert]; omega
  have h1 : ∑ k ∈ Icc 2 (N + 1), ((-1 : ℚ) ^ (k - 1) / k) * ((N + 1).choose k : ℚ) *
      ∑ j ∈ Icc 1 (k - 1), (j : ℚ) ^ N = ∑ k ∈ Icc 1 (N + 1), ((-1 : ℚ) ^ (k - 1) / k) *
      ((N + 1).choose k : ℚ) * ∑ j ∈ Icc 1 (k - 1), (j : ℚ) ^ N := by
    rw [hIcc, sum_insert (by simp)]; simp
  rw [h1, q24a_sum_Icc_one]
  have h2 : ∀ k ∈ range (N + 1), ((-1 : ℚ) ^ (k + 1 - 1) / ((k + 1 : ℕ) : ℚ)) *
      ((N + 1).choose (k + 1) : ℚ) * ∑ j ∈ Icc 1 (k + 1 - 1), (j : ℚ) ^ N =
      -((-1 : ℚ) ^ (k + 1) * ((N + 1).choose (k + 1) : ℚ) * F (k + 1)) := by
    intro k _
    rw [r24a_sum_pow_eq_mul_poly hN]
    have : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    simp only [F, c, Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [sum_congr rfl h2, sum_neg_distrib]
  linarith

/-! ### Helpers for 24.6.2: Eulerian sums -/

/-- Hockey stick over a range: `∑_{i ≤ N} (i choose a) = (N+1 choose a+1)`. -/
theorem s24a_sum_range_choose (N a : ℕ) :
    ∑ i ∈ range (N + 1), i.choose a = (N + 1).choose (a + 1) := by
  induction N with
  | zero => cases a <;> simp [Nat.choose_eq_zero_of_lt]
  | succ N ih => rw [sum_range_succ, ih, Nat.choose_succ_succ (N + 1) a, add_comm]

/-- Upper Chu–Vandermonde: `∑_{i ≤ n} (i choose a)(n-i choose b) = (n+1 choose a+b+1)`. -/
theorem s24a_upper_vandermonde (n a b : ℕ) :
    ∑ i ∈ range (n + 1), i.choose a * (n - i).choose b = (n + 1).choose (a + b + 1) := by
  induction n generalizing b with
  | zero => cases a <;> cases b <;> simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    cases b with
    | zero => simpa using s24a_sum_range_choose (n + 1) a
    | succ b =>
      rw [sum_range_succ, Nat.sub_self, Nat.choose_zero_succ, mul_zero, add_zero]
      have : ∀ i ∈ range (n + 1), i.choose a * (n + 1 - i).choose (b + 1) =
          i.choose a * (n - i).choose (b + 1) + i.choose a * (n - i).choose b := by
        intro i hi
        have := mem_range.mp hi
        rw [show n + 1 - i = (n - i) + 1 by omega, Nat.choose_succ_succ, mul_add, add_comm]
      rw [sum_congr rfl this, sum_add_distrib, ih, ih,
        show a + (b + 1) + 1 = (a + b + 1) + 1 by ring,
        Nat.choose_succ_succ (n + 1), add_comm]

/-- Frobenius-type expansion of the Eulerian sums:
`∑_{j=1}^{k} (-1)^j jⁿ (n+1 choose k-j) =
∑_{i=0}^{k} (n-i choose k-i) ∑_{j=0}^{i} (-1)^j (i choose j) jⁿ`
for `1 ≤ n`, `k ≤ n`. -/
theorem s24a_eulerian_expand {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    ∑ j ∈ Icc 1 k, (-1 : ℚ) ^ j * (j : ℚ) ^ n * ((n + 1).choose (k - j) : ℚ) =
      ∑ i ∈ range (k + 1), ((n - i).choose (k - i) : ℚ) *
        ∑ j ∈ range (i + 1), (-1 : ℚ) ^ j * (i.choose j : ℚ) * (j : ℚ) ^ n := by
  have hext : ∀ i ∈ range (k + 1), ((n - i).choose (k - i) : ℚ) *
      ∑ j ∈ range (i + 1), (-1 : ℚ) ^ j * (i.choose j : ℚ) * (j : ℚ) ^ n =
      ∑ j ∈ range (k + 1), ((n - i).choose (k - i) : ℚ) * ((-1 : ℚ) ^ j * (i.choose j : ℚ) *
        (j : ℚ) ^ n) := by
    intro i hi
    rw [mul_sum]
    refine sum_subset (range_subset_range.mpr (by simp at hi; omega)) fun j hj hj' => ?_
    simp only [mem_range] at hj hj'
    rw [Nat.choose_eq_zero_of_lt (show i < j by omega)]; simp
  rw [sum_congr rfl hext, sum_comm]
  have h0 : ∑ j ∈ Icc 1 k, (-1 : ℚ) ^ j * (j : ℚ) ^ n * ((n + 1).choose (k - j) : ℚ) =
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (j : ℚ) ^ n * ((n + 1).choose (k - j) : ℚ) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    simp [zero_pow (show n ≠ 0 by omega)]
    rfl
  rw [h0]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hV : ∑ i ∈ range (k + 1), ((n - i).choose (k - i) : ℚ) * (i.choose j : ℚ) =
      ((n + 1).choose (k - j) : ℚ) := by
    have h1 : ∑ i ∈ range (k + 1), (n - i).choose (k - i) * i.choose j =
        ∑ i ∈ range (n + 1), i.choose j * (n - i).choose (n - k) := by
      rw [← sum_subset (range_subset_range.mpr (show k + 1 ≤ n + 1 by omega))]
      · refine sum_congr rfl fun i hi => ?_
        have := mem_range.mp hi
        rw [mul_comm, show (n - i).choose (k - i) = (n - i).choose (n - k) by
          rw [← Nat.choose_symm (show k - i ≤ n - i by omega)]; congr 1; omega]
      · intro i hi hi'
        simp only [mem_range] at hi hi'
        rw [Nat.choose_eq_zero_of_lt (show n - i < n - k by omega), mul_zero]
    have h2 := s24a_upper_vandermonde n j (n - k)
    rw [show j + (n - k) + 1 = n + 1 - (k - j) by omega, Nat.choose_symm (by omega)] at h2
    exact_mod_cast h1.trans h2
  rw [← hV, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **DLMF 24.6.9**: `Bₙ = ∑_{k=0}^{n} 1/(k+1) ∑_{j=0}^{k} (-1)ʲ (k choose j) jⁿ`. DLMF states
`n ≥ 1`; with `0⁰ = 1` it also holds for `n = 0` (stronger than DLMF). -/
@[dlmf 24.6.E9]
theorem bernoulli_eq_explicit₉ (n : ℕ) :
    bernoulli n = ∑ k ∈ range (n + 1), 1 / ((k : ℚ) + 1) *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * (j : ℚ) ^ n := by
  have h := q24a_beta_eq n
  have : ((bernoulli n : ℚ) : ℂ) = ((∑ k ∈ range (n + 1), 1 / ((k : ℚ) + 1) *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * (j : ℚ) ^ n : ℚ) : ℂ) := by
    rw [← h, q24a_beta]; push_cast
    exact sum_congr rfl fun k _ => by rw [q24a_c]; ring
  exact_mod_cast this

/-- **DLMF 24.6.2**: `Bₙ = 1/(n+1) ∑_{k=1}^{n} ∑_{j=1}^{k} (-1)ʲ jⁿ (n+1 choose k-j)/(n choose k)`,
`n ≥ 1`. -/
@[dlmf 24.6.E2]
theorem bernoulli_eq_explicit₂ {n : ℕ} (hn : 1 ≤ n) :
    bernoulli n = 1 / (n + 1) * ∑ k ∈ Icc 1 n, (∑ j ∈ Icc 1 k,
      (-1 : ℚ) ^ j * (j : ℚ) ^ n * ((n + 1).choose (k - j) : ℚ)) / (n.choose k : ℚ) := by
  set T : ℕ → ℚ := fun i => ∑ j ∈ range (i + 1), (-1 : ℚ) ^ j * (i.choose j : ℚ) * (j : ℚ) ^ n
  have hT0 : T 0 = 0 := by simp [T, zero_pow (show n ≠ 0 by omega)]
  have hstep : ∀ k ∈ Icc 1 n, (∑ j ∈ Icc 1 k,
      (-1 : ℚ) ^ j * (j : ℚ) ^ n * ((n + 1).choose (k - j) : ℚ)) / (n.choose k : ℚ) =
      ∑ i ∈ range (n + 1), (k.choose i : ℚ) / (n.choose i : ℚ) * T i := by
    intro k hk
    have hkn : k ≤ n := (mem_Icc.mp hk).2
    rw [s24a_eulerian_expand hn hkn, sum_div]
    rw [← sum_subset (range_subset_range.mpr (show k + 1 ≤ n + 1 by omega))]
    · refine sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have hc := Nat.choose_mul (n := n) (k := k) (s := i) hik
      have hc' : (n.choose k : ℚ) * (k.choose i : ℚ) =
          (n.choose i : ℚ) * ((n - i).choose (k - i) : ℚ) := by
        exact_mod_cast hc
      have h1 : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
      have h2 : (n.choose i : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hik.trans hkn)).ne'
      have : (k.choose i : ℚ) / n.choose i = ((n - i).choose (k - i) : ℚ) / n.choose k := by
        rw [div_eq_div_iff h2 h1]; linear_combination hc'
      rw [this]; ring
    · intro i hi hi'
      simp only [mem_range] at hi hi'
      rw [Nat.choose_eq_zero_of_lt (show k < i by omega)]; simp
  rw [sum_congr rfl hstep, sum_comm, bernoulli_eq_explicit₉, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [hT0, show n ≠ 0 by omega]
  have hs : ∑ k ∈ Icc 1 n, (k.choose i : ℚ) = ((n + 1).choose (i + 1) : ℚ) := by
    have := s24a_sum_range_choose n i
    rw [sum_range_succ', Nat.choose_eq_zero_of_lt hi0, add_zero] at this
    rw [q24a_sum_Icc_one']
    exact_mod_cast this
  have hsc := Nat.add_one_mul_choose_eq n i
  have hsc' : ((n : ℚ) + 1) * (n.choose i : ℚ) =
      ((n + 1).choose (i + 1) : ℚ) * ((i : ℚ) + 1) := by
    exact_mod_cast hsc
  have h2 : (n.choose i : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hin).ne'
  rw [← sum_mul, ← sum_div, hs]
  have : (n : ℚ) + 1 ≠ 0 := by positivity
  have : (i : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  linear_combination T i * hsc'

/-- **DLMF 24.6.3**: `B₂ₙ = ∑_{k=1}^{n} ((k-1)! k!/(2k+1)!) ∑_{j=1}^{k} (-1)^{j-1} (2k choose k+j)
j^{2n}`, `n ≥ 1`. -/
@[dlmf 24.6.E3]
theorem bernoulli_two_mul_eq_explicit₃ {n : ℕ} (hn : 1 ≤ n) :
    bernoulli (2 * n) = ∑ k ∈ Icc 1 n, ((k - 1)! * k ! / (2 * k + 1)! : ℚ) *
      ∑ j ∈ Icc 1 k, (-1 : ℚ) ^ (j - 1) * ((2 * k).choose (k + j) : ℚ) * (j : ℚ) ^ (2 * n) := by
  sorry

/-! ### Helpers for 24.6.4–24.6.5: central differences -/

section

open Polynomial

/-- A rational polynomial with `H(x+1) + H(x-1) = 0` for all `x` vanishes. -/
theorem r24a_poly_eq_zero_of_add_shift {H : ℚ[X]}
    (h : ∀ x : ℚ, H.eval (x + 1) + H.eval (x - 1) = 0) : H = 0 := by
  have h2 : ∀ x : ℚ, H.eval (x + 2) = -H.eval x := fun x => by
    have := h (x + 1); rw [show x + 1 + 1 = x + 2 by ring, show x + 1 - 1 = x by ring] at this
    linarith
  have h4 : ∀ x : ℚ, H.eval (x + 4) = H.eval x := fun x => by
    rw [show x + 4 = x + 2 + 2 by ring, h2, h2, neg_neg]
  have hk : ∀ k : ℕ, H.eval (4 * (k : ℚ)) = H.eval 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [show (4 : ℚ) * ((k + 1 : ℕ) : ℚ) = 4 * k + 4 by push_cast; ring, h4, ih]
  set P := H - Polynomial.C (H.eval 0)
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (4 * k : ℚ))
      (fun a b hab => by simpa using hab) fun k => ?_
    simp [P, hk k]
  have hc : H = Polynomial.C (H.eval 0) := sub_eq_zero.mp hP
  have := h 0
  rw [hc] at this; simp at this
  rw [hc, this, map_zero]


/-- Second difference of iterated forward differences:
`Δ^{k+2} f(y) = Δᵏ f(y+2) - 2 Δᵏ f(y+1) + Δᵏ f(y)`. -/
theorem r24a_fwdDiff_iter_add_two (f : ℚ → ℚ) (k : ℕ) (y : ℚ) :
    (fwdDiff 1)^[k + 2] f y =
      (fwdDiff 1)^[k] f (y + 2) - 2 * (fwdDiff 1)^[k] f (y + 1) + (fwdDiff 1)^[k] f y := by
  rw [add_comm, Function.iterate_add_apply]
  show fwdDiff 1 (fwdDiff 1 ((fwdDiff 1)^[k] f)) y = _
  unfold fwdDiff
  rw [show y + 1 + 1 = y + 2 by ring]
  ring

/-- The central-difference series `Q(x) = ∑_{k=0}^{n} (-1/2)ᵏ Δ^{2k} f(x - k)` of `f = x^{2n}`
solves `Q(x+1) + Q(x-1) = 2x^{2n}`. -/
theorem r24a_central_series (n : ℕ) (x : ℚ) :
    let Q : ℚ → ℚ := fun y => ∑ k ∈ range (n + 1), (-1 / 2 : ℚ) ^ k *
      (fwdDiff 1)^[2 * k] (fun r : ℚ => r ^ (2 * n)) (y - k)
    Q (x + 1) + Q (x - 1) = 2 * x ^ (2 * n) := by
  intro Q
  set f : ℚ → ℚ := fun r : ℚ => r ^ (2 * n)
  set g : ℕ → ℚ → ℚ := fun k y => (fwdDiff 1)^[2 * k] f y
  have hstep : ∀ k, (-1 / 2 : ℚ) ^ k * g k (x + 1 - k) + (-1 / 2 : ℚ) ^ k * g k (x - 1 - k) =
      2 * ((-1 / 2 : ℚ) ^ k * g k (x - k) -
        (-1 / 2 : ℚ) ^ (k + 1) * g (k + 1) (x - (k + 1 : ℕ))) := by
    intro k
    have := r24a_fwdDiff_iter_add_two f (2 * k) (x - 1 - k)
    simp only [g]
    rw [show 2 * (k + 1) = 2 * k + 2 by ring,
      show x - ((k + 1 : ℕ) : ℚ) = x - 1 - k by push_cast; ring, this]
    rw [show x - 1 - k + 2 = x + 1 - k by ring, show x - 1 - k + 1 = x - k by ring, pow_succ]
    ring
  have hQ : Q (x + 1) + Q (x - 1) = 2 * ∑ k ∈ range (n + 1), ((-1 / 2 : ℚ) ^ k * g k (x - k) -
      (-1 / 2 : ℚ) ^ (k + 1) * g (k + 1) (x - (k + 1 : ℕ))) := by
    simp only [Q, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← hstep k]
  rw [hQ, sum_range_sub' (fun k => (-1 / 2 : ℚ) ^ k * g k (x - k))]
  have h0 : g (n + 1) = 0 := by
    simp only [g, f]
    exact fwdDiff_iter_pow_eq_zero_of_lt (by omega)
  simp [h0, g, f]

/-- `E₂ₙ` from the central-difference series: `E₂ₙ = ∑_{k=0}^{n} (-1/2)ᵏ Δ^{2k}[x^{2n}](-k)`. -/
theorem r24a_eulerNumber_central (n : ℕ) :
    eulerNumber (2 * n) = ∑ k ∈ range (n + 1), (-1 / 2 : ℚ) ^ k *
      (fwdDiff 1)^[2 * k] (fun r : ℚ => r ^ (2 * n)) (0 - k) := by
  set QP : ℚ[X] := ∑ k ∈ range (n + 1), Polynomial.C ((-1 / 2 : ℚ) ^ k) *
    ∑ i ∈ range (2 * k + 1), Polynomial.C (((-1 : ℤ) ^ (2 * k - i) * (2 * k).choose i : ℤ) : ℚ) *
      (X + Polynomial.C ((i : ℚ) - k)) ^ (2 * n)
  have hQP : ∀ y : ℚ, QP.eval y = ∑ k ∈ range (n + 1), (-1 / 2 : ℚ) ^ k *
      (fwdDiff 1)^[2 * k] (fun r : ℚ => r ^ (2 * n)) (y - k) := by
    intro y
    simp only [QP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X]
    refine sum_congr rfl fun k _ => ?_
    rw [fwdDiff_iter_eq_sum_shift]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]
    congr 2; ring
  set GP : ℚ[X] := Polynomial.C ((2 : ℚ) ^ (2 * n)) *
    (euler (2 * n)).comp (Polynomial.C (1 / 2) * X + Polynomial.C (1 / 2))
  have hGP : ∀ x : ℚ, GP.eval (x + 1) + GP.eval (x - 1) = 2 * x ^ (2 * n) := by
    intro x
    simp only [GP, eval_mul, eval_C, eval_comp, eval_add, eval_X]
    have := euler_eval_add_one_add (2 * n) (x / 2)
    rw [show 1 / 2 * (x + 1) + 1 / 2 = x / 2 + 1 by ring,
      show 1 / 2 * (x - 1) + 1 / 2 = x / 2 by ring,
      ← mul_add, this, div_pow]
    field_simp
  have hH : QP - GP = 0 := by
    refine r24a_poly_eq_zero_of_add_shift fun x => ?_
    simp only [eval_sub]
    have h1 := r24a_central_series n x
    simp only at h1
    rw [← hQP, ← hQP] at h1
    linarith [hGP x]
  have h0 := congrArg (Polynomial.eval 0) (sub_eq_zero.mp hH)
  rw [hQP] at h0
  rw [h0]
  simp only [GP, eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_zero, zero_add, eulerNumber]

/-- Folding the central difference of the even function `x^{2n}`:
`∑_{i=0}^{2k} (-1)^{2k-i} (2k choose i)(i-k)^{2n} =
2(-1)ᵏ ∑_{j=1}^{k} (-1)ʲ (2k choose k-j) j^{2n}`. -/
theorem r24a_central_fold (n k : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range (2 * k + 1), (-1 : ℚ) ^ (2 * k - i) * ((2 * k).choose i : ℚ) *
      ((i : ℚ) - k) ^ (2 * n) = 2 * (-1) ^ k * ∑ j ∈ Icc 1 k, (-1 : ℚ) ^ j *
        ((2 * k).choose (k - j) : ℚ) * (j : ℚ) ^ (2 * n) := by
  rw [show 2 * k + 1 = k + (k + 1) by ring, sum_range_add, sum_range_succ', ← sum_range_reflect,
    q24a_sum_Icc_one', mul_sum]
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
  have e1 : ((k : ℚ) - 1 - j - k) ^ (2 * n) = ((j : ℚ) + 1) ^ (2 * n) := by
    rw [show (k : ℚ) - 1 - j - k = -((j : ℚ) + 1) by ring, neg_pow, pow_mul]; norm_num
  have e2 : ((k : ℚ) + (j + 1) - k) = (j : ℚ) + 1 := by ring
  rw [e1, e2]
  have e3 : (-1 : ℚ) ^ k = (-1) ^ (k - j - 1) * (-1) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e3]
  have e4 : (-1 : ℚ) ^ (j * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  ring_nf
  rw [e4]
  ring


/-- Reflected summation over a final segment: `∑_{k=n-m}^{n} G k = ∑_{i=0}^{m} G (n - i)`. -/
theorem r24a_sum_Icc_sub_reflect {M : Type*} [AddCommMonoid M] (G : ℕ → M) {m n : ℕ} (h : m ≤ n) :
    ∑ k ∈ Icc (n - m) n, G k = ∑ i ∈ range (m + 1), G (n - i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show Icc (n - (m + 1)) n = insert (n - (m + 1)) (Icc (n - m) n) by
      ext k; simp only [mem_insert, mem_Icc]; omega, sum_insert (by simp only [mem_Icc]; omega),
      ih (by omega), sum_range_succ (n := m + 1), add_comm]

end

/-- **DLMF 24.6.4**: `E₂ₙ = ∑_{k=1}^{n} 2^{1-k} ∑_{j=1}^{k} (-1)ʲ (2k choose k-j) j^{2n}`,
`n ≥ 1`. -/
@[dlmf 24.6.E4]
theorem eulerNumber_two_mul_eq_explicit₄ {n : ℕ} (hn : 1 ≤ n) :
    eulerNumber (2 * n) = ∑ k ∈ Icc 1 n, 1 / (2 : ℚ) ^ (k - 1) *
      ∑ j ∈ Icc 1 k, (-1 : ℚ) ^ j * ((2 * k).choose (k - j) : ℚ) * (j : ℚ) ^ (2 * n) := by
  rw [r24a_eulerNumber_central, sum_range_succ', q24a_sum_Icc_one']
  simp only [pow_zero, mul_zero, Function.iterate_zero, id, Nat.cast_zero, sub_zero,
    zero_pow (show 2 * n ≠ 0 by omega), add_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [fwdDiff_iter_eq_sum_shift]
  have : ∑ i ∈ range (2 * (k + 1) + 1),
      ((-1 : ℤ) ^ (2 * (k + 1) - i) * ((2 * (k + 1)).choose i : ℤ)) •
      (fun r : ℚ => r ^ (2 * n)) (0 - ((k + 1 : ℕ) : ℚ) + i • (1 : ℚ)) =
      ∑ i ∈ range (2 * (k + 1) + 1), (-1 : ℚ) ^ (2 * (k + 1) - i) * ((2 * (k + 1)).choose i : ℚ) *
        ((i : ℚ) - ((k + 1 : ℕ) : ℚ)) ^ (2 * n) := by
    refine sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]; push_cast; ring
  rw [this, r24a_central_fold n (k + 1) hn, Nat.add_sub_cancel]
  rw [show (-1 / 2 : ℚ) ^ (k + 1) = (-1) ^ (k + 1) / (2 * 2 ^ k) by
    rw [div_pow, pow_succ (2 : ℚ) k]; ring]
  have h1 : ((-1 : ℚ) ^ (k + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  field_simp
  linear_combination (∑ j ∈ Icc 1 (k + 1), (-1 : ℚ) ^ j * ((2 * (k + 1)).choose (k + 1 - j) : ℚ) *
    (j : ℚ) ^ (2 * n)) * h1

/-- **DLMF 24.6.5**: `E₂ₙ = 2^{1-n} ∑_{k=0}^{n-1} (-1)^{n-k} (n-k)^{2n}
∑_{j=0}^{k} (2n-2j choose k-j) 2ʲ`, `n ≥ 1`. -/
@[dlmf 24.6.E5]
theorem eulerNumber_two_mul_eq_explicit₅ {n : ℕ} (hn : 1 ≤ n) :
    eulerNumber (2 * n) = 1 / (2 : ℚ) ^ (n - 1) * ∑ k ∈ range n,
      (-1 : ℚ) ^ (n - k) * ((n - k : ℕ) : ℚ) ^ (2 * n) *
        ∑ j ∈ range (k + 1), ((2 * n - 2 * j).choose (k - j) : ℚ) * 2 ^ j := by
  rw [eulerNumber_two_mul_eq_explicit₄ hn, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm' (t' := Icc 1 n) (s' := fun j => Icc j n) (fun k j => by
    simp only [mem_Icc]; omega)]
  rw [q24a_sum_Icc_one', ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < n := mem_range.mp hk
  rw [show n - 1 - k + 1 = n - k by omega,
    r24a_sum_Icc_sub_reflect _ (by omega : k ≤ n)]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show n - i - (n - k) = k - i by omega, show 2 * (n - i) = 2 * n - 2 * i by omega]
  rw [show (2 : ℚ) ^ (n - 1) = 2 ^ (n - i - 1) * 2 ^ i by rw [← pow_add]; congr 1; omega]
  field_simp

/-! ### Helpers for 24.6.6: the symmetric shift -/

section

open fwdDiff_aux
open Polynomial

/-- The symmetric shift `f ↦ f(· + 1) + f(· - 1)` as an endomorphism. -/
def s24a_S : Module.End ℤ (ℚ → ℚ) := shiftₗ ℚ ℚ (1 : ℚ) + shiftₗ ℚ ℚ (-1 : ℚ)

/-- Binomial expansion of powers of the symmetric shift. -/
theorem s24a_S_pow_apply (f : ℚ → ℚ) (i : ℕ) (x : ℚ) :
    (s24a_S ^ i) f x = ∑ j ∈ range (i + 1), (i.choose j : ℚ) * f (x + j - (i - j : ℕ)) := by
  have hc : Commute (shiftₗ ℚ ℚ (1 : ℚ)) (shiftₗ ℚ ℚ (-1 : ℚ)) := by
    ext f y; simp [Module.End.mul_apply, shiftₗ_apply, add_right_comm]
  rw [s24a_S, hc.add_pow, LinearMap.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, shiftₗ_pow_apply,
    shiftₗ_pow_apply]
  simp only [Pi.smul_apply, nsmul_eq_mul, mul_one, mul_neg]
  congr 2
  ring

/-- `2 - S = -(τ₋₁ Δ²)`. -/
theorem s24a_two_sub_S :
    (2 : Module.End ℤ (ℚ → ℚ)) - s24a_S =
      -(shiftₗ ℚ ℚ (-1 : ℚ) * fwdDiffₗ ℚ ℚ (1 : ℚ) ^ 2) := by
  ext f y
  simp [s24a_S, pow_two, Module.End.mul_apply, shiftₗ_apply, fwdDiff]
  ring_nf

/-- `(2 - S)^N` kills `x^{2n}` for `N > n`. -/
theorem s24a_two_sub_S_pow_apply {n N : ℕ} (hN : n < N) (x : ℚ) :
    ((2 - s24a_S) ^ N) (fun r : ℚ => r ^ (2 * n)) x = 0 := by
  have hc : Commute (shiftₗ ℚ ℚ (-1 : ℚ)) (fwdDiffₗ ℚ ℚ (1 : ℚ) ^ 2) := by
    refine Commute.pow_right ?_ 2
    ext f y; simp [Module.End.mul_apply, shiftₗ_apply, fwdDiff, add_right_comm]
  have h0 : (fwdDiffₗ ℚ ℚ (1 : ℚ) ^ (2 * N)) (fun r : ℚ => r ^ (2 * n)) = 0 := by
    have := congrFun (coe_fwdDiffₗ_pow (M := ℚ) (G := ℚ) (1 : ℚ) (2 * N))
      (fun r : ℚ => r ^ (2 * n))
    rw [this]
    exact fwdDiff_iter_pow_eq_zero_of_lt (by omega)
  rw [s24a_two_sub_S, neg_pow, hc.mul_pow, ← pow_mul, Module.End.mul_apply, Module.End.mul_apply,
    h0, map_zero, map_zero]
  rfl

/-- Binomial expansion of `(2 - S)^N x^{2n} = 0`. -/
theorem s24a_binom_S {n N : ℕ} (hN : n < N) (x : ℚ) :
    ∑ i ∈ range (N + 1), (-1 : ℚ) ^ i * 2 ^ (N - i) * (N.choose i : ℚ) *
      (s24a_S ^ i) (fun r : ℚ => r ^ (2 * n)) x = 0 := by
  have h := s24a_two_sub_S_pow_apply hN x
  have hc : Commute (-s24a_S) (2 : Module.End ℤ (ℚ → ℚ)) := (Commute.ofNat_right _ 2)
  rw [sub_eq_neg_add, hc.add_pow, LinearMap.sum_apply, Finset.sum_apply] at h
  rw [← h]
  refine sum_congr rfl fun i _ => ?_
  rw [neg_pow s24a_S i, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hpow2 : (2 : Module.End ℤ (ℚ → ℚ)) ^ (N - i) = ((2 ^ (N - i) : ℕ) : Module.End ℤ _) := by
    push_cast; rfl
  have hneg : (-1 : Module.End ℤ (ℚ → ℚ)) ^ i = (((-1) ^ i : ℤ) : Module.End ℤ _) := by
    push_cast; rfl
  rw [hpow2, hneg, Module.End.intCast_apply, Module.End.natCast_apply, Module.End.natCast_apply,
    map_nsmul, map_nsmul]
  simp only [Pi.smul_apply, zsmul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  push_cast
  ring

/-- Folding a symmetric sum: `∑_{j=0}^{k} (k choose j)(j - (k-j))^{2n} =
2 ∑_{j=0}^{⌊(k-1)/2⌋} (k choose j)(k-2j)^{2n}` for `k ≥ 1`, `n ≥ 1`. -/
theorem s24a_fold (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∑ j ∈ range (k + 1), (k.choose j : ℚ) * ((j : ℚ) - ((k - j : ℕ) : ℚ)) ^ (2 * n) =
      2 * ∑ j ∈ range ((k - 1) / 2 + 1), (k.choose j : ℚ) * ((k - 2 * j : ℕ) : ℚ) ^ (2 * n) := by
  set g : ℕ → ℚ := fun j => (k.choose j : ℚ) * ((j : ℚ) - ((k - j : ℕ) : ℚ)) ^ (2 * n)
  have hA : (range (k + 1)).filter (fun j => 2 * j < k) = range ((k - 1) / 2 + 1) := by
    ext j; simp only [mem_filter, mem_range]; omega
  have hsplit := sum_filter_add_sum_filter_not (range (k + 1)) (fun j => 2 * j < k) g
  have hsplit2 := sum_filter_add_sum_filter_not ((range (k + 1)).filter (fun j => ¬ 2 * j < k))
    (fun j => 2 * j = k) g
  have hC : ∑ j ∈ ((range (k + 1)).filter (fun j => ¬ 2 * j < k)).filter (fun j => 2 * j = k),
      g j = 0 := by
    refine sum_eq_zero fun j hj => ?_
    simp only [mem_filter] at hj
    simp only [g]
    rw [show ((j : ℚ) - ((k - j : ℕ) : ℚ)) = 0 by
      rw [Nat.cast_sub (by omega)]; have : (k : ℚ) = 2 * j := by exact_mod_cast hj.2.symm
      rw [this]; ring]
    simp; omega
  have hB : ∑ j ∈ ((range (k + 1)).filter (fun j => ¬ 2 * j < k)).filter (fun j => ¬ 2 * j = k),
      g j = ∑ j ∈ (range (k + 1)).filter (fun j => 2 * j < k), g j := by
    refine sum_nbij' (fun j => k - j) (fun j => k - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_filter, mem_range] at hj ⊢; omega
    · intro j hj; simp only [mem_filter, mem_range] at hj ⊢; omega
    · intro j hj; simp only [mem_filter, mem_range] at hj; omega
    · intro j hj; simp only [mem_filter, mem_range] at hj; omega
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      simp only [g]
      rw [Nat.choose_symm (by omega), show k - (k - j) = j by omega,
        show ((k - j : ℕ) : ℚ) - (j : ℚ) = -((j : ℚ) - ((k - j : ℕ) : ℚ)) by ring, neg_pow,
        pow_mul (-1 : ℚ)]
      simp
  have hD : ∀ j ∈ (range (k + 1)).filter (fun j => 2 * j < k),
      g j = (k.choose j : ℚ) * ((k - 2 * j : ℕ) : ℚ) ^ (2 * n) := by
    intro j hj
    simp only [mem_filter, mem_range] at hj
    simp only [g]
    rw [show ((j : ℚ) - ((k - j : ℕ) : ℚ)) = -((k - 2 * j : ℕ) : ℚ) by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring, neg_pow,
      pow_mul (-1 : ℚ)]
    simp
  rw [← hsplit, ← hsplit2, hC, hB, zero_add, ← two_mul, sum_congr rfl hD, hA]

/-- Proof of DLMF 24.6.6 by the symmetric-shift operator and uniqueness of polynomial solutions
of `Q(x+1) + Q(x-1) = 2x^{2n}`. -/
theorem s24a_eulerNumber_two_mul_eq_explicit₆ {n : ℕ} (hn : 1 ≤ n) :
    eulerNumber (2 * n) = ∑ k ∈ Icc 1 (2 * n), ((-1 : ℚ) ^ k / 2 ^ (k - 1)) *
      ((2 * n + 1).choose (k + 1) : ℚ) *
        ∑ j ∈ range ((k - 1) / 2 + 1), (k.choose j : ℚ) * ((k - 2 * j : ℕ) : ℚ) ^ (2 * n) := by
  set p : ℚ → ℚ := fun r : ℚ => r ^ (2 * n)
  set N := 2 * n + 1
  set Q : ℚ → ℚ := fun x => ∑ k ∈ range N, (-1 : ℚ) ^ k * (N.choose (k + 1) : ℚ) / 2 ^ k *
    (s24a_S ^ k) p x
  have hSshift : ∀ k x,
      (s24a_S ^ k) p (x + 1) + (s24a_S ^ k) p (x - 1) = (s24a_S ^ (k + 1)) p x := by
    intro k x
    rw [pow_succ', Module.End.mul_apply, s24a_S, LinearMap.add_apply, Pi.add_apply,
      shiftₗ_apply, shiftₗ_apply, sub_eq_add_neg]
  have hQ : ∀ x, Q (x + 1) + Q (x - 1) = 2 * x ^ (2 * n) := by
    intro x
    have hb := s24a_binom_S (n := n) (N := N) (by omega) x
    rw [sum_range_succ'] at hb
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
      mul_one] at hb
    have h0 : (1 : Module.End ℤ (ℚ → ℚ)) (fun r : ℚ => r ^ (2 * n)) x = x ^ (2 * n) := rfl
    rw [h0] at hb
    simp only [Q, ← sum_add_distrib]
    have hterm : ∀ k ∈ range N, (-1 : ℚ) ^ k * (N.choose (k + 1) : ℚ) / 2 ^ k *
        (s24a_S ^ k) p (x + 1) + (-1 : ℚ) ^ k * (N.choose (k + 1) : ℚ) / 2 ^ k *
        (s24a_S ^ k) p (x - 1) = -((-1 : ℚ) ^ (k + 1) * 2 ^ (N - (k + 1)) *
          (N.choose (k + 1) : ℚ) * (s24a_S ^ (k + 1)) p x) / 2 ^ (2 * n) := by
      intro k hk
      have hk' := mem_range.mp hk
      rw [← mul_add, hSshift, show (2 : ℚ) ^ (2 * n) = 2 ^ (N - (k + 1)) * 2 ^ k by
        rw [← pow_add]; congr 1; omega]
      field_simp
      ring
    have hN2 : (2 : ℚ) ^ N = 2 * 2 ^ (2 * n) := by rw [pow_succ]; ring
    rw [sum_congr rfl hterm, ← sum_div, sum_neg_distrib, neg_div, neg_eq_iff_eq_neg,
      div_eq_iff (pow_ne_zero _ two_ne_zero)]
    linear_combination hb - x ^ (2 * n) * hN2
  set QP : ℚ[X] := ∑ k ∈ range N, C ((-1 : ℚ) ^ k * (N.choose (k + 1) : ℚ) / 2 ^ k) *
    ∑ j ∈ range (k + 1), C (k.choose j : ℚ) * (X + C ((j : ℚ) - ((k - j : ℕ) : ℚ))) ^ (2 * n)
  have hQP : ∀ y, QP.eval y = Q y := by
    intro y
    simp only [QP, Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X,
      s24a_S_pow_apply, p]
    refine sum_congr rfl fun k _ => ?_
    congr 1
    refine sum_congr rfl fun j _ => ?_
    ring
  set GP : ℚ[X] := C ((2 : ℚ) ^ (2 * n)) * (euler (2 * n)).comp (C (1 / 2) * X + C (1 / 2))
  have hGP : ∀ x : ℚ, GP.eval (x + 1) + GP.eval (x - 1) = 2 * x ^ (2 * n) := by
    intro x
    simp only [GP, eval_mul, eval_C, eval_comp, eval_add, eval_X]
    have := euler_eval_add_one_add (2 * n) (x / 2)
    rw [show 1 / 2 * (x + 1) + 1 / 2 = x / 2 + 1 by ring,
      show 1 / 2 * (x - 1) + 1 / 2 = x / 2 by ring,
      ← mul_add, this, div_pow]
    field_simp
  have hH : QP - GP = 0 := by
    refine r24a_poly_eq_zero_of_add_shift fun x => ?_
    simp only [eval_sub, hQP]
    linarith [hGP x, hQ x]
  have h0 := congrArg (Polynomial.eval 0) (sub_eq_zero.mp hH)
  rw [hQP] at h0
  have hE : eulerNumber (2 * n) = Q 0 := by
    rw [h0]
    simp only [GP, eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_zero, zero_add, eulerNumber]
  rw [hE]
  simp only [Q, s24a_S_pow_apply, p, zero_add]
  rw [sum_range_succ', q24a_sum_Icc_one']
  simp only [pow_zero, zero_add, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul,
    sum_range_one, Nat.cast_zero, sub_zero, zero_pow (show 2 * n ≠ 0 by omega), mul_zero,
    add_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [s24a_fold n (k + 1) hn (by omega), Nat.add_sub_cancel, pow_succ]
  field_simp
  ring

end

/-- **DLMF 24.6.6**: `E₂ₙ = ∑_{k=1}^{2n} ((-1)ᵏ/2^{k-1}) (2n+1 choose k+1)
∑_{j=0}^{⌊(k-1)/2⌋} (k choose j)(k-2j)^{2n}`, `n ≥ 1`. -/
@[dlmf 24.6.E6]
theorem eulerNumber_two_mul_eq_explicit₆ {n : ℕ} (hn : 1 ≤ n) :
    eulerNumber (2 * n) = ∑ k ∈ Icc 1 (2 * n), ((-1 : ℚ) ^ k / 2 ^ (k - 1)) *
      ((2 * n + 1).choose (k + 1) : ℚ) *
        ∑ j ∈ range ((k - 1) / 2 + 1), (k.choose j : ℚ) * ((k - 2 * j : ℕ) : ℚ) ^ (2 * n) := by
  exact s24a_eulerNumber_two_mul_eq_explicit₆ hn

/-- **DLMF 24.6.7**: `Bₙ(x) = ∑_{k=0}^{n} 1/(k+1) ∑_{j=0}^{k} (-1)ʲ (k choose j)(x+j)ⁿ`,
all `n ≥ 0`, complex `x`. -/
@[dlmf 24.6.E7]
theorem bernoulliPolyB_eq_explicit (n : ℕ) (x : ℂ) :
    bernoulliPolyB n x = ∑ k ∈ range (n + 1), 1 / ((k : ℂ) + 1) *
      ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * (x + j) ^ n := by
  have hD : ∀ k, ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * (x + j) ^ n =
      ∑ i ∈ range (n + 1), (n.choose i : ℂ) * x ^ (n - i) * q24a_c k i := by
    intro k
    simp only [q24a_c, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [add_comm x, add_pow, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  simp only [hD, mul_sum]
  rw [sum_comm, bernoulliPolyB_eq_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i + 1 ≤ n + 1 := by simpa using hi
  rw [← q24a_beta_eq, q24a_beta_extend hi', mul_sum, sum_mul]
  exact sum_congr rfl fun k _ => by ring

/-- **DLMF 24.6.8**: `Eₙ(x) = 2⁻ⁿ ∑_{k=1}^{n+1} ∑_{j=0}^{k-1} (-1)ʲ (n+1 choose k)(x+j)ⁿ`, all
`n ≥ 0`, complex `x`. -/
@[dlmf 24.6.E8]
theorem eulerPolyE_eq_explicit (n : ℕ) (x : ℂ) :
    eulerPolyE n x = 1 / (2 : ℂ) ^ n * ∑ k ∈ Icc 1 (n + 1),
      ∑ j ∈ range k, (-1 : ℂ) ^ j * ((n + 1).choose k : ℂ) * (x + j) ^ n := by
  have hin : ∀ k ∈ Icc 1 (n + 1), ∑ j ∈ range k, (-1 : ℂ) ^ j * ((n + 1).choose k : ℂ) * (x + j) ^ n
      = ((n + 1).choose k : ℂ) / 2 * (-((-1) ^ k * eulerPolyE n (x + k)) + eulerPolyE n x) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have h := sum_range_neg_one_pow_mul_add_mul_pow n hk1 x 1 one_ne_zero
    simp only [one_mul, one_pow, div_one] at h
    rw [show ∑ j ∈ range k, (-1 : ℂ) ^ j * ((n + 1).choose k : ℂ) * (x + j) ^ n =
      ((n + 1).choose k : ℂ) * ∑ j ∈ range k, (-1 : ℂ) ^ j * (x + j) ^ n by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring, h, add_comm (k : ℂ) x]
    rw [show (-1 : ℂ) ^ k = -(-1) ^ (k - 1) by
      rw [show k = k - 1 + 1 by omega, pow_succ]; simp]
    ring
  rw [sum_congr rfl hin, q24a_sum_Icc_one']
  have h0 := q24a_alt_sum_eulerPolyE n x
  rw [sum_range_succ'] at h0
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_zero, add_zero] at h0
  have hc := Nat.sum_range_choose (n + 1)
  rw [sum_range_succ'] at hc
  have hc' : ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℂ) = 2 ^ (n + 1) - 1 := by
    have := congrArg (Nat.cast : ℕ → ℂ) hc
    push_cast at this
    simp only [Nat.choose_zero_right, Nat.cast_one] at this
    linear_combination this
  have : ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℂ) / 2 *
      (-((-1) ^ (k + 1) * eulerPolyE n (x + ((k + 1 : ℕ) : ℂ))) + eulerPolyE n x) =
      -(1 / 2) * ∑ k ∈ range (n + 1), (-1 : ℂ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℂ) *
        eulerPolyE n (x + ((k + 1 : ℕ) : ℂ)) +
      eulerPolyE n x / 2 * ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℂ) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [this, hc']
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  linear_combination h0

/-- **DLMF 24.6.10**: `Eₙ = 2⁻ⁿ ∑_{k=1}^{n+1} (n+1 choose k) ∑_{j=0}^{k-1} (-1)ʲ (2j+1)ⁿ`, all
`n ≥ 0`. -/
@[dlmf 24.6.E10]
theorem eulerNumber_eq_explicit₁₀ (n : ℕ) :
    eulerNumber n = 1 / (2 : ℚ) ^ n * ∑ k ∈ Icc 1 (n + 1), ((n + 1).choose k : ℚ) *
      ∑ j ∈ range k, (-1 : ℚ) ^ j * (2 * (j : ℚ) + 1) ^ n := by
  have h := eulerPolyE_eq_explicit n (1 / 2)
  rw [eulerPolyE_half] at h
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have : ((eulerNumber n : ℚ) : ℂ) = ((1 / (2 : ℚ) ^ n * ∑ k ∈ Icc 1 (n + 1),
      ((n + 1).choose k : ℚ) * ∑ j ∈ range k, (-1 : ℚ) ^ j * (2 * (j : ℚ) + 1) ^ n : ℚ) : ℂ) := by
    push_cast
    rw [div_eq_iff h2] at h
    rw [h, mul_comm, ← mul_assoc, mul_one_div_cancel h2, one_mul, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [show (1 / 2 : ℂ) + j = (2 * j + 1) / 2 by ring, div_pow]
    field_simp
  exact_mod_cast this

/-- **DLMF 24.6.11**: `Bₙ = n/(2ⁿ(2ⁿ-1)) ∑_{k=1}^{n} ∑_{j=0}^{k-1} (-1)^{j+1} (n choose k) j^{n-1}`,
`n ≥ 1`. -/
@[dlmf 24.6.E11]
theorem bernoulli_eq_explicit₁₁ {n : ℕ} (hn : 1 ≤ n) :
    bernoulli n = n / (2 ^ n * (2 ^ n - 1)) * ∑ k ∈ Icc 1 n, ∑ j ∈ range k,
      (-1 : ℚ) ^ (j + 1) * (n.choose k : ℚ) * (j : ℚ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [bernoulli_one]; norm_num
  have h := eulerPolyE_eq_explicit m 0
  rw [(eulerPolyE_zero_one hm).1, (eulerPolyE_zero_one hm).2] at h
  have h2 : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (2 : ℂ) ^ (m + 1) - 1 ≠ 0 := by
    rw [sub_ne_zero]; norm_cast
    exact (Nat.one_lt_pow (by omega) (by norm_num)).ne'
  have hm1 : (m : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
  have : ((bernoulli (m + 1) : ℚ) : ℂ) = ((((m + 1 : ℕ) : ℚ) / (2 ^ (m + 1) * (2 ^ (m + 1) - 1)) *
      ∑ k ∈ Icc 1 (m + 1), ∑ j ∈ range k,
        (-1 : ℚ) ^ (j + 1) * ((m + 1).choose k : ℚ) * (j : ℚ) ^ (m + 1 - 1) : ℚ) : ℂ) := by
    push_cast
    simp only [zero_add] at h ⊢
    have hs : ∑ k ∈ Icc 1 (m + 1), ∑ j ∈ range k, (-1 : ℂ) ^ (j + 1) * ((m + 1).choose k : ℂ) *
        (j : ℂ) ^ m = -∑ k ∈ Icc 1 (m + 1), ∑ j ∈ range k, (-1 : ℂ) ^ j * ((m + 1).choose k : ℂ) *
        (j : ℂ) ^ m := by
      rw [← sum_neg_distrib]; refine sum_congr rfl fun k _ => ?_
      rw [← sum_neg_distrib]; refine sum_congr rfl fun j _ => ?_
      ring
    rw [hs]
    generalize (∑ k ∈ Icc 1 (m + 1), ∑ j ∈ range k, (-1 : ℂ) ^ j * ((m + 1).choose k : ℂ) *
        (j : ℂ) ^ m) = S at h ⊢
    rw [pow_succ] at h h3 ⊢
    generalize (2 : ℂ) ^ m = P at h h2 h3 ⊢
    have h4 : P * 2 - 1 ≠ 0 := h3
    field_simp at h
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (mul_ne_zero h2 two_ne_zero) h4)]
    linear_combination h
  exact_mod_cast this

/-- **DLMF 24.6.12**: `E₂ₙ = ∑_{k=0}^{2n} 2⁻ᵏ ∑_{j=0}^{k} (-1)ʲ (k choose j)(1+2j)^{2n}`, all
`n ≥ 0`. -/
@[dlmf 24.6.E12]
theorem eulerNumber_two_mul_eq_explicit₁₂ (n : ℕ) :
    eulerNumber (2 * n) = ∑ k ∈ range (2 * n + 1), 1 / (2 : ℚ) ^ k *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * (1 + 2 * (j : ℚ)) ^ (2 * n) := by
  have h := q24a_eulerPolyE_newton (2 * n) (1 / 2)
  rw [eulerPolyE_half] at h
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have : ((eulerNumber (2 * n) : ℚ) : ℂ) = ((∑ k ∈ range (2 * n + 1), 1 / (2 : ℚ) ^ k *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) *
        (1 + 2 * (j : ℚ)) ^ (2 * n) : ℚ) : ℂ) := by
    push_cast
    rw [div_eq_iff h2] at h
    rw [h, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show (1 / 2 : ℂ) + j = (1 + 2 * j) / 2 by ring, div_pow]
    field_simp
  exact_mod_cast this

end DLMF.BernoulliEuler
