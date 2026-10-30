/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Calculus
public import DLMF.QSeries.Pochhammer

/-!
# Gaussian `q`-binomial coefficients (Duverney §10.1.1)

`qBinom q n k = [n k]_q` is defined by the `q`-Pascal rule (Duverney (10.6)–(10.7)). This file
proves `[n k]_1 = C(n,k)`, the product form `[k+m, k]_q (q;q)_k (q;q)_m = (q;q)_{k+m}`
(Duverney (10.4)), and Cauchy's finite `q`-binomial theorem
`(x;q)_n = ∑_k [n k]_q (-1)^k q^{k(k-1)/2} x^k` (Duverney (10.8)), and the limit
`[n k]_q → C(n,k)` as `q → 1` (10.5). Mathlib has no Gaussian binomial coefficients.
-/

@[expose] public section

open Complex Finset

noncomputable section

namespace DLMF.QSeries

/-- `[n 0]_q = 1`. -/
@[simp] theorem qBinom_zero_right (q : ℂ) (n : ℕ) : qBinom q n 0 = 1 := by
  cases n <;> rfl

/-- `[0, k+1]_q = 0`. -/
@[simp] theorem qBinom_zero_succ (q : ℂ) (k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

/-- The `q`-Pascal rule `[n+1, k+1]_q = [n, k]_q + q^{k+1} [n, k+1]_q` (Duverney (10.7)). -/
@[dlmf 17.2.E31 "exact: first polynomial q-Pascal rule after successor reindexing"]
theorem qBinom_succ_succ (q : ℂ) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/-- `[n k]_q = 0` for `k > n`. -/
theorem qBinom_eq_zero_of_lt (q : ℂ) {n k : ℕ} (h : n < k) : qBinom q n k = 0 := by
  induction n generalizing k with
  | zero => obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0); rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [qBinom_succ_succ, ih (by omega), ih (by omega)]; ring

/-- `[n n]_q = 1` (Duverney (10.6)). -/
@[simp] theorem qBinom_self (q : ℂ) (n : ℕ) : qBinom q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qBinom_succ_succ, ih, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]; ring

/-- At `q = 1` the Gaussian coefficients are the binomial coefficients. -/
theorem qBinom_one (n k : ℕ) : qBinom 1 n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => rw [qBinom_succ_succ, ih, ih, Nat.choose_succ_succ]; push_cast; ring

/-- Splitting the first factor: `(x;q)_{n+1} = (1-x)(xq;q)_n`. -/
theorem qPochhammer_succ' (x q : ℂ) (n : ℕ) :
    qPochhammer x q (n + 1) = (1 - x) * qPochhammer (x * q) q n := by
  induction n with
  | zero => simp [qPochhammer_succ]
  | succ n ih =>
    rw [qPochhammer_succ, ih, qPochhammer_succ]; ring

/-- The finite `q`-binomial theorem (Cauchy), Duverney (10.8):
`(x;q)_n = ∑_k [n k]_q (-1)^k q^{k(k-1)/2} x^k`. -/
@[dlmf 17.2.E35 "exact: finite q-binomial theorem after expanding (-z)^j"]
theorem qPochhammer_eq_sum_qBinom (x q : ℂ) (n : ℕ) :
    qPochhammer x q n =
      ∑ k ∈ range (n + 1), qBinom q n k * (-1) ^ k * q ^ k.choose 2 * x ^ k := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hc (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    set g : ℕ → ℂ := fun k => qBinom q n k * (-1) ^ k * q ^ (k + 1).choose 2 * x ^ k
    have hL : qPochhammer x q (n + 1) =
        ∑ k ∈ range (n + 1), g k + ∑ k ∈ range (n + 1), qBinom q n k * (-1) ^ (k + 1) *
          q ^ (k + 1).choose 2 * x ^ (k + 1) := by
      rw [qPochhammer_succ', ih, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      simp only [g, hc]; ring
    rw [hL, sum_range_succ' g, sum_range_succ' _ (n + 1)]
    simp only [qBinom_succ_succ, add_mul, sum_add_distrib]
    rw [sum_range_succ (fun k => q ^ (k + 1) * qBinom q n (k + 1) * _ * _ * _),
      qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
    have hg : ∑ k ∈ range n, g (k + 1) = ∑ k ∈ range n, q ^ (k + 1) * qBinom q n (k + 1) *
        (-1) ^ (k + 1) * q ^ (k + 1).choose 2 * x ^ (k + 1) := by
      refine sum_congr rfl fun k _ => ?_
      simp only [g, hc (k + 1)]; ring
    rw [hg]
    simp [g]
    ring


/-- The product form `[k+m, k]_q (q;q)_k (q;q)_m = (q;q)_{k+m}` of Duverney (10.4). -/
theorem qBinom_mul_qPochhammer (q : ℂ) (k m : ℕ) :
    qBinom q (k + m) k * qPochhammer q q k * qPochhammer q q m = qPochhammer q q (k + m) := by
  induction h : k + m generalizing k m with
  | zero =>
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ m = 0 := by omega
    simp
  | succ n ih =>
    rcases k with _ | k
    · simp only [Nat.zero_add] at h; subst h; simp
    rcases m with _ | m
    · obtain rfl : k = n := by omega
      simp
    have h1 := ih k (m + 1) (by omega)
    have h2 := ih (k + 1) m (by omega)
    obtain rfl : n = k + m + 1 := by omega
    rw [qBinom_succ_succ, qPochhammer_succ q q (k + m + 1), qPochhammer_succ q q k,
      qPochhammer_succ q q m]
    rw [qPochhammer_succ q q m] at h1
    rw [qPochhammer_succ q q k] at h2
    linear_combination (1 - q * q ^ k) * h1 + q ^ (k + 1) * (1 - q * q ^ m) * h2

/-- `q ↦ [n k]_q` is continuous (it is a polynomial in `q`). -/
theorem continuous_qBinom (n k : ℕ) : Continuous fun q : ℂ => qBinom q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp only [qBinom_zero_right, qBinom_zero_succ] <;> fun_prop
  | succ n ih =>
    cases k with
    | zero => simp only [qBinom_zero_right]; fun_prop
    | succ k => simp only [qBinom_succ_succ]; exact (ih k).add ((continuous_pow _).mul (ih (k + 1)))

/-- `[n k]_q → C(n, k)` as `q → 1` (Duverney (10.5)). -/
@[dlmf 17.2.E28 "exact: complex q tends to1, using polynomial Gaussian binomials"]
theorem tendsto_qBinom (n k : ℕ) :
    Filter.Tendsto (fun q : ℂ => qBinom q n k) (nhds 1) (nhds (n.choose k : ℂ)) := by
  rw [← qBinom_one]
  exact (continuous_qBinom n k).tendsto 1

end DLMF.QSeries

end
