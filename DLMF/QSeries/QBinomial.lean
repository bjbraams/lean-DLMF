/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.CalculusProperties
public import DLMF.QSeries.Pochhammer

/-!
# Gaussian `q`-binomial coefficients (Duverney §10.1.1)

The Gaussian coefficient `qBinom q n k = [n k]_q` is defined by the `q`-Pascal rule
(Duverney (10.6)–(10.7)). Mathlib has no Gaussian binomial coefficients.

The special values, the `q`-Pascal rule and the limit `q → 1` are in
`DLMF.QSeries.Basic.CalculusProperties`.

## Main results

* `qBinom_mul_qPochhammer`: `[k+m, k]_q (q;q)_k (q;q)_m = (q;q)_{k+m}` (Duverney (10.4)).
* `qPochhammer_eq_sum_qBinom`: Cauchy's finite `q`-binomial theorem
  `(x;q)_n = ∑_k [n k]_q (-1)^k q^{k(k-1)/2} x^k` (Duverney (10.8), DLMF 17.2.35).
-/

@[expose] public section

open Complex Finset

noncomputable section

namespace DLMF.QSeries

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

end DLMF.QSeries

end
