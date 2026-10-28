/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.QBinomial

/-!
# The `q`-Pfaff–Saalschütz sum (AAR §10.?, Gasper–Rahman (II.12))

The terminating balanced `₃φ₂` sum, proved here as a polynomial identity valid for every `q`:
for all `q, x, r, s`,
`∑_m [n m]_q (r;q)_m (s;q)_m (x;q)_{n-m} (xrsq^m;q)_{n-m} x^m = (xr;q)_n (xs;q)_n`.
Dividing by `(q;q)_n (xrs q;q)_n` gives the usual quotient form, in which `x = aq/(rs)`; this is
the form used for Bailey's lemma.

The proof is by induction on `n`, generalizing `x`, with the explicit telescoping certificate
`G(m) = -[n, m-1]_q x^m (r;q)_m (s;q)_m (xq;q)_{n+1-m} (xrsq^m;q)_{n+1-m}`.

## Main results

* `qBinom_succ_succ'`: the second `q`-Pascal rule `[n+1, k+1]_q = [n, k+1]_q + q^{n-k} [n, k]_q`.
* `sum_qBinom_saalschutz`: the polynomial form of the `q`-Pfaff–Saalschütz sum.
* `sum_saalschutz_div`: the quotient form used for Bailey's lemma.
-/

@[expose] public section

open Complex Finset

noncomputable section

namespace DLMF.QSeries

/-- The second `q`-Pascal rule `[n+1, k+1]_q = [n, k+1]_q + q^{n-k} [n, k]_q`, valid for all
`n, k` (both sides vanish when `k > n`). -/
@[dlmf 17.2.E32 "exact: second polynomial q-Pascal rule; local adapter proved"]
theorem qBinom_succ_succ' (q : ℂ) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n (k + 1) + q ^ (n - k) * qBinom q n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [qBinom_succ_succ]
  | succ n ih =>
    cases k with
    | zero =>
      have h0 := ih 0
      simp only [qBinom_succ_succ, qBinom_zero_right, Nat.sub_zero, zero_add, pow_one] at h0 ⊢
      rw [pow_succ]
      linear_combination q * h0
    | succ k =>
      rcases lt_or_ge k n with hk | hk
      · obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
        have h1 := ih k
        have h2 := ih (k + 1)
        have hD1 := qBinom_succ_succ q (k + 1 + d) k
        have hD2 := qBinom_succ_succ q (k + 1 + d) (k + 1)
        rw [show k + 1 + d - k = d + 1 by omega] at h1
        rw [show k + 1 + d - (k + 1) = d by omega] at h2
        rw [show k + 1 + d + 1 - (k + 1) = d + 1 by omega,
          qBinom_succ_succ q (k + 1 + d + 1) (k + 1)]
        linear_combination (-q ^ (d + 1)) * hD1 + h1 - hD2 + q ^ (k + 2) * h2
      · obtain ⟨e, rfl⟩ : ∃ e, k = n + e := ⟨k - n, by omega⟩
        rcases e with _ | e
        · rw [Nat.add_zero, show n + 1 - (n + 1) = 0 by omega, qBinom_self, qBinom_self,
            qBinom_eq_zero_of_lt q (by omega : n + 1 < n + 1 + 1)]
          ring
        · rw [qBinom_eq_zero_of_lt q (by omega : n + 1 + 1 < n + (e + 1) + 1 + 1),
            qBinom_eq_zero_of_lt q (by omega : n + 1 < n + (e + 1) + 1 + 1),
            qBinom_eq_zero_of_lt q (by omega : n + 1 < n + (e + 1) + 1)]
          ring

/-- The summand of the polynomial `q`-Pfaff–Saalschütz sum. -/
private def saalTerm (q r s : ℂ) (n : ℕ) (x : ℂ) (m : ℕ) : ℂ :=
  qBinom q n m * qPochhammer r q m * qPochhammer s q m * qPochhammer x q (n - m) *
    qPochhammer (x * r * s * q ^ m) q (n - m) * x ^ m

/-- The telescoping certificate. -/
private def saalCert (q r s : ℂ) (n : ℕ) (x : ℂ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => -(qBinom q n k * x ^ (k + 1) * qPochhammer r q (k + 1) *
      qPochhammer s q (k + 1) * qPochhammer (x * q) q (n - k) *
      qPochhammer (x * r * s * q ^ (k + 1)) q (n - k))

/-- One step of the recursion in `n` for the `q`-Saalschütz sum, as a telescoping difference
of `saalCert`. -/
private lemma saal_step (q r s x : ℂ) (n m : ℕ) (hm : m ≤ n + 1) :
    saalTerm q r s (n + 1) x m - (1 - x * r) * (1 - x * s) * saalTerm q r s n (x * q) m =
      saalCert q r s n x (m + 1) - saalCert q r s n x m := by
  rcases m with _ | k
  · simp only [saalTerm, saalCert, qBinom_zero_right, qPochhammer_zero, pow_zero, mul_one,
      Nat.sub_zero, zero_add, pow_one, sub_zero]
    rw [qPochhammer_succ' x q n, qPochhammer_succ' (x * r * s) q n,
      show x * q * r * s = x * r * s * q by ring]
    simp only [qPochhammer_one]
    ring
  rcases eq_or_lt_of_le hm with h | h
  · obtain rfl : k = n := by omega
    simp only [saalTerm, saalCert]
    rw [qBinom_eq_zero_of_lt q (Nat.lt_succ_self k), qBinom_self, qBinom_self, Nat.sub_self,
      Nat.sub_self]
    simp only [qPochhammer_zero]
    ring
  obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by omega⟩
  have e1 : k + 1 + j + 1 - (k + 1) = j + 1 := by omega
  have e2 : k + 1 + j - (k + 1) = j := by omega
  have e3 : k + 1 + j - k = j + 1 := by omega
  have hP1 := qBinom_succ_succ q (k + 1 + j) k
  have hP2 := qBinom_succ_succ' q (k + 1 + j) k
  rw [e3] at hP2
  simp only [saalCert, saalTerm, e1, e2, e3]
  rw [qPochhammer_succ' x q j, qPochhammer_succ' (x * r * s * q ^ (k + 1)) q j,
    qPochhammer_succ (x * q) q j, qPochhammer_succ r q (k + 1), qPochhammer_succ s q (k + 1),
    show x * q * r * s * q ^ (k + 1) = x * r * s * q ^ (k + 1) * q by ring,
    show x * r * s * q ^ (k + 1 + 1) = x * r * s * q ^ (k + 1) * q by ring]
  linear_combination
    ((1 - x) * (1 - x * r * s * q ^ (k + 1)) + x * (1 - x * r * s * q ^ (k + 1))) *
        (qPochhammer r q (k + 1) * qPochhammer s q (k + 1) * qPochhammer (x * q) q j *
          qPochhammer (x * r * s * q ^ (k + 1) * q) q j * x ^ (k + 1)) * hP1 -
      x * (1 - x * r * s * q ^ (k + 1)) *
        (qPochhammer r q (k + 1) * qPochhammer s q (k + 1) * qPochhammer (x * q) q j *
          qPochhammer (x * r * s * q ^ (k + 1) * q) q j * x ^ (k + 1)) * hP2

/-- The `q`-Pfaff–Saalschütz sum in polynomial form, valid for all `q, x, r, s`:
`∑_m [n m]_q (r;q)_m (s;q)_m (x;q)_{n-m} (xrsq^m;q)_{n-m} x^m = (xr;q)_n (xs;q)_n`. -/
theorem sum_qBinom_saalschutz (q x r s : ℂ) (n : ℕ) :
    ∑ m ∈ range (n + 1), qBinom q n m * qPochhammer r q m * qPochhammer s q m *
        qPochhammer x q (n - m) * qPochhammer (x * r * s * q ^ m) q (n - m) * x ^ m =
      qPochhammer (x * r) q n * qPochhammer (x * s) q n := by
  change ∑ m ∈ range (n + 1), saalTerm q r s n x m = _
  induction n generalizing x with
  | zero => simp [saalTerm]
  | succ n ih =>
    have hsum : ∑ m ∈ range (n + 1 + 1),
        (saalTerm q r s (n + 1) x m - (1 - x * r) * (1 - x * s) * saalTerm q r s n (x * q) m) =
          saalCert q r s n x (n + 1 + 1) - saalCert q r s n x 0 := by
      rw [← sum_range_sub (saalCert q r s n x)]
      exact sum_congr rfl fun m hm => saal_step q r s x n m (by simp at hm; omega)
    have hlast : saalTerm q r s n (x * q) (n + 1) = 0 := by
      simp [saalTerm, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
    have hcert : saalCert q r s n x (n + 1 + 1) = 0 := by
      simp [saalCert, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
    rw [sum_sub_distrib, ← mul_sum, sum_range_succ (fun m => saalTerm q r s n (x * q) m),
      hlast, add_zero, ih, hcert] at hsum
    simp only [saalCert, sub_zero] at hsum
    rw [sub_eq_zero.mp hsum, qPochhammer_succ' (x * r) q n, qPochhammer_succ' (x * s) q n,
      show x * q * r = x * r * q by ring, show x * q * s = x * s * q by ring]
    ring

/-- If `(x;q)_n ≠ 0` then `(x;q)_m ≠ 0` for every `m ≤ n`. -/
theorem qPochhammer_ne_zero_of_le {x q : ℂ} {m n : ℕ} (h : qPochhammer x q n ≠ 0) (hm : m ≤ n) :
    qPochhammer x q m ≠ 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [qPochhammer_add] at h
  exact left_ne_zero_of_mul h

/-- The `q`-Pfaff–Saalschütz sum in quotient form (Gasper–Rahman (II.12) with `a = r`,
`b = s`, `c = xrs`, after reversing the summation):
`∑_m (r;q)_m (s;q)_m (x;q)_{n-m} x^m / ((q;q)_{n-m} (q;q)_m (xrs;q)_m)
  = (xr;q)_n (xs;q)_n / ((q;q)_n (xrs;q)_n)`. -/
@[dlmf 17.7.E4 "equivalent finite q-Pfaff-Saalschutz identity after reversing the summation; quotient normalization differs"]
theorem sum_saalschutz_div (q x r s : ℂ) (n : ℕ) (hq : ∀ m ≤ n, qPochhammer q q m ≠ 0)
    (hA : qPochhammer (x * r * s) q n ≠ 0) :
    ∑ m ∈ range (n + 1), qPochhammer r q m * qPochhammer s q m * qPochhammer x q (n - m) *
        x ^ m / (qPochhammer q q (n - m) * qPochhammer q q m * qPochhammer (x * r * s) q m) =
      qPochhammer (x * r) q n * qPochhammer (x * s) q n /
        (qPochhammer q q n * qPochhammer (x * r * s) q n) := by
  rw [eq_div_iff (mul_ne_zero (hq n le_rfl) hA), sum_mul, ← sum_qBinom_saalschutz]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := by simpa [Nat.lt_succ_iff] using hm
  have hqm := hq m hmn
  have hqnm := hq (n - m) (Nat.sub_le n m)
  have hAm := qPochhammer_ne_zero_of_le hA hmn
  have hB := qBinom_mul_qPochhammer q m (n - m)
  have hS := qPochhammer_add (x * r * s) q m (n - m)
  rw [Nat.add_sub_cancel' hmn] at hB hS
  rw [← hB, hS]
  field_simp

end DLMF.QSeries

end
