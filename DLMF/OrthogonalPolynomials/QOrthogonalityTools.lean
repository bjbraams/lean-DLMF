/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Saalschutz
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Tools for orthogonality of `q`-families

Helpers for DLMF §§18.27–18.28:

* the balanced `q`-Pfaff–Saalschütz sum in the standard form
  `₃φ₂(q^{-n}, r, s; c, e; q, q)` with `c e = q^{1-n} r s` (`qOrth_saalschutz`), obtained
  termwise from the polynomial form `DLMF.QSeries.sum_qBinom_saalschutz`;
* moments of the little `q`-Jacobi weight by the `q`-binomial theorem
  (`qOrth_littleQJacobi_moment`) and the vanishing of the resulting moment sums
  (`qOrth_littleQJacobi_sum_zero`).
-/

@[expose] public section

open Complex Finset DLMF.QSeries

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The ratio rule `[n, m+1]_q (1 - q^{m+1}) = [n, m]_q (1 - q^{n-m})`. -/
theorem qOrth_qBinom_succ_ratio {q : ℂ} (hq : ‖q‖ < 1) (m d : ℕ) :
    qBinom q (m + 1 + d) (m + 1) * (1 - q * q ^ m) =
      qBinom q (m + 1 + d) m * (1 - q * q ^ d) := by
  have h1 := qBinom_mul_qPochhammer q (m + 1) d
  have h2 := qBinom_mul_qPochhammer q m (d + 1)
  rw [show m + (d + 1) = m + 1 + d by ring] at h2
  rw [qPochhammer_succ q q m] at h1
  rw [qPochhammer_succ q q d] at h2
  have hm := qPochhammer_self_ne_zero hq m
  have hd := qPochhammer_self_ne_zero hq d
  apply mul_right_cancel₀ (mul_ne_zero hm hd)
  linear_combination h1 - h2

/-- Term conversion between the reversed polynomial form and the `q^{-n}` form. -/
theorem qOrth_term {q x c : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hx : x ≠ 0) {n : ℕ}
    (hc : c * x * q ^ n = q) {m : ℕ} (hm : m ≤ n) :
    qBinom q n m * qPochhammer x q (n - m) * x ^ m * qPochhammer c q m * qPochhammer q q m =
      qPochhammer x q n * qPochhammer (q⁻¹ ^ n) q m * q ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih := ih (by omega)
    obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - (m + 1), by omega⟩
    have e1 : m + 1 + d - m = d + 1 := by omega
    have e2 : m + 1 + d - (m + 1) = d := by omega
    rw [e1, qPochhammer_succ x q d] at ih
    rw [e2]
    have hR := qOrth_qBinom_succ_ratio hq m d
    have hX : x * (1 - c * q ^ m) = -(q⁻¹ ^ d) * (1 - x * q ^ d) := by
      have hc' : c = q / (x * q ^ (m + 1 + d)) := by
        field_simp; linear_combination hc
      subst hc'
      simp only [inv_pow]
      field_simp
      ring
    have hP : (1 - q⁻¹ ^ (m + 1 + d) * q ^ m) * q = -(q⁻¹ ^ d) * (1 - q * q ^ d) := by
      simp only [inv_pow]
      field_simp
      ring
    rw [qPochhammer_succ c q m, qPochhammer_succ (q⁻¹ ^ (m + 1 + d)) q m,
      qPochhammer_succ q q m]
    linear_combination
      (x * (1 - c * q ^ m) * (qPochhammer x q d * x ^ m * qPochhammer c q m *
        qPochhammer q q m)) * hR +
      (qBinom q (m + 1 + d) m * (1 - q * q ^ d) * (qPochhammer x q d * x ^ m *
        qPochhammer c q m * qPochhammer q q m)) * hX +
      (-(q⁻¹ ^ d) * (1 - q * q ^ d)) * ih -
      (qPochhammer x q (m + 1 + d) * qPochhammer (q⁻¹ ^ (m + 1 + d)) q m * q ^ m) * hP

/-- The balanced `q`-Pfaff–Saalschütz sum in the standard `q^{-n}` form: with
`c x qⁿ = q` and `x r s = e`,
`(x;q)_n (e;q)_n ₃φ₂(q^{-n}, r, s; c, e; q, q) = (xr;q)_n (xs;q)_n`. -/
theorem qOrth_saalschutz {q x c r s e : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hx : x ≠ 0) {n : ℕ}
    (hc : c * x * q ^ n = q) (he : x * r * s = e)
    (hcn : ∀ m ≤ n, qPochhammer c q m ≠ 0) (hen : qPochhammer e q n ≠ 0) :
    qPochhammer x q n * qPochhammer e q n *
        ∑ m ∈ range (n + 1), qPochhammer (q⁻¹ ^ n) q m * qPochhammer r q m *
          qPochhammer s q m * q ^ m /
            (qPochhammer q q m * qPochhammer c q m * qPochhammer e q m) =
      qPochhammer (x * r) q n * qPochhammer (x * s) q n := by
  rw [← sum_qBinom_saalschutz, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := by simpa [Nat.lt_succ_iff] using hm
  have hT := qOrth_term hq hq0 hx hc hmn
  have hS := qPochhammer_add e q m (n - m)
  rw [Nat.add_sub_cancel' hmn] at hS
  have hqm := qPochhammer_self_ne_zero hq m
  have hcm := hcn m hmn
  have hem := qPochhammer_ne_zero_of_le hen hmn
  subst he
  rw [hS]
  generalize qPochhammer (q⁻¹ ^ n) q m = P at hT ⊢
  field_simp
  linear_combination -(qPochhammer r q m * qPochhammer s q m *
    qPochhammer (x * r * s * q ^ m) q (n - m)) * hT

/-- Moments of the little `q`-Jacobi weight, by the `q`-binomial theorem. -/
theorem qOrth_littleQJacobi_moment {a b q : ℂ} (hq : ‖q‖ < 1) (haq : ‖a * q‖ < 1) (t : ℕ) :
    HasSum (fun y : ℕ => (q ^ t) ^ y *
      (qPochhammer (b * q) q y * (a * q) ^ y / qPochhammer q q y))
      (qPochhammerInf (a * b * q ^ (t + 2)) q / qPochhammerInf (a * q ^ (t + 1)) q) := by
  have hz : ‖a * q ^ (t + 1)‖ < 1 := by
    rw [pow_succ, ← mul_assoc, mul_comm a, mul_assoc, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg q) hq.le)) haq
  have hs := (summable_q_binomial_series (a := b * q) hq hz).hasSum
  rw [← q_binomial_theorem hq hz] at hs
  convert hs using 1
  · funext y
    simp only [mul_pow, ← pow_mul]
    ring_nf
  · congr 2; ring

/-- `(w;q)_n = 0` as soon as one factor `1 - w q^k`, `k < n`, vanishes. -/
theorem qOrth_qPochhammer_eq_zero {w q : ℂ} {n k : ℕ} (hk : k < n) (h : w * q ^ k = 1) :
    qPochhammer w q n = 0 := by
  rw [qPochhammer_eq_prod]
  exact prod_eq_zero (mem_range.mpr hk) (by rw [h, sub_self])

/-- `(w;q)_n ≠ 0` when no factor vanishes. -/
theorem qOrth_qPochhammer_ne_zero {w q : ℂ} {n : ℕ} (h : ∀ k < n, w * q ^ k ≠ 1) :
    qPochhammer w q n ≠ 0 := by
  rw [qPochhammer_eq_prod]
  exact prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (h k (mem_range.mp hk)).symm

/-- The moment sum behind the orthogonality of little `q`-Jacobi polynomials vanishes:
a balanced `₃φ₂` with a factor `(q^{i+1-n};q)_n = 0`. -/
theorem qOrth_littleQJacobi_sum_zero {a b q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (haq : ‖a * q‖ < 1) (hab : ∀ p : ℕ, a * b * q ^ (p + 2) ≠ 1)
    (ha1 : ∀ p : ℕ, a * q ^ (p + 1) ≠ 1) {i n : ℕ} (hin : i < n) :
    ∑ j ∈ range (n + 1), qPochhammer (q⁻¹ ^ n) q j * qPochhammer (a * b * q ^ (n + 1)) q j /
        (qPochhammer (a * q) q j * qPochhammer q q j) * q ^ j *
        (qPochhammerInf (a * b * q ^ (i + j + 2)) q / qPochhammerInf (a * q ^ (i + j + 1)) q) =
      0 := by
  set e := a * b * q ^ (i + 2)
  set r := a * q ^ (i + 1)
  set x := (a * q ^ n)⁻¹
  have hx : x ≠ 0 := inv_ne_zero (mul_ne_zero ha0 (pow_ne_zero _ hq0))
  have hen : ∀ k : ℕ, 1 - e * q ^ k ≠ 0 := fun k h => hab (i + k) (by
    simp only [e] at h; linear_combination -h)
  have hrn : ∀ k : ℕ, 1 - r * q ^ k ≠ 0 := fun k h => ha1 (i + k) (by
    simp only [r] at h; linear_combination -h)
  have hQ := qPochhammerInf_ne_zero hq hrn
  have hcn : ∀ m : ℕ, qPochhammer (a * q) q m ≠ 0 :=
    qPochhammer_ne_zero_of_factors hq (one_sub_mul_pow_ne_zero_of_norm haq hq)
  have hS := qOrth_saalschutz (q := q) (x := x) (c := a * q) (r := r) (s := a * b * q ^ (n + 1))
    (e := e) hq hq0 hx (n := n) (by simp only [x]; field_simp)
    (by simp only [x, r, e]; field_simp; ring) (fun m _ => hcn m)
    (qPochhammer_ne_zero_of_factors hq hen n)
  have hxr : qPochhammer (x * r) q n = 0 :=
    qOrth_qPochhammer_eq_zero (k := n - 1 - i) (by omega) (by
      simp only [x, r]
      rw [mul_assoc, mul_assoc a, ← pow_add, show i + 1 + (n - 1 - i) = n by omega]
      field_simp)
  have hxn : qPochhammer x q n ≠ 0 := qOrth_qPochhammer_ne_zero fun k hk h => ha1 (n - 1 - k) (by
    simp only [x] at h
    have : q ^ k * q ^ (n - 1 - k + 1) = q ^ n := by rw [← pow_add]; congr 1; omega
    field_simp at h
    apply mul_left_cancel₀ (pow_ne_zero k hq0)
    linear_combination a * this - h)
  rw [hxr, zero_mul] at hS
  have hsum := (mul_eq_zero.mp hS).resolve_left
    (mul_ne_zero hxn (qPochhammer_ne_zero_of_factors hq hen n))
  rw [← mul_zero (qPochhammerInf e q / qPochhammerInf r q), ← hsum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have h1 := qPochhammerInf_mul_qPochhammer (a := e) hq j
  have h2 := qPochhammerInf_mul_qPochhammer (a := r) hq j
  rw [show e * q ^ j = a * b * q ^ (i + j + 2) by simp only [e]; ring] at h1
  rw [show r * q ^ j = a * q ^ (i + j + 1) by simp only [r]; ring] at h2
  have hej := qPochhammer_ne_zero_of_factors hq hen j
  have hrj := qPochhammerInf_shift_ne_zero hq hrn j
  rw [show r * q ^ j = a * q ^ (i + j + 1) by simp only [r]; ring] at hrj
  have hqj := qPochhammer_self_ne_zero hq j
  have hcj := hcn j
  have hrj' := qPochhammer_ne_zero_of_factors hq hrn j
  rw [h1, h2]
  generalize qPochhammer (q⁻¹ ^ n) q j = P
  field_simp

end DLMF.OrthogonalPolynomials

end
