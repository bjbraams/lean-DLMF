/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.ShiftedFactorials
public import DLMF.QSeries.QBinomial

/-!
# A finite telescoping recurrence for the q-Whipple sum

The terminating balanced sum in DLMF 17.7.11 satisfies a recurrence advancing the
truncation parameter by two. A rational telescoping certificate proves this recurrence
without division by any upper shifted factorial, so zero upper parameters are retained.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.WhippleRecurrence

/-- The q-Whipple summand, with its squared upper parameter written as `x`. -/
def kernel (e x q N : ℂ) (k : ℕ) : ℂ :=
  qPochhammer N⁻¹ q k * qPochhammer (N * q) q k * qPochhammer x (q ^ 2) k /
    (qPochhammer e q k * qPochhammer (x * q / e) q k *
      qPochhammer (q ^ 2) (q ^ 2) k) * q ^ k

/-- Interchanging a block of length two with an arbitrary shifted-factorial block. -/
lemma pochhammer_two_shift (a q : ℂ) (k : ℕ) :
    qPochhammer (a * q ^ 2) q k * (1 - a) * (1 - a * q) =
      qPochhammer a q k * (1 - a * q ^ k) * (1 - a * q ^ (k + 1)) := by
  have h1 := qPochhammer_add a q 2 k
  have h2 := qPochhammer_add a q k 2
  rw [Nat.add_comm 2 k] at h1
  rw [h2] at h1
  simp only [qPochhammer_succ, qPochhammer_zero, pow_zero, mul_one, one_mul] at h1
  rw [pow_succ q k]
  simp only [pow_one] at h1
  linear_combination -h1

/-- Changing the truncating parameter by two gives a polynomial factor in the index power. -/
lemma kernel_mul_shift {e x q N : ℂ} (hq : q ≠ 0) (hN : N ≠ 0) (k : ℕ) :
    kernel e x q N k * ((1 - N * q * q ^ k) * (1 - N * q ^ 2 * q ^ k)) =
      kernel e x q (N * q ^ 2) k * ((N * q ^ 2 - q ^ k) * (N * q - q ^ k)) := by
  have hneg := pochhammer_two_shift (N * q ^ 2)⁻¹ q k
  have hpos := pochhammer_two_shift (N * q) q k
  have harg : (N * q ^ 2)⁻¹ * q ^ 2 = N⁻¹ := by field_simp
  rw [harg] at hneg
  have hn : qPochhammer N⁻¹ q k * ((1 - N * q) * (1 - N * q ^ 2)) =
      qPochhammer (N * q ^ 2)⁻¹ q k * ((N * q ^ 2 - q ^ k) * (N * q - q ^ k)) := by
    field_simp at hneg
    simp only [one_div] at hneg
    rw [pow_succ q k] at hneg
    apply mul_left_cancel₀ hq
    linear_combination hneg
  have hp : qPochhammer (N * q ^ 2 * q) q k * ((1 - N * q) * (1 - N * q ^ 2)) =
      qPochhammer (N * q) q k * ((1 - N * q * q ^ k) * (1 - N * q ^ 2 * q ^ k)) := by
    rw [show N * q ^ 2 * q = N * q * q ^ 2 by ring]
    simp only [pow_succ] at hpos ⊢
    convert hpos using 1 <;> ring
  have hu : qPochhammer N⁻¹ q k * qPochhammer (N * q) q k *
      ((1 - N * q * q ^ k) * (1 - N * q ^ 2 * q ^ k)) =
      qPochhammer (N * q ^ 2)⁻¹ q k * qPochhammer (N * q ^ 2 * q) q k *
        ((N * q ^ 2 - q ^ k) * (N * q - q ^ k)) := by
    linear_combination (qPochhammer (N * q ^ 2 * q) q k) * hn -
      (qPochhammer N⁻¹ q k) * hp
  unfold kernel
  linear_combination
    (qPochhammer x (q ^ 2) k /
      (qPochhammer e q k * qPochhammer (x * q / e) q k *
        qPochhammer (q ^ 2) (q ^ 2) k) * q ^ k) * hu

/-- The rational telescoping certificate multiplying the summand at truncation `n+2`. -/
def certificateFactor (e x q N t : ℂ) : ℂ :=
  e * N * q ^ 2 * (N ^ 2 * q ^ 3 - 1) *
    (1 - e * t / q) * (1 - x * t / e) * (1 - t ^ 2) /
      (t * (1 - N * q * t) * (1 - N * q ^ 2 * t))

/-- The coefficient of the sum at truncation `n+2`. -/
def nextFactor (e x q N : ℂ) : ℂ := (1 - e * N * q) * (e - x * N * q ^ 2)

/-- The coefficient of the sum at truncation `n`. -/
def currentFactor (e x q N : ℂ) : ℂ := (e - N * q ^ 2) * (x - e * N * q)

/-- The summand has its rational index ratio, also at totalized lower parameters. -/
lemma kernel_succ (e x q N : ℂ) (k : ℕ) :
    kernel e x q N (k + 1) = kernel e x q N k *
      (q * (1 - N⁻¹ * q ^ k) * (1 - N * q * q ^ k) * (1 - x * (q ^ k) ^ 2)) /
        ((1 - e * q ^ k) * (1 - x * q * q ^ k / e) * (1 - q ^ 2 * (q ^ k) ^ 2)) := by
  have hp : (q ^ 2) ^ k = (q ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  unfold kernel
  simp only [qPochhammer_succ, pow_succ q k, hp]
  rw [show x * q / e * q ^ k = x * q * q ^ k / e by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The rational certificate telescopes the contiguous difference of q-Whipple summands. -/
lemma kernel_contiguous {e x q N : ℂ} (he : e ≠ 0) (hq0 : q ≠ 0) (hN : N ≠ 0)
    (hq : ‖q‖ < 1) (hE : ∀ j, qPochhammer e q j ≠ 0)
    (hX : ∀ j, qPochhammer (x * q / e) q j ≠ 0) (k : ℕ)
    (h1 : 1 - N * q * q ^ k ≠ 0) (h2 : 1 - N * q ^ 2 * q ^ k ≠ 0)
    (h3 : 1 - N * q ^ 3 * q ^ k ≠ 0) :
    nextFactor e x q N * kernel e x q (N * q ^ 2) k -
        currentFactor e x q N * kernel e x q N k =
      certificateFactor e x q N (q ^ (k + 1)) * kernel e x q (N * q ^ 2) (k + 1) -
        certificateFactor e x q N (q ^ k) * kernel e x q (N * q ^ 2) k := by
  have hK : kernel e x q N k = kernel e x q (N * q ^ 2) k *
      ((N * q ^ 2 - q ^ k) * (N * q - q ^ k)) /
        ((1 - N * q * q ^ k) * (1 - N * q ^ 2 * q ^ k)) :=
    (eq_div_iff (mul_ne_zero h1 h2)).mpr (kernel_mul_shift hq0 hN k)
  rw [hK, kernel_succ]
  have ht := pow_ne_zero k hq0
  have h2' : 1 - N * q * (q * q ^ k) ≠ 0 := by convert h2 using 1; ring
  have h3' : 1 - N * q ^ 2 * (q * q ^ k) ≠ 0 := by convert h3 using 1; ring
  have hEf : 1 - e * q ^ k ≠ 0 := by
    have h := hE (k + 1)
    rw [qPochhammer_succ] at h
    exact right_ne_zero_of_mul h
  have hXf : 1 - x * q * q ^ k / e ≠ 0 := by
    have h := hX (k + 1)
    rw [qPochhammer_succ] at h
    convert right_ne_zero_of_mul h using 1; ring
  have hxl : -(q * q ^ k * x) + e ≠ 0 := by
    intro hl
    apply hXf
    field_simp
    linear_combination hl
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hp : (q ^ 2) ^ k = (q ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  have hQf : 1 - q ^ 2 * (q ^ k) ^ 2 ≠ 0 := by
    have h := qPochhammer_self_ne_zero hQ (k + 1)
    rw [qPochhammer_succ, hp] at h
    exact right_ne_zero_of_mul h
  unfold nextFactor currentFactor certificateFactor
  rw [pow_succ' q k]
  have hD0 : 1 - N * q * q ^ k - N * q ^ 2 * q ^ k +
      N ^ 2 * q ^ 3 * q ^ (k * 2) ≠ 0 := by
    convert mul_ne_zero h1 h2 using 1; ring
  have hD3L : -(N * q ^ 3 * q ^ k * e) + N * q ^ 4 * q ^ (k * 2) * x -
      q * q ^ k * x + e ≠ 0 := by
    convert mul_ne_zero h3 hxl using 1; ring
  field_simp
  ring_nf
  field_simp [hD0, hD3L, hxl]
  ring

/-- The terminating q-Whipple sum through its natural truncation index. -/
def finiteSum (e x q : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (n + 1), kernel e x q (q ^ n) k

/-- The telescoping certificate at natural powers of the base. -/
def certificate (e x q : ℂ) (n k : ℕ) : ℂ :=
  certificateFactor e x q (q ^ n) (q ^ k) * kernel e x q (q ^ n * q ^ 2) k

/-- The upper reciprocal power truncates the summand even at totalized lower parameters. -/
lemma kernel_pow_eq_zero {e x q : ℂ} (hq0 : q ≠ 0) {n k : ℕ} (hk : n < k) :
    kernel e x q (q ^ n) k = 0 := by
  simp only [kernel, qPochhammer_recip_pow_eq_zero hq0 hk, zero_mul, zero_div]

/-- The lower endpoint of the telescoping certificate vanishes. -/
@[simp] lemma certificate_zero (e x q : ℂ) (n : ℕ) : certificate e x q n 0 = 0 := by
  simp [certificate, certificateFactor]

/-- The upper endpoint lies beyond the terminating factor. -/
lemma certificate_end {e x q : ℂ} (hq0 : q ≠ 0) (n : ℕ) :
    certificate e x q n (n + 3) = 0 := by
  unfold certificate
  rw [← pow_add, kernel_pow_eq_zero hq0 (show n + 2 < n + 3 by omega), mul_zero]

/-- The finite q-Whipple sum satisfies its two-step recurrence at every regular parameter. -/
theorem finiteSum_contiguous {e x q : ℂ} (he : e ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hE : ∀ j, qPochhammer e q j ≠ 0)
    (hX : ∀ j, qPochhammer (x * q / e) q j ≠ 0) (n : ℕ) :
    nextFactor e x q (q ^ n) * finiteSum e x q (n + 2) =
      currentFactor e x q (q ^ n) * finiteSum e x q n := by
  have hstep (k : ℕ) : nextFactor e x q (q ^ n) * kernel e x q (q ^ (n + 2)) k -
      currentFactor e x q (q ^ n) * kernel e x q (q ^ n) k =
        certificate e x q n (k + 1) - certificate e x q n k := by
    have hf (r : ℕ) (hr : 0 < r) : 1 - q ^ n * q ^ r * q ^ k ≠ 0 := by
      rw [← pow_add, ← pow_add]
      intro hz
      have h : ‖q ^ (n + r + k)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
      rw [← sub_eq_zero.mp hz, norm_one] at h
      exact lt_irrefl _ h
    have h := kernel_contiguous he hq0 (pow_ne_zero n hq0) hq hE hX k
      (by simpa only [pow_one] using hf 1 (by omega)) (hf 2 (by omega)) (hf 3 (by omega))
    simpa only [certificate, ← pow_add] using h
  have hext : (∑ k ∈ range (n + 3), kernel e x q (q ^ n) k) = finiteSum e x q n := by
    rw [show n + 3 = (n + 1) + 1 + 1 by omega, sum_range_succ, sum_range_succ,
      kernel_pow_eq_zero hq0 (show n < n + 1 by omega),
      kernel_pow_eq_zero hq0 (show n < n + 1 + 1 by omega)]
    simp only [add_zero, finiteSum]
  apply sub_eq_zero.mp
  calc
    _ = ∑ k ∈ range (n + 3), (nextFactor e x q (q ^ n) * kernel e x q (q ^ (n + 2)) k -
        currentFactor e x q (q ^ n) * kernel e x q (q ^ n) k) := by
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hext]
      rfl
    _ = ∑ k ∈ range (n + 3), (certificate e x q n (k + 1) - certificate e x q n k) :=
      sum_congr rfl fun k _ => hstep k
    _ = 0 := by rw [sum_range_sub, certificate_end hq0, certificate_zero, sub_self]

/-- The q-Whipple finite sum at truncation zero. -/
@[simp] lemma finiteSum_zero (e x q : ℂ) : finiteSum e x q 0 = 1 := by
  simp [finiteSum, kernel]

/-- The q-Whipple finite sum at truncation one. -/
lemma finiteSum_one {e x q : ℂ} (he : e ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hE : ∀ j, qPochhammer e q j ≠ 0)
    (hX : ∀ j, qPochhammer (x * q / e) q j ≠ 0) :
    finiteSum e x q 1 = q * (1 - e / q) * (1 - x / e) /
      ((1 - e) * (1 - x * q / e)) := by
  have he1 : 1 - e ≠ 0 := by simpa only [qPochhammer_one] using hE 1
  have hx1 : 1 - x * q / e ≠ 0 := by simpa only [qPochhammer_one] using hX 1
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hq1 : 1 - q ^ 2 ≠ 0 := by
    simpa only [qPochhammer_one] using qPochhammer_self_ne_zero hQ 1
  have hxl : e - q * x ≠ 0 := by
    intro hl
    apply hx1
    field_simp
    linear_combination hl
  norm_num only [finiteSum, kernel, Nat.reduceAdd, sum_range_succ, sum_range_zero,
    qPochhammer_one, qPochhammer_zero, pow_zero, pow_one, one_mul, mul_one, one_div_one,
    add_zero, zero_add]
  field_simp
  ring

end DLMF.QHypergeometric.WhippleRecurrence
