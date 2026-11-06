/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ClausenKernel

/-!
# The three-term recurrence of the q-Clausen four-phi-three sum

A finite rational certificate gives the recurrence of the continuous q-ultraspherical
normalization appearing on the left of DLMF 17.9.18. The proof combines the upper
parameters before dividing, retaining their terminating zeros.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.ClausenRecurrence

/-- The certificate multiplier for the three-term recurrence of the first kernel. -/
def firstCertificateFactor (β q N t : ℂ) : ℂ :=
  (N * q ^ 2 * (N * β * q - 1) * (N * β ^ 2 * q - 1) / (N * q ^ 2 - 1)) *
    (1 - β ^ 2 * t ^ 2 / q) * (1 + β * t / q) * (1 - t) /
      (t * (1 - β ^ 2 * N * t) * (1 - β ^ 2 * N * q * t))

/-- Rational verification of the first finite telescoping certificate. -/
lemma first_certificate_algebra (S β q N t : ℂ)
    (hd : ∀ z ∈ [q, N, t, N * q - 1, N * q ^ 2 - 1,
      1 - β ^ 2 * N * t, 1 - β ^ 2 * N * q * t, 1 - β ^ 2 * N * q ^ 2 * t,
      1 - β ^ 2 * q * t ^ 2, 1 + β * t, 1 - q * t], z ≠ 0) :
    (1 - β ^ 2 * N * q) - S * (1 - β * N * q) *
        shiftProduct q (β ^ 2) (N * q) 1 t + β * (1 - N * q) *
        shiftProduct q (β ^ 2) N 2 t =
      firstCertificateFactor β q N (q * t) *
          (q * (1 - (N * q ^ 2)⁻¹ * t) * (1 - β ^ 2 * (N * q ^ 2) * t) *
            (1 - S * t + β * t ^ 2)) /
          ((1 - β ^ 2 * q * t ^ 2) * (1 + β * t) * (1 - q * t)) -
        firstCertificateFactor β q N t := by
  have hq := hd q (by simp)
  have hN := hd N (by simp)
  have ht := hd t (by simp)
  have hN1 := hd (N * q - 1) (by simp)
  have hN2 := hd (N * q ^ 2 - 1) (by simp)
  have hN1' : -1 + N * q ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hN1
  have hN2' : -1 + N * q ^ 2 ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hN2
  have hD0 := hd (1 - β ^ 2 * N * t) (by simp)
  have hD1 := hd (1 - β ^ 2 * N * q * t) (by simp)
  have hD2 := hd (1 - β ^ 2 * N * q ^ 2 * t) (by simp)
  have hW0 := hd (1 - β ^ 2 * q * t ^ 2) (by simp)
  have hW1 := hd (1 + β * t) (by simp)
  have hW2 := hd (1 - q * t) (by simp)
  have hD1' : 1 - β ^ 2 * N * (q * t) ≠ 0 := by convert hD1 using 1; ring
  have hD2' : 1 - β ^ 2 * N * q * (q * t) ≠ 0 := by convert hD2 using 1; ring
  simp only [shiftProduct, firstCertificateFactor, prod_range_succ, prod_range_zero,
    pow_zero, pow_one, mul_one]
  field_simp
  ring_nf
  field_simp
  ring

/-- The finite first sum of the q-Clausen identity. -/
def firstSum (S β q : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (n + 1), firstKernel S β q (q ^ n) k

/-- The finite certificate at natural powers of the base. -/
def firstCertificate (S β q : ℂ) (n k : ℕ) : ℂ :=
  firstCertificateFactor β q (q ^ n) (q ^ k) * firstKernel S β q (q ^ (n + 2)) k

/-- The certificate denominators avoid zero under the fixed square-parameter regularity. -/
lemma first_certificate_regular {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (n k : ℕ) :
    ∀ z ∈ [q, q ^ n, q ^ k, q ^ n * q - 1, q ^ n * q ^ 2 - 1,
      1 - β ^ 2 * q ^ n * q ^ k, 1 - β ^ 2 * q ^ n * q * q ^ k,
      1 - β ^ 2 * q ^ n * q ^ 2 * q ^ k, 1 - β ^ 2 * q * (q ^ k) ^ 2,
      1 + β * q ^ k, 1 - q * q ^ k], z ≠ 0 := by
  have hf (j : ℕ) : 1 - β ^ 2 * q ^ j ≠ 0 := sub_ne_zero.mpr (hB j).symm
  have hN (j : ℕ) (hj : 0 < j) : q ^ n * q ^ j - 1 ≠ 0 := by
    rw [← pow_add]
    intro he
    have h : ‖q ^ (n + j)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [sub_eq_zero.mp he, norm_one] at h
    exact lt_irrefl _ h
  have hp : q ^ (2 * k) = (q ^ k) ^ 2 := by rw [Nat.mul_comm 2 k, pow_mul]
  have hW0 : 1 - β ^ 2 * q * (q ^ k) ^ 2 ≠ 0 := by
    have heq : β ^ 2 * q * (q ^ k) ^ 2 = β ^ 2 * q ^ (2 * k + 1) := by
      rw [pow_succ q (2 * k), hp]
      ring
    simpa only [heq] using hf (2 * k + 1)
  have hW1 : 1 + β * q ^ k ≠ 0 := by
    intro he
    apply hB (2 * k)
    rw [hp]
    linear_combination (β * q ^ k - 1) * he
  simp only [List.forall_mem_cons]
  refine ⟨hq0, pow_ne_zero n hq0, pow_ne_zero k hq0, ?_, hN 2 (by omega), ?_, ?_, ?_,
    hW0, hW1, one_sub_mul_pow_ne_zero_of_norm hq hq k, by simp⟩
  · simpa only [pow_one] using hN 1 (by omega)
  · simpa only [pow_add, mul_assoc] using hf (n + k)
  · simpa only [pow_add, pow_one, mul_assoc] using hf (n + 1 + k)
  · simpa only [pow_add, mul_assoc] using hf (n + 2 + k)

/-- The contiguous difference of the first kernel is the difference of two certificates. -/
lemma firstKernel_contiguous {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) (n k : ℕ) :
    (1 - β ^ 2 * q ^ (n + 1)) * firstKernel S β q (q ^ (n + 2)) k -
        S * (1 - β * q ^ (n + 1)) * firstKernel S β q (q ^ (n + 1)) k +
        β * (1 - q ^ (n + 1)) * firstKernel S β q (q ^ n) k =
      firstCertificate S β q n (k + 1) - firstCertificate S β q n k := by
  have h0 := weightedKernel_eq_shiftProduct hq0 hq hB (firstWeight S β q) n 2 k
  have h1 := weightedKernel_eq_shiftProduct hq0 hq hB (firstWeight S β q) (n + 1) 1 k
  change firstKernel S β q (q ^ n) k =
    firstKernel S β q (q ^ (n + 2)) k * shiftProduct q (β ^ 2) (q ^ n) 2 (q ^ k) at h0
  change firstKernel S β q (q ^ (n + 1)) k =
    firstKernel S β q (q ^ (n + 2)) k * shiftProduct q (β ^ 2) (q ^ (n + 1)) 1 (q ^ k) at h1
  rw [h0, h1]
  unfold firstCertificate
  rw [firstKernel_succ]
  have hA := first_certificate_algebra S β q (q ^ n) (q ^ k)
    (first_certificate_regular hq0 hq hB n k)
  rw [pow_add q n 2, pow_succ q n, pow_succ' q k]
  linear_combination (firstKernel S β q (q ^ n * q ^ 2) k) * hA

/-- The truncating upper factor makes the first kernel vanish beyond its natural endpoint. -/
lemma firstKernel_pow_eq_zero {S β q : ℂ} (hq0 : q ≠ 0) {n k : ℕ} (hk : n < k) :
    firstKernel S β q (q ^ n) k = 0 := by
  simp only [firstKernel, weightedKernel, qPochhammer_recip_pow_eq_zero hq0 hk, zero_mul]

/-- The first certificate vanishes at its lower endpoint. -/
@[simp] lemma firstCertificate_zero (S β q : ℂ) (n : ℕ) : firstCertificate S β q n 0 = 0 := by
  simp [firstCertificate, firstCertificateFactor]

/-- The first certificate vanishes beyond the terminating endpoint. -/
lemma firstCertificate_end {S β q : ℂ} (hq0 : q ≠ 0) (n : ℕ) :
    firstCertificate S β q n (n + 3) = 0 := by
  unfold firstCertificate
  rw [firstKernel_pow_eq_zero hq0 (show n + 2 < n + 3 by omega), mul_zero]

/-- The first finite sum may be extended through any larger endpoint. -/
lemma firstSum_eq_range_of_le {q : ℂ} (hq0 : q ≠ 0) (S β : ℂ) {n N : ℕ} (hn : n ≤ N) :
    firstSum S β q n = ∑ k ∈ range (N + 1), firstKernel S β q (q ^ n) k := by
  unfold firstSum
  apply sum_subset (range_mono (Nat.add_le_add_right hn 1))
  intro k hk hkn
  apply firstKernel_pow_eq_zero hq0
  simp only [mem_range] at hk hkn
  omega

/-- The terminating four-phi-three sum satisfies the continuous q-ultraspherical recurrence. -/
theorem firstSum_contiguous {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) (n : ℕ) :
    (1 - β ^ 2 * q ^ (n + 1)) * firstSum S β q (n + 2) =
      S * (1 - β * q ^ (n + 1)) * firstSum S β q (n + 1) -
        β * (1 - q ^ (n + 1)) * firstSum S β q n := by
  have hs : (1 - β ^ 2 * q ^ (n + 1)) * firstSum S β q (n + 2) -
      S * (1 - β * q ^ (n + 1)) * firstSum S β q (n + 1) +
      β * (1 - q ^ (n + 1)) * firstSum S β q n = 0 := by
    calc
      _ = ∑ k ∈ range (n + 3), ((1 - β ^ 2 * q ^ (n + 1)) *
          firstKernel S β q (q ^ (n + 2)) k - S * (1 - β * q ^ (n + 1)) *
          firstKernel S β q (q ^ (n + 1)) k +
          β * (1 - q ^ (n + 1)) * firstKernel S β q (q ^ n) k) := by
        rw [firstSum_eq_range_of_le hq0 S β (show n + 1 ≤ n + 2 by omega),
          firstSum_eq_range_of_le hq0 S β (show n ≤ n + 2 by omega)]
        simp only [firstSum, mul_sum, sum_sub_distrib, sum_add_distrib]
      _ = ∑ k ∈ range (n + 3), (firstCertificate S β q n (k + 1) -
          firstCertificate S β q n k) :=
        sum_congr rfl fun k _ => firstKernel_contiguous hq0 hq hB S n k
      _ = 0 := by rw [sum_range_sub, firstCertificate_end hq0, firstCertificate_zero, sub_self]
  linear_combination hs

end DLMF.QHypergeometric.ClausenRecurrence
