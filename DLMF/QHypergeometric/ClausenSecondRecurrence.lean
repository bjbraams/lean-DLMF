/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ClausenFirstRecurrence

/-!
# The four-term recurrence of the q-Clausen square

Squaring the three-term recurrence gives a four-term recurrence. A second finite
rational certificate verifies the same recurrence for the five-phi-four kernel.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.ClausenRecurrence

/-- The leading factor of the three-term recurrence. -/
def leadingFactor (β q N : ℂ) : ℂ := 1 - β ^ 2 * N * q

/-- The middle factor independent of the symmetric sum of the upper parameters. -/
def middleFactor (β q N : ℂ) : ℂ := 1 - β * N * q

/-- The trailing factor of the three-term recurrence. -/
def lowerFactor (β q N : ℂ) : ℂ := β * (1 - N * q)

/-- The leading coefficient of the recurrence for the square. -/
def squareLeadingCoefficient (β q N : ℂ) : ℂ :=
  leadingFactor β q N * middleFactor β q N * (leadingFactor β q (N * q)) ^ 2

/-- The coefficient at the second latest index in the square recurrence. -/
def squareNextCoefficient (S β q N : ℂ) : ℂ :=
  leadingFactor β q N * middleFactor β q N * S ^ 2 * (middleFactor β q (N * q)) ^ 2 -
    (leadingFactor β q N) ^ 2 * middleFactor β q (N * q) * lowerFactor β q (N * q)

/-- The coefficient at the second index in the square recurrence. -/
def squareMiddleCoefficient (S β q N : ℂ) : ℂ :=
  leadingFactor β q N * middleFactor β q N * (lowerFactor β q (N * q)) ^ 2 -
    S ^ 2 * (middleFactor β q N) ^ 2 * middleFactor β q (N * q) * lowerFactor β q (N * q)

/-- The coefficient at the earliest index in the square recurrence. -/
def squareCurrentCoefficient (β q N : ℂ) : ℂ :=
  middleFactor β q (N * q) * lowerFactor β q (N * q) * (lowerFactor β q N) ^ 2

/-- The certificate multiplier for the four-term recurrence of the second kernel. -/
def secondCertificateFactor (β q N t : ℂ) : ℂ :=
  (-N * q ^ 3 * (N * β * q - 1) * (N * β * q ^ 2 - 1) * (N * β ^ 2 * q - 1) *
    (N * β ^ 2 * q ^ 2 - 1) * (N ^ 2 * β ^ 2 * q ^ 3 - 1) / (N * q ^ 3 - 1)) *
    (1 - β ^ 2 * t / q) * (1 - β ^ 2 * t ^ 2 / q) * (1 + β * t / q) * (1 - t) /
      (t * (1 - β ^ 2 * N * t) * (1 - β ^ 2 * N * q * t) *
        (1 - β ^ 2 * N * q ^ 2 * t))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Rational verification of the second finite telescoping certificate. -/
lemma second_certificate_algebra (S β q N t : ℂ)
    (hd : ∀ z ∈ [q, N, t, N * q - 1, N * q ^ 2 - 1, N * q ^ 3 - 1,
      1 - β ^ 2 * N * t, 1 - β ^ 2 * N * q * t, 1 - β ^ 2 * N * q ^ 2 * t,
      1 - β ^ 2 * N * q ^ 3 * t, 1 - β ^ 2 * t,
      1 - β ^ 2 * q * t ^ 2, 1 + β * t, 1 - q * t], z ≠ 0) :
    squareLeadingCoefficient β q N - squareNextCoefficient S β q N *
        shiftProduct q (β ^ 2) (N * q ^ 2) 1 t - squareMiddleCoefficient S β q N *
        shiftProduct q (β ^ 2) (N * q) 2 t - squareCurrentCoefficient β q N *
        shiftProduct q (β ^ 2) N 3 t =
      secondCertificateFactor β q N (q * t) *
          (q * (1 - (N * q ^ 3)⁻¹ * t) * (1 - β ^ 2 * (N * q ^ 3) * t) *
            (1 - (S ^ 2 - 2 * β) * t + β ^ 2 * t ^ 2) * (1 - β * t)) /
          ((1 - β ^ 2 * t) * (1 - β ^ 2 * q * t ^ 2) * (1 + β * t) * (1 - q * t)) -
        secondCertificateFactor β q N t := by
  have hq := hd q (by simp)
  have hN := hd N (by simp)
  have ht := hd t (by simp)
  have hN1 := hd (N * q - 1) (by simp)
  have hN2 := hd (N * q ^ 2 - 1) (by simp)
  have hN3 := hd (N * q ^ 3 - 1) (by simp)
  have hN1' : -1 + N * q ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hN1
  have hN2' : -1 + N * q ^ 2 ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hN2
  have hN3' : -1 + N * q ^ 3 ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hN3
  have hD0 := hd (1 - β ^ 2 * N * t) (by simp)
  have hD1 := hd (1 - β ^ 2 * N * q * t) (by simp)
  have hD2 := hd (1 - β ^ 2 * N * q ^ 2 * t) (by simp)
  have hD3 := hd (1 - β ^ 2 * N * q ^ 3 * t) (by simp)
  have hW0 := hd (1 - β ^ 2 * t) (by simp)
  have hW1 := hd (1 - β ^ 2 * q * t ^ 2) (by simp)
  have hW2 := hd (1 + β * t) (by simp)
  have hW3 := hd (1 - q * t) (by simp)
  have hD1' : 1 - β ^ 2 * N * (q * t) ≠ 0 := by convert hD1 using 1; ring
  have hD2' : 1 - β ^ 2 * N * q * (q * t) ≠ 0 := by convert hD2 using 1; ring
  have hD3' : 1 - β ^ 2 * N * q ^ 2 * (q * t) ≠ 0 := by convert hD3 using 1; ring
  let C : ℂ := -N * q ^ 3 * (N * β * q - 1) * (N * β * q ^ 2 - 1) *
    (N * β ^ 2 * q - 1) * (N * β ^ 2 * q ^ 2 - 1) *
    (N ^ 2 * β ^ 2 * q ^ 3 - 1) / (N * q ^ 3 - 1)
  have hstep : secondCertificateFactor β q N (q * t) *
      (q * (1 - (N * q ^ 3)⁻¹ * t) * (1 - β ^ 2 * (N * q ^ 3) * t) *
        (1 - (S ^ 2 - 2 * β) * t + β ^ 2 * t ^ 2) * (1 - β * t)) /
      ((1 - β ^ 2 * t) * (1 - β ^ 2 * q * t ^ 2) * (1 + β * t) * (1 - q * t)) =
      C * (1 - (N * q ^ 3)⁻¹ * t) *
        (1 - (S ^ 2 - 2 * β) * t + β ^ 2 * t ^ 2) * (1 - β * t) /
        (t * (1 - β ^ 2 * N * q * t) * (1 - β ^ 2 * N * q ^ 2 * t)) := by
    change (C * (1 - β ^ 2 * (q * t) / q) * (1 - β ^ 2 * (q * t) ^ 2 / q) *
        (1 + β * (q * t) / q) * (1 - q * t) /
        ((q * t) * (1 - β ^ 2 * N * (q * t)) * (1 - β ^ 2 * N * q * (q * t)) *
          (1 - β ^ 2 * N * q ^ 2 * (q * t)))) * _ / _ = _
    generalize C = c
    have he0 : 1 - β ^ 2 * (q * t) / q = 1 - β ^ 2 * t := by field_simp
    have he1 : 1 - β ^ 2 * (q * t) ^ 2 / q = 1 - β ^ 2 * q * t ^ 2 := by
      field_simp
    have he2 : 1 + β * (q * t) / q = 1 + β * t := by field_simp
    have hcancel (w0 w1 w2 w3 d1 d2 d3 X Y Z : ℂ)
        (hw0 : w0 ≠ 0) (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (hw3 : w3 ≠ 0)
        (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) (hd3 : d3 ≠ 0) :
        (c * w0 * w1 * w2 * w3 / (q * t * d1 * d2 * d3)) *
          (q * X * d3 * Y * Z) / (w0 * w1 * w2 * w3) =
          c * X * Y * Z / (t * d1 * d2) := by field_simp
    rw [he0, he1, he2,
      show 1 - β ^ 2 * N * (q * t) = 1 - β ^ 2 * N * q * t by ring,
      show 1 - β ^ 2 * N * q * (q * t) = 1 - β ^ 2 * N * q ^ 2 * t by ring,
      show 1 - β ^ 2 * N * q ^ 2 * (q * t) = 1 - β ^ 2 * N * q ^ 3 * t by ring,
      show 1 - β ^ 2 * (N * q ^ 3) * t = 1 - β ^ 2 * N * q ^ 3 * t by ring]
    exact hcancel _ _ _ _ _ _ _ _ _ _ hW0 hW1 hW2 hW3 hD1 hD2 hD3
  rw [hstep]
  dsimp only [C]
  have hl0 : lowerFactor β q N = -β * (N * q - 1) := by unfold lowerFactor; ring
  have hl1 : lowerFactor β q (N * q) = -β * (N * q ^ 2 - 1) := by
    unfold lowerFactor
    ring
  simp only [shiftProduct, secondCertificateFactor, squareLeadingCoefficient,
    squareNextCoefficient, squareMiddleCoefficient, squareCurrentCoefficient,
    leadingFactor, middleFactor, hl0, hl1, prod_range_succ, prod_range_zero,
    pow_zero, pow_one, mul_one]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc] at hN1 hN2 hN3 hD0 hD1 hD2 hD3 ⊢
  field_simp
  ring_nf
  have hfactor0 : -1 + β ^ 2 * N * q ^ 2 * t - β ^ 2 * N ^ 2 * q ^ 5 * t + N * q ^ 3 = (N * q ^
    3 - 1) * (1 - β ^ 2 * N * q ^ 2 * t) := by ring
  have hfactor1 : 1 - β ^ 2 * N * q * t - β ^ 2 * N * q ^ 2 * t + β ^ 2 * N ^ 2 * q ^ 3 * t + β
    ^ 2 * N ^ 2 * q ^ 4 * t * 2 + β ^ 2 * N ^ 2 * q ^ 5 * t - β ^ 2 * N ^ 3 * q ^ 6 * t - β ^ 2
    * N ^ 3 * q ^ 7 * t + β ^ 4 * N ^ 2 * q ^ 3 * t ^ 2 - β ^ 4 * N ^ 3 * q ^ 5 * t ^ 2 - β ^ 4
    * N ^ 3 * q ^ 6 * t ^ 2 + β ^ 4 * N ^ 4 * q ^ 8 * t ^ 2 - N * q ^ 2 - N * q ^ 3 + N ^ 2 * q
    ^ 5 = (N * q ^ 2 - 1) * (N * q ^ 3 - 1) * (1 - β ^ 2 * N * q * t) * (1 - β ^ 2 * N * q ^ 2 *
    t) := by ring
  have hfactor2 : 1 - β ^ 2 * N * q * t - β ^ 2 * N * q ^ 2 * t - β ^ 2 * N * t + β ^ 2 * N ^ 2
    * q ^ 2 * t + β ^ 2 * N ^ 2 * q ^ 3 * t * 2 + β ^ 2 * N ^ 2 * q ^ 4 * t * 2 + β ^ 2 * N ^ 2
    * q ^ 5 * t - β ^ 2 * N ^ 3 * q ^ 5 * t - β ^ 2 * N ^ 3 * q ^ 6 * t - β ^ 2 * N ^ 3 * q ^ 7
    * t + β ^ 4 * N ^ 2 * q * t ^ 2 + β ^ 4 * N ^ 2 * q ^ 2 * t ^ 2 + β ^ 4 * N ^ 2 * q ^ 3 * t
    ^ 2 - β ^ 4 * N ^ 3 * q ^ 3 * t ^ 2 - β ^ 4 * N ^ 3 * q ^ 4 * t ^ 2 * 2 - β ^ 4 * N ^ 3 * q
    ^ 5 * t ^ 2 * 2 - β ^ 4 * N ^ 3 * q ^ 6 * t ^ 2 + β ^ 4 * N ^ 4 * q ^ 6 * t ^ 2 + β ^ 4 * N
    ^ 4 * q ^ 7 * t ^ 2 + β ^ 4 * N ^ 4 * q ^ 8 * t ^ 2 - β ^ 6 * N ^ 3 * q ^ 3 * t ^ 3 + β ^ 6
    * N ^ 4 * q ^ 5 * t ^ 3 + β ^ 6 * N ^ 4 * q ^ 6 * t ^ 3 - β ^ 6 * N ^ 5 * q ^ 8 * t ^ 3 - N
    * q ^ 2 - N * q ^ 3 + N ^ 2 * q ^ 5 = (N * q ^ 2 - 1) * (N * q ^ 3 - 1) * (1 - β ^ 2 * N *
    t) * (1 - β ^ 2 * N * q * t) * (1 - β ^ 2 * N * q ^ 2 * t) := by ring
  have hfactor3 : -1 + β ^ 2 * N * q * t + β ^ 2 * N * q ^ 2 * t - β ^ 2 * N ^ 2 * q ^ 4 * t - β
    ^ 2 * N ^ 2 * q ^ 5 * t - β ^ 4 * N ^ 2 * q ^ 3 * t ^ 2 + β ^ 4 * N ^ 3 * q ^ 6 * t ^ 2 + N
    * q ^ 3 = (N * q ^ 3 - 1) * (1 - β ^ 2 * N * q * t) * (1 - β ^ 2 * N * q ^ 2 * t) := by ring
  rw [hfactor0, hfactor1, hfactor2, hfactor3]
  have hfN1 := hd (N * q - 1) (by simp)
  have hfN2 := hd (N * q ^ 2 - 1) (by simp)
  have hfN3 := hd (N * q ^ 3 - 1) (by simp)
  have hfD0 := hd (1 - β ^ 2 * N * t) (by simp)
  have hfD1 := hd (1 - β ^ 2 * N * q * t) (by simp)
  have hfD2 := hd (1 - β ^ 2 * N * q ^ 2 * t) (by simp)
  simp only [mul_inv_rev]
  field_simp [hfN1, hfN2, hfN3, hfD0, hfD1, hfD2]
  ring


/-- The five-phi-four finite sum in the q-Clausen identity. -/
def secondSum (S β q : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (n + 1), secondKernel S β q (q ^ n) k

/-- The finite certificate for the recurrence of the five-phi-four sum. -/
def secondCertificate (S β q : ℂ) (n k : ℕ) : ℂ :=
  secondCertificateFactor β q (q ^ n) (q ^ k) * secondKernel S β q (q ^ (n + 3)) k

/-- The second certificate denominators avoid the fixed square-parameter lattice. -/
lemma second_certificate_regular {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (n k : ℕ) :
    ∀ z ∈ [q, q ^ n, q ^ k, q ^ n * q - 1, q ^ n * q ^ 2 - 1, q ^ n * q ^ 3 - 1,
      1 - β ^ 2 * q ^ n * q ^ k, 1 - β ^ 2 * q ^ n * q * q ^ k,
      1 - β ^ 2 * q ^ n * q ^ 2 * q ^ k, 1 - β ^ 2 * q ^ n * q ^ 3 * q ^ k,
      1 - β ^ 2 * q ^ k, 1 - β ^ 2 * q * (q ^ k) ^ 2,
      1 + β * q ^ k, 1 - q * q ^ k], z ≠ 0 := by
  have h := first_certificate_regular hq0 hq hB n k
  have hN3 : q ^ n * q ^ 3 - 1 ≠ 0 := by
    rw [← pow_add]
    intro he
    have hqN : ‖q ^ (n + 3)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [sub_eq_zero.mp he, norm_one] at hqN
    exact lt_irrefl _ hqN
  have hD3 : 1 - β ^ 2 * q ^ n * q ^ 3 * q ^ k ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [pow_add, mul_assoc] using (hB (n + 3 + k)).symm
  simp only [List.forall_mem_cons] at h ⊢
  rcases h with ⟨hq', hN, ht, hN1, hN2, hD0, hD1, hD2, hW1, hW2, hW3, hnil⟩
  exact ⟨hq', hN, ht, hN1, hN2, hN3, hD0, hD1, hD2, hD3,
    sub_ne_zero.mpr (hB k).symm, hW1, hW2, hW3, hnil⟩

/-- The four-term contiguous difference of the second kernel telescopes. -/
lemma secondKernel_contiguous {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) (n k : ℕ) :
    squareLeadingCoefficient β q (q ^ n) * secondKernel S β q (q ^ (n + 3)) k -
        squareNextCoefficient S β q (q ^ n) * secondKernel S β q (q ^ (n + 2)) k -
        squareMiddleCoefficient S β q (q ^ n) * secondKernel S β q (q ^ (n + 1)) k -
        squareCurrentCoefficient β q (q ^ n) * secondKernel S β q (q ^ n) k =
      secondCertificate S β q n (k + 1) - secondCertificate S β q n k := by
  have h0 := weightedKernel_eq_shiftProduct hq0 hq hB (secondWeight S β q) n 3 k
  have h1 := weightedKernel_eq_shiftProduct hq0 hq hB (secondWeight S β q) (n + 1) 2 k
  have h2 := weightedKernel_eq_shiftProduct hq0 hq hB (secondWeight S β q) (n + 2) 1 k
  change secondKernel S β q (q ^ n) k = secondKernel S β q (q ^ (n + 3)) k *
    shiftProduct q (β ^ 2) (q ^ n) 3 (q ^ k) at h0
  change secondKernel S β q (q ^ (n + 1)) k = secondKernel S β q (q ^ (n + 3)) k *
    shiftProduct q (β ^ 2) (q ^ (n + 1)) 2 (q ^ k) at h1
  change secondKernel S β q (q ^ (n + 2)) k = secondKernel S β q (q ^ (n + 3)) k *
    shiftProduct q (β ^ 2) (q ^ (n + 2)) 1 (q ^ k) at h2
  rw [h0, h1, h2]
  unfold secondCertificate
  rw [secondKernel_succ]
  have hA := second_certificate_algebra S β q (q ^ n) (q ^ k)
    (second_certificate_regular hq0 hq hB n k)
  rw [pow_add q n 3, pow_add q n 2, pow_succ q n, pow_succ' q k]
  linear_combination (secondKernel S β q (q ^ n * q ^ 3) k) * hA

/-- The truncating upper factor makes the second kernel vanish beyond its natural endpoint. -/
lemma secondKernel_pow_eq_zero {S β q : ℂ} (hq0 : q ≠ 0) {n k : ℕ} (hk : n < k) :
    secondKernel S β q (q ^ n) k = 0 := by
  simp only [secondKernel, weightedKernel, qPochhammer_recip_pow_eq_zero hq0 hk, zero_mul]

/-- The second certificate vanishes at its lower endpoint. -/
@[simp] lemma secondCertificate_zero (S β q : ℂ) (n : ℕ) : secondCertificate S β q n 0 = 0 := by
  simp [secondCertificate, secondCertificateFactor]

/-- The second certificate vanishes beyond the terminating endpoint. -/
lemma secondCertificate_end {S β q : ℂ} (hq0 : q ≠ 0) (n : ℕ) :
    secondCertificate S β q n (n + 4) = 0 := by
  unfold secondCertificate
  rw [secondKernel_pow_eq_zero hq0 (show n + 3 < n + 4 by omega), mul_zero]

/-- The second finite sum may be extended through any larger endpoint. -/
lemma secondSum_eq_range_of_le {q : ℂ} (hq0 : q ≠ 0) (S β : ℂ) {n N : ℕ} (hn : n ≤ N) :
    secondSum S β q n = ∑ k ∈ range (N + 1), secondKernel S β q (q ^ n) k := by
  unfold secondSum
  apply sum_subset (range_mono (Nat.add_le_add_right hn 1))
  intro k hk hkn
  apply secondKernel_pow_eq_zero hq0
  simp only [mem_range] at hk hkn
  omega


/-- The five-phi-four finite sum satisfies the square recurrence. -/
theorem secondSum_contiguous {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) (n : ℕ) :
    squareLeadingCoefficient β q (q ^ n) * secondSum S β q (n + 3) =
      squareNextCoefficient S β q (q ^ n) * secondSum S β q (n + 2) +
        squareMiddleCoefficient S β q (q ^ n) * secondSum S β q (n + 1) +
        squareCurrentCoefficient β q (q ^ n) * secondSum S β q n := by
  have hs : squareLeadingCoefficient β q (q ^ n) * secondSum S β q (n + 3) -
      squareNextCoefficient S β q (q ^ n) * secondSum S β q (n + 2) -
      squareMiddleCoefficient S β q (q ^ n) * secondSum S β q (n + 1) -
      squareCurrentCoefficient β q (q ^ n) * secondSum S β q n = 0 := by
    calc
      _ = ∑ k ∈ range (n + 4), (squareLeadingCoefficient β q (q ^ n) *
          secondKernel S β q (q ^ (n + 3)) k - squareNextCoefficient S β q (q ^ n) *
          secondKernel S β q (q ^ (n + 2)) k - squareMiddleCoefficient S β q (q ^ n) *
          secondKernel S β q (q ^ (n + 1)) k -
          squareCurrentCoefficient β q (q ^ n) * secondKernel S β q (q ^ n) k) := by
        rw [secondSum_eq_range_of_le hq0 S β (show n + 2 ≤ n + 3 by omega),
          secondSum_eq_range_of_le hq0 S β (show n + 1 ≤ n + 3 by omega),
          secondSum_eq_range_of_le hq0 S β (show n ≤ n + 3 by omega)]
        simp only [secondSum, mul_sum, sum_sub_distrib]
      _ = ∑ k ∈ range (n + 4), (secondCertificate S β q n (k + 1) -
          secondCertificate S β q n k) :=
        sum_congr rfl fun k _ => secondKernel_contiguous hq0 hq hB S n k
      _ = 0 := by rw [sum_range_sub, secondCertificate_end hq0, secondCertificate_zero, sub_self]
  linear_combination hs

/-- Squaring the first three-term recurrence gives the recurrence of the second finite sum. -/
theorem firstSum_sq_contiguous {β q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, β ^ 2 * q ^ j ≠ 1) (S : ℂ) (n : ℕ) :
    squareLeadingCoefficient β q (q ^ n) * (firstSum S β q (n + 3)) ^ 2 =
      squareNextCoefficient S β q (q ^ n) * (firstSum S β q (n + 2)) ^ 2 +
        squareMiddleCoefficient S β q (q ^ n) * (firstSum S β q (n + 1)) ^ 2 +
        squareCurrentCoefficient β q (q ^ n) * (firstSum S β q n) ^ 2 := by
  have h0 : leadingFactor β q (q ^ n) * firstSum S β q (n + 2) =
      S * middleFactor β q (q ^ n) * firstSum S β q (n + 1) -
        lowerFactor β q (q ^ n) * firstSum S β q n := by
    simpa only [leadingFactor, middleFactor, lowerFactor, pow_succ, mul_assoc] using
      firstSum_contiguous hq0 hq hB S n
  have h1 : leadingFactor β q (q ^ n * q) * firstSum S β q (n + 3) =
      S * middleFactor β q (q ^ n * q) * firstSum S β q (n + 2) -
        lowerFactor β q (q ^ n * q) * firstSum S β q (n + 1) := by
    simpa only [leadingFactor, middleFactor, lowerFactor, pow_succ, mul_assoc] using
      firstSum_contiguous hq0 hq hB S (n + 1)
  have h0sq := congrArg (fun z : ℂ => z ^ 2) h0
  have h1sq := congrArg (fun z : ℂ => z ^ 2) h1
  have hcross := congrArg (fun z : ℂ => z * firstSum S β q (n + 1)) h0
  unfold squareLeadingCoefficient squareNextCoefficient squareMiddleCoefficient
    squareCurrentCoefficient
  linear_combination (leadingFactor β q (q ^ n) * middleFactor β q (q ^ n)) * h1sq +
    (middleFactor β q (q ^ n * q) * lowerFactor β q (q ^ n * q)) * h0sq -
    (2 * S * middleFactor β q (q ^ n) * middleFactor β q (q ^ n * q) *
      lowerFactor β q (q ^ n * q)) * hcross


end DLMF.QHypergeometric.ClausenRecurrence
