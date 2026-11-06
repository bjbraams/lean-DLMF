/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.ShiftedFactorials
public import DLMF.QSeries.QBinomial

/-!
# Finite kernels for the q-Clausen identity

Symmetric upper parameters are combined into quadratic shifted-factorial factors.
A common pair of terminating upper parameters admits index-independent shift ratios;
these give finite telescoping proofs for the square identity of DLMF 17.9.18.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.ClausenRecurrence

/-- The shifted-factorial product associated with a symmetric quadratic factor. -/
def quadraticPochhammer (S β q : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => quadraticPochhammer S β q k * (1 - S * q ^ k + β * (q ^ k) ^ 2)

/-- Combining the two upper parameters records only their sum and product. -/
lemma quadraticPochhammer_eq_mul (a b q : ℂ) (k : ℕ) :
    quadraticPochhammer (a + b) (a * b) q k = qPochhammer a q k * qPochhammer b q k := by
  induction k with
  | zero => simp [quadraticPochhammer]
  | succ k ih => rw [quadraticPochhammer, ih, qPochhammer_succ, qPochhammer_succ]; ring

/-- A kernel with the paired truncation parameters `N⁻¹` and `BN`. -/
def weightedKernel (q B N : ℂ) (w : ℕ → ℂ) (k : ℕ) : ℂ :=
  qPochhammer N⁻¹ q k * qPochhammer (B * N) q k * w k

/-- The weight of the terminating four-phi-three sum. -/
def firstWeight (S β q : ℂ) (k : ℕ) : ℂ :=
  quadraticPochhammer S β q k /
    (qPochhammer (β ^ 2 * q) (q ^ 2) k * qPochhammer (-β) q k * qPochhammer q q k) * q ^ k

/-- The weight of the terminating five-phi-four sum. -/
def secondWeight (S β q : ℂ) (k : ℕ) : ℂ :=
  quadraticPochhammer (S ^ 2 - 2 * β) (β ^ 2) q k * qPochhammer β q k /
    (qPochhammer (β ^ 2) q k * qPochhammer (β ^ 2 * q) (q ^ 2) k *
      qPochhammer (-β) q k * qPochhammer q q k) * q ^ k

/-- The first finite kernel, expressed in its symmetric parameters. -/
def firstKernel (S β q N : ℂ) (k : ℕ) : ℂ := weightedKernel q (β ^ 2) N (firstWeight S β q) k

/-- The second finite kernel, expressed in its symmetric parameters. -/
def secondKernel (S β q N : ℂ) (k : ℕ) : ℂ := weightedKernel q (β ^ 2) N (secondWeight S β q) k

/-- Interchanging the initial factor and a block of arbitrary length. -/
lemma pochhammer_one_shift (a q : ℂ) (k : ℕ) :
    (1 - a) * qPochhammer (a * q) q k = qPochhammer a q k * (1 - a * q ^ k) := by
  have h := qPochhammer_succ' a q k
  rw [qPochhammer_succ] at h
  exact h.symm

/-- The common upper pair shifts without division by either upper shifted factorial. -/
lemma weightedKernel_mul_shift {q N : ℂ} (hq : q ≠ 0) (hN : N ≠ 0)
    (B : ℂ) (w : ℕ → ℂ) (k : ℕ) :
    weightedKernel q B N w k * ((N * q - 1) * (1 - B * N * q ^ k)) =
      weightedKernel q B (N * q) w k * ((N * q - q ^ k) * (1 - B * N)) := by
  have hneg := pochhammer_one_shift (N * q)⁻¹ q k
  have hpos := pochhammer_one_shift (B * N) q k
  rw [show (N * q)⁻¹ * q = N⁻¹ by field_simp] at hneg
  have hn : (N * q - 1) * qPochhammer N⁻¹ q k =
      (N * q - q ^ k) * qPochhammer (N * q)⁻¹ q k := by
    field_simp at hneg
    simp only [one_div] at hneg
    linear_combination hneg
  have hp : (1 - B * N) * qPochhammer (B * (N * q)) q k =
      qPochhammer (B * N) q k * (1 - B * N * q ^ k) := by
    simpa only [mul_assoc] using hpos
  unfold weightedKernel
  linear_combination (qPochhammer (B * (N * q)) q k * w k * (1 - B * N)) * hn -
    (qPochhammer N⁻¹ q k * w k * (N * q - 1)) * hp

/-- The multiplier for a succession of shifts in the paired upper parameters. -/
def shiftProduct (q B N : ℂ) (r : ℕ) (t : ℂ) : ℂ :=
  ∏ j ∈ range r, ((N * q ^ (j + 1) - t) * (1 - B * N * q ^ j)) /
    ((N * q ^ (j + 1) - 1) * (1 - B * N * q ^ j * t))

/-- Iterating the upper-parameter shift is valid at every regular positive power of the base. -/
lemma weightedKernel_eq_shiftProduct {q B : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, B * q ^ j ≠ 1) (w : ℕ → ℂ) (n r k : ℕ) :
    weightedKernel q B (q ^ n) w k =
      weightedKernel q B (q ^ (n + r)) w k * shiftProduct q B (q ^ n) r (q ^ k) := by
  have hf1 (j : ℕ) : q ^ n * q ^ (j + 1) - 1 ≠ 0 := by
    rw [← pow_add]
    intro he
    have h : ‖q ^ (n + (j + 1))‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [sub_eq_zero.mp he, norm_one] at h
    exact lt_irrefl _ h
  have hf2 (j : ℕ) : 1 - B * q ^ n * q ^ j * q ^ k ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [pow_add, mul_assoc] using (hB (n + j + k)).symm
  induction r with
  | zero => simp [shiftProduct]
  | succ r ih =>
    have hs : weightedKernel q B (q ^ (n + r)) w k =
        weightedKernel q B (q ^ (n + (r + 1))) w k *
          ((q ^ n * q ^ (r + 1) - q ^ k) * (1 - B * q ^ n * q ^ r)) /
          ((q ^ n * q ^ (r + 1) - 1) * (1 - B * q ^ n * q ^ r * q ^ k)) := by
      apply (eq_div_iff (mul_ne_zero (hf1 r) (hf2 r))).mpr
      have h := weightedKernel_mul_shift hq0 (pow_ne_zero (n + r) hq0) B w k
      simpa only [pow_add, pow_succ, mul_assoc] using h
    rw [ih, hs]
    simp only [shiftProduct, prod_range_succ]
    ring

/-- The first kernel has its rational ratio in the summation index. -/
lemma firstKernel_succ (S β q N : ℂ) (k : ℕ) :
    firstKernel S β q N (k + 1) = firstKernel S β q N k *
      (q * (1 - N⁻¹ * q ^ k) * (1 - β ^ 2 * N * q ^ k) *
        (1 - S * q ^ k + β * (q ^ k) ^ 2)) /
      ((1 - β ^ 2 * q * (q ^ k) ^ 2) * (1 + β * q ^ k) * (1 - q * q ^ k)) := by
  have hp : (q ^ 2) ^ k = (q ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  simp only [firstKernel, weightedKernel, firstWeight, qPochhammer_succ,
    quadraticPochhammer, pow_succ q k, hp]
  simp only [div_eq_mul_inv, mul_inv_rev, neg_mul, sub_neg_eq_add]
  ring

/-- The second kernel has its rational ratio in the summation index. -/
lemma secondKernel_succ (S β q N : ℂ) (k : ℕ) :
    secondKernel S β q N (k + 1) = secondKernel S β q N k *
      (q * (1 - N⁻¹ * q ^ k) * (1 - β ^ 2 * N * q ^ k) *
        (1 - (S ^ 2 - 2 * β) * q ^ k + β ^ 2 * (q ^ k) ^ 2) * (1 - β * q ^ k)) /
      ((1 - β ^ 2 * q ^ k) * (1 - β ^ 2 * q * (q ^ k) ^ 2) *
        (1 + β * q ^ k) * (1 - q * q ^ k)) := by
  have hp : (q ^ 2) ^ k = (q ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  simp only [secondKernel, weightedKernel, secondWeight, qPochhammer_succ,
    quadraticPochhammer, pow_succ q k, hp]
  simp only [div_eq_mul_inv, mul_inv_rev, neg_mul, sub_neg_eq_add]
  ring

end DLMF.QHypergeometric.ClausenRecurrence
