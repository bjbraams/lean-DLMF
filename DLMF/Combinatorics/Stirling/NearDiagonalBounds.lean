/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Stirling.RecurrencesAndIdentities
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounds near the diagonal for Stirling numbers of the second kind

The iterated-sum recurrence bounds `S(n+k,k)` between `k^(2n)/(2^n n!)` and
`(k+n)^(2n)/(2^n n!)`. Dividing through by the first expression gives an exponential
bound that proves the uniform asymptotic formula in DLMF 26.8.43.

The power-sum estimates use Mathlib's monotone sum-integral comparisons.

## Main results

* `stirlingSecond_add_bounds`: global lower and upper bounds near the diagonal.
* `stirlingSecond_add_div_bounds`: bounds for the normalized ratio when `k > 0`.
-/

public noncomputable section

open Finset

namespace DLMF.Combinatorics

/-- Global bounds for Stirling numbers of the second kind near the diagonal, including
the zero row and zero column. -/
lemma stirlingSecond_add_bounds (n k : ℕ) :
    (k : ℝ) ^ (2 * n) / (2 ^ n * n.factorial) ≤ Nat.stirlingSecond (n + k) k ∧
      (Nat.stirlingSecond (n + k) k : ℝ) ≤
        ((k + n : ℕ) : ℝ) ^ (2 * n) / (2 ^ n * n.factorial) := by
  have hpow (p K : ℕ) :
      (∑ j ∈ range K, (j : ℝ) ^ p) ≤ (K : ℝ) ^ (p + 1) / (p + 1) ∧
        (K : ℝ) ^ (p + 1) / (p + 1) ≤ ∑ j ∈ range (K + 1), (j : ℝ) ^ p := by
    have hm : MonotoneOn (fun x : ℝ => x ^ p) (Set.Icc ((0 : ℕ) : ℝ) (K : ℝ)) := by
      intro x hx y _ hxy
      exact pow_le_pow_left₀ (by simpa only [Nat.cast_zero] using hx.1) hxy p
    have hu := hm.sum_le_integral_Ico (Nat.zero_le K)
    have hl := hm.integral_le_sum_Ico (Nat.zero_le K)
    simp only [← range_eq_Ico, Nat.cast_zero, integral_pow,
      zero_pow (by omega : p + 1 ≠ 0), sub_zero] at hu hl
    refine ⟨hu, ?_⟩
    rw [sum_range_succ']
    simpa only [Nat.cast_zero] using
      hl.trans (le_add_of_nonneg_right (pow_nonneg (by norm_num : (0 : ℝ) ≤ 0) p))
  induction n generalizing k with
  | zero => simp [Nat.stirlingSecond_self]
  | succ n ih =>
    have hc (j : ℕ) := ih j
    have hrec := congrArg (Nat.cast (R := ℝ)) (stirlingSecond_add_succ n k)
    push_cast at hrec
    rw [show n + 1 + k = n + k + 1 by omega, hrec]
    have hden : (0 : ℝ) < 2 ^ n * n.factorial := by positivity
    have hden' : (2 : ℝ) ^ (n + 1) * (n + 1).factorial =
        (2 * n + 1 + 1 : ℝ) * (2 ^ n * n.factorial) := by
      rw [pow_succ, Nat.factorial_succ]
      push_cast
      ring
    constructor
    · have hsum : (∑ j ∈ range (k + 1), (j : ℝ) ^ (2 * n + 1)) /
          (2 ^ n * n.factorial) ≤
        ∑ j ∈ range (k + 1), (j : ℝ) * Nat.stirlingSecond (n + j) j := by
        rw [sum_div]
        apply sum_le_sum
        intro j _
        have h := mul_le_mul_of_nonneg_left (hc j).1 (Nat.cast_nonneg j)
        simpa only [pow_succ, mul_div_assoc, mul_comm] using h
      have hp := (hpow (2 * n + 1) k).2
      have hb := (div_le_div_of_nonneg_right hp hden.le).trans hsum
      rw [div_div] at hb
      push_cast at hb
      rw [← hden'] at hb
      simpa only [show 2 * (n + 1) = 2 * n + 1 + 1 by omega] using hb
    · have hsum : (∑ j ∈ range (k + 1), (j : ℝ) * Nat.stirlingSecond (n + j) j) ≤
          (∑ j ∈ range (k + 1), if j = 0 then 0 else ((j + n : ℕ) : ℝ) ^ (2 * n + 1)) /
            (2 ^ n * n.factorial) := by
        rw [sum_div]
        apply sum_le_sum
        intro j _
        by_cases hj : j = 0
        · subst j
          simp
        · rw [ite_eq_right hj]
          have h := mul_le_mul_of_nonneg_left (hc j).2 (Nat.cast_nonneg j)
          apply h.trans
          rw [← mul_div_assoc, div_le_div_iff_of_pos_right hden, pow_succ]
          rw [mul_comm (((j + n : ℕ) : ℝ) ^ (2 * n))]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right j n)
            (by positivity)
      have hshift : (∑ j ∈ range (k + 1), if j = 0 then 0 else
          ((j + n : ℕ) : ℝ) ^ (2 * n + 1)) ≤
            ∑ i ∈ range (k + n + 1), (i : ℝ) ^ (2 * n + 1) := by
        rw [sum_range_succ']
        simp only [ite_true, add_zero, Nat.succ_ne_zero, ite_false]
        rw [← sum_image (f := fun i : ℕ => (i : ℝ) ^ (2 * n + 1))
          (g := fun j : ℕ => j + 1 + n) (fun a _ b _ h => by dsimp only at h; omega)]
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
          simp only [mem_range] at hj ⊢
          omega
        · intro i _ _
          positivity
      have hp := hshift.trans (hpow (2 * n + 1) (k + n + 1)).1
      have hb := hsum.trans (div_le_div_of_nonneg_right hp hden.le)
      rw [div_div] at hb
      push_cast at hb
      rw [← hden'] at hb
      simpa only [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Nat.cast_add,
        Nat.cast_one, add_assoc] using hb


/-- The normalized near-diagonal Stirling number lies between one and an exponential
whose exponent is quadratic in the distance from the diagonal. -/
lemma stirlingSecond_add_div_bounds {k : ℕ} (hk : 0 < k) (n : ℕ) :
    1 ≤ (Nat.stirlingSecond (n + k) k : ℝ) /
        ((k : ℝ) ^ (2 * n) / (2 ^ n * n.factorial)) ∧
      (Nat.stirlingSecond (n + k) k : ℝ) /
        ((k : ℝ) ^ (2 * n) / (2 ^ n * n.factorial)) ≤
          Real.exp (2 * (n : ℝ) ^ 2 / k) := by
  obtain ⟨hlo, hhi⟩ := stirlingSecond_add_bounds n k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hC : (0 : ℝ) < 2 ^ n * n.factorial := by positivity
  have hD : (0 : ℝ) < (k : ℝ) ^ (2 * n) / (2 ^ n * n.factorial) :=
    div_pos (pow_pos hkR _) hC
  refine ⟨(le_div_iff₀ hD).mpr (by simpa only [one_mul] using hlo), ?_⟩
  have he :
      (((k + n : ℕ) : ℝ) ^ (2 * n) / (2 ^ n * n.factorial)) /
          ((k : ℝ) ^ (2 * n) / (2 ^ n * n.factorial)) =
        (1 + (n : ℝ) / k) ^ (2 * n) := by
    rw [div_div_div_cancel_right₀ hC.ne', ← div_pow]
    congr 1
    push_cast
    field_simp
  calc
    _ ≤ (1 + (n : ℝ) / k) ^ (2 * n) := by
      rw [← he]
      exact div_le_div_of_nonneg_right hhi hD.le
    _ ≤ (Real.exp ((n : ℝ) / k)) ^ (2 * n) := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [Real.add_one_le_exp ((n : ℝ) / k)]
    _ = Real.exp (2 * (n : ℝ) ^ 2 / k) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

end DLMF.Combinatorics
