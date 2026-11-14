/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# A Newton identity for Stirling numbers and power sums

For fixed `k`, the numbers `S(k+d,k)` are complete homogeneous symmetric sums of
`1, …, k`. Their Newton identity relates them to the power sums of these integers.

* `Nat.mul_stirlingSecond_add_eq_sum_pow`: the Newton recurrence.

The proof uses Mathlib's Stirling recurrence and formal power series derivative API;
no convergence assumptions are needed.
-/

public noncomputable section

open Finset
open scoped Nat PowerSeries

namespace Nat

/-- The rational Newton identity, proved by differentiating its formal generating series. -/
private lemma cast_mul_stirlingSecond_add_eq_sum_pow (k d : ℕ) :
    ((d + 1) * Nat.stirlingSecond (k + (d + 1)) k : ℚ) =
      ∑ i ∈ Finset.range (d + 1), (∑ j ∈ Finset.range (k + 1), (j : ℚ) ^ (i + 1)) *
        (Nat.stirlingSecond (k + (d - i)) k : ℚ) := by
  let F (k : ℕ) : PowerSeries ℚ := PowerSeries.mk fun d => (Nat.stirlingSecond (k + d) k : ℚ)
  let G (k : ℕ) : PowerSeries ℚ := PowerSeries.mk fun d =>
    ∑ j ∈ Finset.range (k + 1), (j : ℚ) ^ (d + 1)
  let H (k : ℕ) : PowerSeries ℚ := 1 - PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X
  have hF (k : ℕ) : F (k + 1) * H k = F k := by
    dsimp only [H]
    rw [mul_sub, mul_one, ← mul_assoc]
    ext d
    rcases d with _ | d
    · simp [F, Nat.stirlingSecond_self]
    · rw [map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
      simp only [F, PowerSeries.coeff_mk]
      rw [show k + 1 + (d + 1) = (k + 1 + d) + 1 by omega,
        Nat.stirlingSecond_succ_succ]
      push_cast
      rw [show k + (d + 1) = k + 1 + d by omega]
      ring
  have hG (k : ℕ) : G (k + 1) * H k = G k * H k + PowerSeries.C ((k + 1 : ℕ) : ℚ) := by
    dsimp only [H]
    rw [mul_sub, mul_one, mul_sub, mul_one]
    simp only [← mul_assoc]
    ext d
    rcases d with _ | d
    · simp [G, sum_range_succ]
    · rw [map_sub, map_add, map_sub, PowerSeries.coeff_succ_mul_X,
        PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C]
      simp only [G, PowerSeries.coeff_mk, PowerSeries.coeff_C, Nat.succ_ne_zero, ↓reduceIte,
        add_zero, sum_range_succ, pow_succ]
      ring
  have hder : ∀ k : ℕ, PowerSeries.derivative (F k) = F k * G k := by
    intro k
    induction k with
    | zero =>
      have hF0 : F 0 = 1 := by ext d; rcases d with _ | d <;> simp [F]
      have hG0 : G 0 = 0 := by ext d; simp [G]
      rw [hF0, hG0, PowerSeries.derivative_one, mul_zero]
    | succ k ih =>
      have hH0 : H k ≠ 0 := by
        intro he
        have h := congrArg PowerSeries.constantCoeff he
        norm_num [H] at h
      apply mul_right_cancel₀ hH0
      have hd := congrArg PowerSeries.derivative (hF k)
      rw [Derivation.leibniz, ih] at hd
      simp only [H, map_sub, Derivation.leibniz, PowerSeries.derivative_one,
        PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul, mul_one, mul_zero,
        add_zero, zero_sub] at hd
      have hf := hF k
      have hg := hG k
      dsimp only [H] at hf hg ⊢
      linear_combination hd - F (k + 1) * hg - G k * hf
  have h := congrArg (PowerSeries.coeff d) (hder k)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    ← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [F, G, PowerSeries.coeff_mk, Prod.swap] at h
  simpa only [mul_comm] using h

/-- The complete homogeneous Stirling numbers satisfy Newton's power sum identity. -/
lemma mul_stirlingSecond_add_eq_sum_pow (k d : ℕ) :
    (d + 1) * Nat.stirlingSecond (k + (d + 1)) k =
      ∑ i ∈ Finset.range (d + 1), (∑ j ∈ Finset.range (k + 1), j ^ (i + 1)) *
        Nat.stirlingSecond (k + (d - i)) k := by
  exact_mod_cast cast_mul_stirlingSecond_add_eq_sum_pow k d

end Nat
