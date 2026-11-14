/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.JacobiElliptic.ModulusInversion
import DLMFMathlib.Analysis.Asymptotics.SparsePowerSeries
import Mathlib.Tactic

/-!
# Bounds for real theta constants

Natural-index theta series give strict comparisons of the reduced theta-two constant with
theta-three constants at the nome and its fourth power. Pairing neighboring exponents and
using the arithmetic-geometric mean inequality proves the lower bound.
-/

open Set Filter Asymptotics
open scoped Real Topology
namespace DLMF.JacobiElliptic
open DLMF.Elliptic
/-- The reduced theta-two constant is strictly less than twice the theta-three constant. -/
public theorem jacobiThetaTwoReducedQ_lt_two_mul_jacobiThetaThreeNullQ {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    jacobiThetaTwoReducedQ q < 2 * Real.jacobiThetaThreeNullQ q := by
  have hs := summable_nat_pow_of_le_exponent
    (by simpa only [Real.norm_eq_abs, abs_of_pos hq0] using hq1)
    (K := ℝ) (z := q) (fun n => n * (n + 1)) (fun n => by nlinarith)
  have ht := summable_nat_pow_of_le_exponent
    (by simpa only [Real.norm_eq_abs, abs_of_pos hq0] using hq1)
    (K := ℝ) (z := q) (fun n => n ^ 2) (fun n => by nlinarith)
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have ht1 := (summable_nat_add_iff 1).mpr ht
  have hpoint (n : ℕ) : q ^ ((n + 1) * (n + 2)) < 2 * q ^ ((n + 1) ^ 2) := by
    have h := pow_le_pow_of_le_one hq0.le hq1.le
      (by nlinarith : (n + 1) ^ 2 ≤ (n + 1) * (n + 2))
    have hp : 0 < q ^ ((n + 1) ^ 2) := pow_pos hq0 _
    linarith only [h, hp]
  have H := Summable.tsum_lt_tsum (fun n => (hpoint n).le) (hpoint 0) hs1 (ht1.mul_left 2)
  rw [tsum_mul_left] at H
  rw [jacobiThetaTwoReducedQ_eq_two_mul_tsum hq0 hq1,
    jacobiThetaThreeNullQ_eq_two_mul_tsum_sub_one hq0 hq1]
  have HS := hs.sum_add_tsum_nat_add 1
  have HT := ht.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_mul, pow_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0)] at HS HT
  have HSc : ∑' n : ℕ, q ^ ((n + 1) * ((n + 1) + 1)) =
      ∑' n : ℕ, q ^ ((n + 1) * (n + 2)) := by rfl
  rw [HSc] at HS
  linarith only [H, HS, HT]
/-- The reduced theta-two constant exceeds twice the theta-three constant at the fourth power
of the nome. -/
public theorem two_mul_jacobiThetaThreeNullQ_pow_four_lt_jacobiThetaTwoReducedQ {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    2 * Real.jacobiThetaThreeNullQ (q ^ 4) < jacobiThetaTwoReducedQ q := by
  have hs := summable_nat_pow_of_le_exponent
    (by simpa only [Real.norm_eq_abs, abs_of_pos hq0] using hq1)
    (K := ℝ) (z := q) (fun n => n * (n + 1)) (fun n => by nlinarith)
  have ht := summable_nat_pow_of_le_exponent
    (by simpa only [Real.norm_eq_abs, abs_of_pos hq0] using hq1)
    (K := ℝ) (z := q) (fun n => 4 * n ^ 2) (fun n => by nlinarith)
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have ht1 := (summable_nat_add_iff 1).mpr ht
  have he := hs1.comp_injective (show Function.Injective (fun n : ℕ => 2 * n) from by
    intro a b h; dsimp only at h; omega)
  have ho := hs1.comp_injective (show Function.Injective (fun n : ℕ => 2 * n + 1) from by
    intro a b h; dsimp only at h; omega)
  have hpoint (n : ℕ) : 2 * q ^ (4 * (n + 1) ^ 2) <
      q ^ ((2 * n + 1) * (2 * n + 2)) + q ^ ((2 * n + 2) * (2 * n + 3)) := by
    have hp := pow_pos hq0 ((2 * n + 1) * (2 * n + 2))
    have hpow : q ^ (2 * (n + 1)) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
    have hsquare : 0 < (1 - q ^ (2 * (n + 1))) ^ 2 := sq_pos_of_pos (by linarith)
    have hmul := mul_pos hp hsquare
    have he1 : 4 * (n + 1) ^ 2 = (2 * n + 1) * (2 * n + 2) + 2 * (n + 1) := by ring
    have he2 : (2 * n + 2) * (2 * n + 3) =
        (2 * n + 1) * (2 * n + 2) + 2 * (2 * (n + 1)) := by ring
    rw [he1, he2, pow_add, pow_add,
      show q ^ (2 * (2 * (n + 1))) = (q ^ (2 * (n + 1))) ^ 2 by
        rw [← pow_mul]; congr 1; ring]
    nlinarith only [hmul]
  have HS := hs.sum_add_tsum_nat_add 1
  have HT := ht.sum_add_tsum_nat_add 1
  have HP := tsum_even_add_odd (f := fun n : ℕ => q ^ ((n + 1) * (n + 2))) he ho
  simp only [Function.comp_def, Nat.add_assoc, Nat.reduceAdd] at he ho HP
  have hsum : Summable (fun n : ℕ => q ^ ((2 * n + 1) * (2 * n + 2)) +
      q ^ ((2 * n + 2) * (2 * n + 3))) := he.add ho
  have H := Summable.tsum_lt_tsum (fun n => (hpoint n).le) (hpoint 0) (ht1.mul_left 2) hsum
  rw [tsum_mul_left] at H
  rw [← he.tsum_add ho] at HP
  rw [HP] at H
  rw [jacobiThetaTwoReducedQ_eq_two_mul_tsum hq0 hq1,
    jacobiThetaThreeNullQ_eq_two_mul_tsum_sub_one (pow_pos hq0 4)
      (pow_lt_one₀ hq0.le hq1 (by decide : (4 : ℕ) ≠ 0))]
  simp only [Finset.sum_range_one, zero_mul, mul_zero, pow_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0)] at HS HT
  have HX : ∑' n : ℕ, (q ^ 4) ^ (n ^ 2) = ∑' n : ℕ, q ^ (4 * n ^ 2) := by
    simp only [pow_mul]
  rw [HX]
  have HSc : ∑' n : ℕ, q ^ ((n + 1) * ((n + 1) + 1)) =
      ∑' n : ℕ, q ^ ((n + 1) * (n + 2)) := by rfl
  rw [HSc] at HS
  linarith only [H, HS, HT]
end DLMF.JacobiElliptic
