/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Positivity.Finset

/-!
# Elementary argument reductions (DLMF §4.45)

The exact argument transformations are retained; the worked decimal example
4.45.12–14 is excluded as numerical. Upstream logarithm, exponential and
periodicity identities are recorded in `Elementary.MathlibCoverage`.
-/

@[expose] public noncomputable section

open Filter
open scoped Real Topology

namespace DLMF.Elementary

/-- The small logarithm argument obtained after `m` square roots. -/
@[dlmf 4.45.E1]
def logReductionArgument (x : ℝ) (m : ℕ) : ℝ := x ^ ((2 : ℝ) ^ (-(m : ℤ))) - 1

/-- Repeated square roots make the logarithm-series argument arbitrarily small. -/
@[dlmf 4.45.i]
theorem logReductionArgument_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (logReductionArgument x) atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℤ))) atTop (𝓝 0) := by
    simpa [zpow_neg, one_div] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
  change Tendsto (fun m : ℕ => x ^ ((2 : ℝ) ^ (-(m : ℤ))) - 1) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.rpow_zero, sub_self] using
    (((Real.continuous_const_rpow hx.ne').tendsto 0).comp hpow).sub_const 1

/-- Nearest decimal scaling exponent for a real exponential argument. -/
@[dlmf 4.45.E4]
def expReductionIndex (x : ℝ) : ℤ := ⌊x / Real.log 10 + 1 / 2⌋

/-- The reduced real exponential argument. -/
@[dlmf 4.45.E4]
def expReductionArgument (x : ℝ) : ℝ := x - expReductionIndex x * Real.log 10

/-- Nearest half-turn index for a real trigonometric argument. -/
@[dlmf 4.45.E6]
def trigReductionIndex (x : ℝ) : ℤ := ⌊x / Real.pi + 1 / 2⌋

/-- The reduced trigonometric angle, algebraically `π (x/π - m)`. -/
@[dlmf 4.45.E6]
def trigReductionAngle (x : ℝ) : ℝ := x - trigReductionIndex x * Real.pi

/-- Scaled form of Mathlib’s `abs_sub_round`: reduction stays within half a period. -/
theorem abs_sub_nearest_mul_le (x : ℝ) {L : ℝ} (hL : 0 < L) :
    |x - (⌊x / L + 1 / 2⌋ : ℤ) * L| ≤ L / 2 := by
  have h := mul_le_mul_of_nonneg_right (abs_sub_round (x / L)) hL.le
  calc |x - (⌊x / L + 1 / 2⌋ : ℤ) * L|
      = |(x / L - (⌊x / L + 1 / 2⌋ : ℤ)) * L| := by
        congr 1
        field_simp
    _ = |x / L - (⌊x / L + 1 / 2⌋ : ℤ)| * L := by rw [abs_mul, abs_of_pos hL]
    _ ≤ 1 / 2 * L := by simpa only [round_eq] using h
    _ = L / 2 := by ring

/-- The exact exponential argument bound from the prose following 4.45.5. -/
@[dlmf 4.45.i]
theorem expReductionArgument_bound (x : ℝ) :
    |expReductionArgument x| ≤ Real.log 10 / 2 :=
  abs_sub_nearest_mul_le x (Real.log_pos (by norm_num))

/-- The exact trigonometric argument bound from the prose following 4.45.7. -/
@[dlmf 4.45.i]
theorem trigReductionAngle_bound (x : ℝ) :
    |trigReductionAngle x| ≤ Real.pi / 2 :=
  abs_sub_nearest_mul_le x Real.pi_pos

/-- The source's factored form of the reduced angle. -/
@[dlmf 4.45.E6]
theorem trigReductionAngle_eq (x : ℝ) :
    trigReductionAngle x = Real.pi * (x / Real.pi - trigReductionIndex x) := by
  dsimp [trigReductionAngle]
  field_simp

/-- One stable half-angle reduction step for the arctangent. -/
@[dlmf 4.45.E9]
def arctanReductionStep (x : ℝ) : ℝ := x / (1 + Real.sqrt (1 + x ^ 2))

/-- The arctangent half-angle iteration starts at the original argument. -/
@[dlmf 4.45.E9]
def arctanReductionSequence (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => arctanReductionStep (arctanReductionSequence x n)

/-- Positive arguments stay positive under half-angle reduction. -/
theorem arctanReductionStep_pos {x : ℝ} (hx : 0 < x) : 0 < arctanReductionStep x := by
  exact div_pos hx (by positivity)

/-- The stable half-angle identity in the source. -/
@[dlmf 4.45.E8]
theorem arctanReductionStep_identity {x : ℝ} (hx : 0 < x) :
    2 * Real.arctan (arctanReductionStep x) = Real.arctan x := by
  let s := Real.sqrt (1 + x ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hden : 0 < 1 + s := by positivity
  have hlt : arctanReductionStep x < 1 := by
    change x / (1 + s) < 1
    apply (div_lt_one hden).mpr
    nlinarith
  rw [Real.two_mul_arctan (by linarith [arctanReductionStep_pos hx]) hlt]
  congr 1
  change 2 * (x / (1 + s)) / (1 - (x / (1 + s)) ^ 2) = x
  change x / (1 + s) < 1 at hlt
  have hd : 1 - (x / (1 + s)) ^ 2 ≠ 0 := by
    have hp := arctanReductionStep_pos hx
    change 0 < x / (1 + s) at hp
    nlinarith
  apply (div_eq_iff hd).mpr
  field_simp
  linear_combination -hs2

/-- All iterated arguments remain positive. -/
theorem arctanReductionSequence_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 < arctanReductionSequence x n := by
  induction n with
  | zero => exact hx
  | succ n ih => exact arctanReductionStep_pos ih

/-- Every positive half-angle step reduces the argument by at least a factor two. -/
theorem arctanReductionStep_le_half {x : ℝ} (hx : 0 < x) :
    arctanReductionStep x ≤ x / 2 := by
  have hs := Real.sqrt_nonneg (1 + x ^ 2)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hone : 1 ≤ Real.sqrt (1 + x ^ 2) := by nlinarith [sq_nonneg x]
  exact div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)

/-- The repeated half-angle arguments admit a geometric bound. -/
@[dlmf 4.45.i]
theorem arctanReductionSequence_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    arctanReductionSequence x n ≤ x * (1 / 2) ^ n := by
  induction n with
  | zero => simp [arctanReductionSequence]
  | succ n ih =>
    calc arctanReductionSequence x (n + 1)
        ≤ arctanReductionSequence x n / 2 :=
          arctanReductionStep_le_half (arctanReductionSequence_pos hx n)
      _ ≤ (x * (1 / 2) ^ n) / 2 := by gcongr
      _ = x * (1 / 2) ^ (n + 1) := by rw [pow_succ]; ring

/-- Repeated arctangent reduction eventually gives an arbitrarily small argument. -/
@[dlmf 4.45.i]
theorem arctanReductionSequence_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (arctanReductionSequence x) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => x * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => (arctanReductionSequence_pos hx n).le) (arctanReductionSequence_le hx)

/-- Reconstruction after any finite number of half-angle steps. -/
@[dlmf 4.45.E10]
theorem arctanReductionSequence_identity {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.arctan x = 2 ^ n * Real.arctan (arctanReductionSequence x n) := by
  induction n with
  | zero => simp [arctanReductionSequence]
  | succ n ih =>
    rw [ih, pow_succ, arctanReductionSequence]
    rw [mul_assoc, arctanReductionStep_identity (arctanReductionSequence_pos hx n)]

end DLMF.Elementary
