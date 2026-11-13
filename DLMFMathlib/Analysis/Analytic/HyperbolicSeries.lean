/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Power series of weighted hyperbolic cosines and cosines

An exponentially summable sequence of weights permits exchanging its sampling sum with
the power series of `cosh` or `cos`. The resulting Taylor coefficients are the even moments
of the sampled frequencies. Absolute summability of the double series justifies the exchange.

## Main results

* `Real.summable_abs_weighted_coshSeries`: absolute double-series convergence.
* `Real.hasSum_tsum_mul_cosh`: the even moment series for a weighted sum of `cosh`.
* `Real.hasSum_tsum_mul_cos`: the alternating moment series for a weighted sum of `cos`.
-/

public noncomputable section

open Filter
open scoped Nat

namespace Real

/-- Exponential summability bounds the absolute double series of weighted hyperbolic cosines. -/
lemma summable_abs_weighted_coshSeries {ι : Type*} {w b : ι → ℝ} {ρ z : ℝ}
    (h : Summable (fun i => |w i| * exp (ρ * |b i|))) (hz : |z| ≤ ρ) :
    Summable (fun p : ι × ℕ => |w p.1| * |b p.1 * z| ^ (2 * p.2) / (2 * p.2).factorial) := by
  have hrow (i : ι) : HasSum (fun n : ℕ => |w i| * |b i * z| ^ (2 * n) / (2 * n).factorial)
      (|w i| * cosh |b i * z|) := by
    simpa only [mul_div_assoc] using (Real.hasSum_cosh |b i * z|).mul_left |w i|
  refine (summable_prod_of_nonneg (fun p => by positivity)).mpr ⟨fun i => (hrow i).summable, ?_⟩
  refine h.of_nonneg_of_le (fun i => tsum_nonneg fun n => by positivity) fun i => ?_
  rw [(hrow i).tsum_eq]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    cosh |b i * z| ≤ exp |b i * z| := by
      rw [cosh_eq]
      have he := exp_le_exp.mpr (show -|b i * z| ≤ |b i * z| by linarith [abs_nonneg (b i * z)])
      linarith
    _ ≤ exp (ρ * |b i|) := by
      rw [Real.exp_le_exp, abs_mul]
      nlinarith [abs_nonneg (b i)]

/-- A weighted sum of hyperbolic cosines has the moment power series whenever an exponential
majorant of its weights is summable. -/
lemma hasSum_tsum_mul_cosh {ι : Type*} {w b : ι → ℝ} {ρ z : ℝ}
    (h : Summable (fun i => |w i| * exp (ρ * |b i|))) (hz : |z| ≤ ρ) :
    HasSum (fun n : ℕ => (∑' i, w i * (b i) ^ (2 * n)) * z ^ (2 * n) / (2 * n).factorial)
      (∑' i, w i * cosh (b i * z)) := by
  let F : ι × ℕ → ℝ := fun p => w p.1 * (b p.1 * z) ^ (2 * p.2) / (2 * p.2).factorial
  have habs := summable_abs_weighted_coshSeries h hz
  have hF : Summable F := habs.of_norm_bounded fun p => by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  have hs := hF.prod_symm.prod.hasSum
  dsimp only [Prod.swap_prod_mk] at hs
  rw [Summable.tsum_comm (f := fun i n => F (i, n)) hF] at hs
  have hrow (i : ι) : (∑' n, F (i, n)) = w i * cosh (b i * z) := by
    exact ((Real.hasSum_cosh (b i * z)).mul_left (w i)).congr_fun
      (fun n => by dsimp only [F]; ring) |>.tsum_eq
  simp_rw [hrow] at hs
  refine hs.congr_fun fun n => ?_
  dsimp only [F]
  simp_rw [mul_pow, ← mul_assoc]
  rw [tsum_div_const, tsum_mul_right]

/-- A weighted sum of cosines has the alternating moment series under an exponential
summability hypothesis. -/
lemma hasSum_tsum_mul_cos {ι : Type*} {w b : ι → ℝ} {ρ z : ℝ}
    (h : Summable (fun i => |w i| * exp (ρ * |b i|))) (hz : |z| ≤ ρ) :
    HasSum (fun n : ℕ => (-1) ^ n * (∑' i, w i * (b i) ^ (2 * n)) *
      z ^ (2 * n) / (2 * n).factorial) (∑' i, w i * cos (b i * z)) := by
  let F : ι × ℕ → ℝ := fun p => w p.1 * ((-1) ^ p.2 *
    (b p.1 * z) ^ (2 * p.2)) / (2 * p.2).factorial
  have habs := summable_abs_weighted_coshSeries h hz
  have hF : Summable F := habs.of_norm_bounded fun p => by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_pow, Nat.abs_cast]
  have hs := hF.prod_symm.prod.hasSum
  dsimp only [Prod.swap_prod_mk] at hs
  rw [Summable.tsum_comm (f := fun i n => F (i, n)) hF] at hs
  have hrow (i : ι) : (∑' n, F (i, n)) = w i * cos (b i * z) := by
    exact ((Real.hasSum_cos (b i * z)).mul_left (w i)).congr_fun
      (fun n => by dsimp only [F]; ring) |>.tsum_eq
  simp_rw [hrow] at hs
  refine hs.congr_fun fun n => ?_
  dsimp only [F]
  simp_rw [mul_pow]
  have he (i : ι) : w i * ((-1) ^ n * (b i ^ (2 * n) * z ^ (2 * n))) =
      (-1) ^ n * (w i * b i ^ (2 * n)) * z ^ (2 * n) := by ring
  simp_rw [he]
  rw [tsum_div_const, tsum_mul_right, tsum_mul_left]

end Real
