/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The polylogarithm (Duverney Chapter 8; DLMF §25.12)

`Li_n(z) = ∑_{k ≥ 1} z^k/k^n` on the closed unit disk (`n ≥ 2`) or the open disk. This file
proves `Li₁(z) = -log(1-z)`, the termwise derivative `Li_{n+1}' = Li_n/z`, `Li_n(1) = ζ(n)`, the
duplication formula `Li_n(z) + Li_n(-z) = 2^{1-n} Li_n(z²)`, the value
`Li_n(-1) = -(1 - 2^{1-n})ζ(n)`, and the identification with Mathlib's `expZeta` on the circle.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section
namespace DLMF.Polylog

/-- The polylogarithm `Li_n(z) = ∑_{k ≥ 1} z^k/k^n` (DLMF 25.12.10), as a `tsum`. It is meaningful
on the closed unit disk for `n ≥ 2` and on the open disk for all `n`. The plain name `polylog` is
reserved for the continuation to `ℂ ∖ [1, ∞)`, which is not yet defined; the real integral forms
are `Real.dilog` and `Real.trilog`. -/
@[dlmf 25.12.E10]
def polylogSeries (n : ℕ) (z : ℂ) : ℂ := ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ n

/-- The terms are bounded by `1/(k+1)^n` on the closed disk. -/
lemma norm_term_le (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ n‖ ≤ 1 / ((k : ℝ) + 1) ^ n := by
  rw [norm_div, norm_pow, norm_pow, show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; ring,
    norm_real, Real.norm_of_nonneg (by positivity)]
  gcongr
  exact pow_le_one₀ (norm_nonneg _) hz

/-- `∑ 1/(k+1)^n` converges for `n ≥ 2`. -/
lemma summable_one_div_succ_pow {n : ℕ} (hn : 2 ≤ n) :
    Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ n := by
  have h := (Real.summable_one_div_nat_pow (p := n)).mpr (by omega)
  exact (summable_nat_add_iff 1).mpr h |>.congr fun k => by push_cast; ring_nf

/-- For `n ≥ 2` the series converges absolutely on the closed unit disk. -/
lemma summable_polylogSeries {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ n :=
  Summable.of_norm_bounded (summable_one_div_succ_pow hn) (norm_term_le n hz)

/-- On the open unit disk the series converges absolutely for every `n`. -/
lemma summable_polylogSeries_of_norm_lt_one (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ n := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left
    ‖z‖) fun k => ?_
  rw [norm_div, norm_pow, norm_pow, pow_succ, mul_comm]
  have h1 : 1 ≤ ‖(k : ℂ) + 1‖ ^ n := by
    apply one_le_pow₀
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  exact div_le_self (by positivity) h1

/-- `Li₁(z) = -log(1 - z)` on the open unit disk. -/
theorem polylogSeries_one {z : ℂ} (hz : ‖z‖ < 1) : polylogSeries 1 z = -log (1 - z) := by
  rw [polylogSeries, ← (hasSum_taylorSeries_neg_log' hz).tsum_eq]
  simp

/-- `HasSum` form of the series, indexed from `0` (the `k = 0` term vanishes for `n ≥ 1`). -/
lemma hasSum_polylogSeries_zero_index {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hs : Summable fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ n) :
    HasSum (fun k : ℕ => z ^ k / (k : ℂ) ^ n) (polylogSeries n z) := by
  have h := hs.hasSum
  have h0 : z ^ 0 / ((0 : ℕ) : ℂ) ^ n = 0 := by
    simp [zero_pow (by omega : n ≠ 0)]
  rw [← hasSum_nat_add_iff' 1, Finset.sum_range_one, h0, sub_zero]
  simpa only [polylogSeries, Nat.cast_add, Nat.cast_one] using h

/-- `Li_n(1) = ζ(n)` for `n ≥ 2` (DLMF 25.12.12 generalized). -/
@[dlmf 25.12.ii]
theorem polylogSeries_one_eq_zeta {n : ℕ} (hn : 2 ≤ n) : polylogSeries n 1 = riemannZeta n := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
  have h := hasSum_polylogSeries_zero_index (by omega)
      (summable_polylogSeries hn (z := 1) (by simp))
  simp only [one_pow] at h
  exact h.tsum_eq.symm


/-- The duplication formula `Li_n(z) + Li_n(-z) = 2^{1-n} Li_n(z²)` (Duverney (8.11)),
whenever the three series converge. -/
theorem polylogSeries_add_polylogSeries_neg {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (h1 : Summable fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ n)
    (h2 : Summable fun k : ℕ => (-z) ^ (k + 1) / ((k : ℂ) + 1) ^ n)
    (h3 : Summable fun k : ℕ => (z ^ 2) ^ (k + 1) / ((k : ℂ) + 1) ^ n) :
    polylogSeries n z + polylogSeries n (-z) = 2 / 2 ^ n * polylogSeries n (z ^ 2) := by
  have hs := (hasSum_polylogSeries_zero_index hn h1).add (hasSum_polylogSeries_zero_index hn h2)
  have he : HasSum (fun k : ℕ => z ^ (2 * k) / ((2 * k : ℕ) : ℂ) ^ n +
      (-z) ^ (2 * k) / ((2 * k : ℕ) : ℂ) ^ n) (2 / 2 ^ n * polylogSeries n (z ^ 2)) := by
    have h := (hasSum_polylogSeries_zero_index hn h3).mul_left (2 / 2 ^ n)
    refine h.congr_fun fun k => ?_
    simp only [pow_mul, neg_sq, ← two_mul]
    push_cast
    rw [mul_pow]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [zero_pow (by omega : n ≠ 0)]
    · have : (k : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hk.ne')
      field_simp
  have ho : HasSum (fun k : ℕ => z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ) ^ n +
      (-z) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ) ^ n) 0 := by
    refine (hasSum_zero).congr_fun fun k => ?_
    rw [neg_pow, pow_succ (-1 : ℂ), pow_mul]
    simp
    ring
  have h := HasSum.even_add_odd (f := fun k : ℕ => z ^ k / (k : ℂ) ^ n + (-z) ^ k / (k : ℂ) ^ n)
    he ho
  rw [add_zero] at h
  exact hs.unique h

/-- The duplication formula on the closed unit disk for `n ≥ 2`. -/
theorem polylogSeries_add_polylogSeries_neg_of_norm_le {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polylogSeries n z + polylogSeries n (-z) = 2 / 2 ^ n * polylogSeries n (z ^ 2) :=
  polylogSeries_add_polylogSeries_neg (by omega) (summable_polylogSeries hn hz)
    (summable_polylogSeries hn (by rwa [norm_neg])) (summable_polylogSeries hn (by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz))

/-- `Li_n(-1) = -(1 - 2^{1-n}) ζ(n)` for `n ≥ 2` (Duverney (8.9)). -/
theorem polylogSeries_neg_one {n : ℕ} (hn : 2 ≤ n) :
    polylogSeries n (-1) = -(1 - 2 / 2 ^ n) * riemannZeta n := by
  have h := polylogSeries_add_polylogSeries_neg_of_norm_le hn (z := 1) (by simp)
  rw [one_pow, polylogSeries_one_eq_zeta hn] at h
  linear_combination h


/-- Termwise differentiation on the open unit disk:
`d/dz Li_{n+1}(z) = ∑_{k ≥ 0} z^k/(k+1)^n`. -/
theorem hasDerivAt_polylogSeries (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylogSeries (n + 1)) (∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ n) z := by
  set r : ℝ := (1 + ‖z‖) / 2
  have hr1 : r < 1 := by simp only [r]; linarith
  have hzr : ‖z‖ < r := by simp only [r]; linarith
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hd (k : ℕ) (w : ℂ) : HasDerivAt (fun w : ℂ => w ^ (k + 1) / ((k : ℂ) + 1) ^ (n + 1))
      (w ^ k / ((k : ℂ) + 1) ^ n) w := by
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h := (hasDerivAt_pow (k + 1) w).div_const (((k : ℂ) + 1) ^ (n + 1))
    refine h.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hb (k : ℕ) (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) r) :
      ‖w ^ k / ((k : ℂ) + 1) ^ n‖ ≤ r ^ k := by
    rw [mem_ball_zero_iff] at hw
    rw [norm_div, norm_pow, norm_pow]
    have h1 : 1 ≤ ‖(k : ℂ) + 1‖ ^ n := by
      apply one_le_pow₀
      rw [show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    calc ‖w‖ ^ k / ‖(k : ℂ) + 1‖ ^ n ≤ ‖w‖ ^ k := div_le_self (by positivity) h1
      _ ≤ r ^ k := by gcongr
  exact hasDerivAt_tsum_of_isPreconnected (summable_geometric_of_lt_one hr0 hr1)
    Metric.isOpen_ball (convex_ball _ _).isPreconnected (fun k w _ => hd k w) hb
    (Metric.mem_ball_self (by simp only [r]; positivity))
        (summable_polylogSeries_of_norm_lt_one (n + 1)
      (by simp)) (mem_ball_zero_iff.mpr hzr)

/-- `z ∑ z^k/(k+1)^n = Li_n(z)`, so `Li_{n+1}'(z) = Li_n(z)/z` for `z ≠ 0` (Duverney (8.2)). -/
theorem hasDerivAt_polylogSeries_div (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (polylogSeries (n + 1)) (polylogSeries n z / z) z := by
  refine (hasDerivAt_polylogSeries n hz).congr_deriv ?_
  rw [polylogSeries, eq_div_iff hz0, ← tsum_mul_right]
  exact tsum_congr fun k => by ring

/-- On the unit circle, `Li_n(e^{2πia})` is Mathlib's `expZeta a n` for `n ≥ 2`. -/
@[dlmf 25.13]
theorem polylogSeries_exp_eq_expZeta {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    polylogSeries n (exp (2 * π * I * a)) = HurwitzZeta.expZeta a n := by
  have h := HurwitzZeta.hasSum_expZeta_of_one_lt_re a (s := n) (by simp; exact_mod_cast hn)
  have hz : ‖exp (2 * π * I * a)‖ ≤ 1 := by
    rw [show 2 * (π : ℂ) * I * a = ((2 * π * a : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have hp := hasSum_polylogSeries_zero_index (by omega) (summable_polylogSeries hn hz)
  refine hp.unique (h.congr_fun fun k => ?_)
  rw [cpow_natCast, ← exp_nat_mul]
  ring_nf

/-- `Li₂(1) = π²/6` (Duverney (8.17)). -/
theorem polylogSeries_two_one : polylogSeries 2 1 = (π : ℂ) ^ 2 / 6 := by
  rw [polylogSeries_one_eq_zeta le_rfl]; exact_mod_cast riemannZeta_two

/-- `Li₂(-1) = -π²/12` (Duverney (8.17)). -/
theorem polylogSeries_two_neg_one : polylogSeries 2 (-1) = -(π : ℂ) ^ 2 / 12 := by
  rw [polylogSeries_neg_one le_rfl]
  have h : riemannZeta ((2 : ℕ) : ℂ) = (π : ℂ) ^ 2 / 6 := by exact_mod_cast riemannZeta_two
  rw [h]; ring

/-- `Li₃(1) = ζ(3)` and `Li₃(-1) = -¾ ζ(3)` (Duverney (8.31)). -/
theorem polylogSeries_three_one_neg_one :
    polylogSeries 3 1 = riemannZeta 3 ∧ polylogSeries 3 (-1) = -(3 / 4) * riemannZeta 3 := by
  refine ⟨by exact_mod_cast polylogSeries_one_eq_zeta (n := 3) (by norm_num), ?_⟩
  have h := polylogSeries_neg_one (n := 3) (by norm_num)
  push_cast at h
  rw [h]; ring

end DLMF.Polylog

end
