/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Polylog.Basic.Series

/-!
# The real dilogarithm: definition and basic properties (DLMF §25.12(i))

The real dilogarithm `Real.dilog x = ∫₀ˣ -log(1-t)/t dt` for `x ≤ 1` (DLMF 25.12.2,
Duverney (8.13)), its derivative, and its identification with the series `Li₂` of
`DLMF.Polylog.Basic.Series` on `[-1, 1]`.

## Main definitions

* `dilogKernel`: the kernel `-log(1-t)/t`, extended by its limit `1` at `t = 0`.
* `Real.dilog`: the real dilogarithm (DLMF 25.12.2).

## Main results

* `Real.hasDerivAt_dilog`, `Real.dilog_zero`: `Li₂'(x) = -log(1-x)/x` on `(-∞, 1)`, and
  `Li₂(0) = 0`.
* `polylogSeries_two_ofReal_eq_dilog`: the series `Li₂` agrees with `Real.dilog` on `[-1, 1]`
  (DLMF 25.12.2).
* `Real.dilog_one`, `Real.dilog_neg_one`: `Li₂(1) = π²/6`, `Li₂(-1) = -π²/12`.
* `Real.continuousOn_dilog`: `Real.dilog` is continuous on `[-1, 1]`.

## Implementation notes

At the endpoints `±1` the identification with the series uses integrability of the
nonnegative kernel against the continuous series. The functional equations of the dilogarithm
are in `DLMF.Polylog.Dilog`. The complex polylogarithm `DLMF.Zeta.polylog` of arbitrary order
(the continuation to `ℂ \ [1, ∞)`) is defined separately in `DLMF.Zeta.Basic.Polylog`.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Polylog

open DLMF.Zeta (polylogSeries polylogSeries_natCast polylogSeries_zero_arg)

/-- The kernel `-log(1-t)/t`, extended by its limit `1` at `t = 0`. -/
def dilogKernel (t : ℝ) : ℝ := dslope (fun t => -Real.log (1 - t)) 0 t

/-- The kernel away from `0`. -/
theorem dilogKernel_of_ne {t : ℝ} (ht : t ≠ 0) : dilogKernel t = -Real.log (1 - t) / t := by
  rw [dilogKernel, dslope_of_ne _ ht, slope_def_field]
  simp

/-- The kernel at `0`. -/
theorem dilogKernel_zero : dilogKernel 0 = 1 := by
  rw [dilogKernel, dslope_same]
  have h : HasDerivAt (fun t : ℝ => -Real.log (1 - t)) 1 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)).fun_neg
    convert this using 1 <;> simp
  exact h.deriv

/-- The kernel is continuous on `(-∞, 1)`. -/
theorem continuousAt_dilogKernel {t : ℝ} (ht : t < 1) : ContinuousAt dilogKernel t := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => -Real.log (1 - t)) t :=
    (((differentiableAt_id).const_sub 1).log (by simp; linarith)).fun_neg
  by_cases h0 : t = 0
  · subst h0; exact continuousAt_dslope_same.mpr hd
  · exact (continuousAt_dslope_of_ne h0).mpr hd.continuousAt

/-- The real dilogarithm `Li₂(x) = ∫₀ˣ -log(1-t)/t dt`, meaningful for `x ≤ 1` (Duverney (8.13)). -/
@[dlmf 25.12.E2]
def Real.dilog (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, dilogKernel t

/-- The kernel is continuous on `(-∞, 1)`. -/
theorem continuousOn_dilogKernel : ContinuousOn dilogKernel (Iio 1) :=
  fun _ ht => (continuousAt_dilogKernel ht).continuousWithinAt

/-- The kernel is integrable on compact subintervals of `(-∞, 1)`. -/
theorem intervalIntegrable_dilogKernel {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    IntervalIntegrable dilogKernel MeasureTheory.volume a b :=
  (continuousOn_dilogKernel.mono fun t ht => by
    rw [mem_uIcc] at ht; rcases ht with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [mem_Iio] <;>
      linarith).intervalIntegrable

/-- `Li₂' = -log(1-x)/x` on `(-∞, 1)`. -/
theorem Real.hasDerivAt_dilog {x : ℝ} (hx : x < 1) : HasDerivAt Real.dilog (dilogKernel x) x :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_dilogKernel (by norm_num) hx)
    (continuousOn_dilogKernel.stronglyMeasurableAtFilter isOpen_Iio x hx)
    (continuousAt_dilogKernel hx)

/-- `Li₂(0) = 0`. -/
theorem Real.dilog_zero : Real.dilog 0 = 0 := by simp [Real.dilog]

/-- The series of `Li_n` at a real point is real. -/
theorem polylogSeries_ofReal (n : ℕ) (x : ℝ) :
    polylogSeries n x = ((∑' k : ℕ, x ^ (k + 1) / ((k : ℝ) + 1) ^ n : ℝ) : ℂ) := by
  rw [polylogSeries_natCast, ofReal_tsum]
  push_cast
  rfl

/-- The derivative series of `Li₂` at a real point of `(-1, 1)` is the kernel. -/
theorem tsum_eq_dilogKernel {x : ℝ} (hx : |x| < 1) :
    ∑' k : ℕ, (x : ℂ) ^ k / ((k : ℂ) + 1) ^ 1 = (dilogKernel x : ℂ) := by
  have hxn : ‖(x : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_eq_abs]
  by_cases h0 : x = 0
  · subst h0
    rw [dilogKernel_zero, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
    simp
  · have hd := (hasDerivAt_polylogSeries_div 1 hxn (ofReal_ne_zero.mpr h0)).deriv
    rw [(hasDerivAt_polylogSeries 1 hxn).deriv] at hd
    rw [hd, Nat.cast_one, polylogSeries_one hxn, dilogKernel_of_ne h0]
    have h1 : (0 : ℝ) < 1 - x := by linarith [abs_lt.mp hx]
    rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log h1.le]
    push_cast; ring

/-- Along the real segment `(-1, 1)` the series `Li₂` has derivative the kernel. -/
theorem hasDerivAt_polylogSeries_two_ofReal {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun t : ℝ => polylogSeries 2 t) (dilogKernel x : ℂ) x := by
  have hxn : ‖(x : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_eq_abs]
  have h := (hasDerivAt_polylogSeries 1 hxn).comp_ofReal
  rw [show ((1 + 1 : ℕ) : ℂ) = 2 by norm_num] at h
  exact h.congr_deriv (tsum_eq_dilogKernel hx)

/-- `Li_n` is continuous on the closed unit disk for `n ≥ 2`. -/
theorem continuousOn_polylogSeries {n : ℕ} (hn : 2 ≤ n) :
    ContinuousOn (polylogSeries n) (Metric.closedBall 0 1) := by
  rw [show polylogSeries n = fun z => ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ n
    from funext (polylogSeries_natCast n)]
  exact continuousOn_tsum (fun k => (by fun_prop : Continuous fun z : ℂ =>
      z ^ (k + 1) / ((k : ℂ) + 1) ^ n).continuousOn) (summable_one_div_succ_pow hn)
    (fun k z hz => norm_term_le n (by simpa using hz) k)

/-- The series `Li₂` agrees with the integral `Real.dilog` on `(-1, 1)`. -/
theorem polylogSeries_two_ofReal_eq_dilog_of_abs_lt {x : ℝ} (hx : |x| < 1) :
    polylogSeries 2 x = Real.dilog x := by
  set D : ℝ → ℂ := fun t => polylogSeries 2 t - Real.dilog t
  have hD (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt D 0 t := by
    have ht' : |t| < 1 := abs_lt.mpr ht
    have h := (hasDerivAt_polylogSeries_two_ofReal ht').fun_sub
      (Real.hasDerivAt_dilog (by linarith [ht.2])).ofReal_comp
    simpa using h
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
    (fun t ht => (hD t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hD t ht).deriv) (abs_lt.mp hx) (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num)
  simp only [D, ofReal_zero, polylogSeries_zero_arg, Real.dilog_zero, sub_zero] at hc
  exact sub_eq_zero.mp hc

/-- The kernel is nonnegative on `(-1, 1)`. -/
theorem dilogKernel_nonneg {t : ℝ} (ht : |t| < 1) : 0 ≤ dilogKernel t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [dilogKernel_of_ne h.ne]
    exact div_nonneg_of_nonpos (neg_nonpos.mpr (Real.log_nonneg (by linarith))) h.le
  · subst h; rw [dilogKernel_zero]; norm_num
  · rw [dilogKernel_of_ne h.ne']
    exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (by linarith [abs_lt.mp ht])
      (by linarith))) h.le

/-- The real part of the series, continuous on `[-1, 1]`. -/
theorem continuousOn_re_polylogSeries_two :
    ContinuousOn (fun t : ℝ => (polylogSeries 2 t).re) (Icc (-1) 1) :=
  continuous_re.comp_continuousOn ((by simpa using continuousOn_polylogSeries (n := 2) le_rfl :
    ContinuousOn (polylogSeries 2) (Metric.closedBall 0 1)).comp
    continuous_ofReal.continuousOn fun t ht => by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ht)

/-- The real part of the series has derivative the kernel on `(-1, 1)`. -/
theorem hasDerivAt_re_polylogSeries_two {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (fun t : ℝ => (polylogSeries 2 t).re) (dilogKernel t) t := by
  have h := reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_polylogSeries_two_ofReal ht)
  simp only [Function.comp_def, reCLM_apply, ofReal_re] at h
  exact h

/-- `∫ₐᵇ` of the kernel through the series, for `-1 ≤ a ≤ b ≤ 1`. -/
theorem integral_dilogKernel_eq {a b : ℝ} (hab : a ≤ b) (ha : -1 ≤ a) (hb : b ≤ 1) :
    ∫ t in a..b, dilogKernel t = (polylogSeries 2 b).re - (polylogSeries 2 a).re := by
  have hsub : Icc a b ⊆ Icc (-1) 1 := Icc_subset_Icc ha hb
  have hcont := continuousOn_re_polylogSeries_two.mono hsub
  have hd : ∀ t ∈ Ioo a b, HasDerivAt (fun t : ℝ => (polylogSeries 2 t).re) (dilogKernel t) t :=
    fun t ht => hasDerivAt_re_polylogSeries_two
        (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hint : IntervalIntegrable dilogKernel MeasureTheory.volume a b := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg
        (g := fun t : ℝ => (polylogSeries 2 t).re)
      (by rwa [uIcc_of_le hab]) ?_ ?_
    · intro t ht; rw [min_eq_left hab, max_eq_right hab] at ht; exact hd t ht
    · intro t ht; rw [min_eq_left hab, max_eq_right hab] at ht
      exact dilogKernel_nonneg (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hd hint

/-- The series `Li₂` agrees with `Real.dilog` on `[-1, 1]` (Duverney (8.13)). -/
@[dlmf 25.12.E2]
theorem polylogSeries_two_ofReal_eq_dilog {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    polylogSeries 2 x = Real.dilog x := by
  have hre : polylogSeries 2 x = ((polylogSeries 2 x).re : ℂ) := by
    have h := polylogSeries_ofReal 2 x
    rw [Nat.cast_ofNat] at h
    rw [h]; simp
  rcases le_total 0 x with h | h
  · rw [Real.dilog, integral_dilogKernel_eq h (by norm_num) hx.2, ofReal_zero,
      polylogSeries_zero_arg]
    simpa using hre
  · rw [Real.dilog, intervalIntegral.integral_symm, integral_dilogKernel_eq h hx.1 (by norm_num),
      ofReal_zero, polylogSeries_zero_arg]
    simpa using hre

/-- `Li₂(1) = π²/6`. -/
theorem Real.dilog_one : Real.dilog 1 = π ^ 2 / 6 := by
  have h := polylogSeries_two_ofReal_eq_dilog (x := 1) (by norm_num)
  rw [ofReal_one, polylogSeries_two_one] at h
  exact_mod_cast h.symm

/-- `Li₂(-1) = -π²/12`. -/
theorem Real.dilog_neg_one : Real.dilog (-1) = -π ^ 2 / 12 := by
  have h := polylogSeries_two_ofReal_eq_dilog (x := -1) (by norm_num)
  rw [ofReal_neg, ofReal_one, polylogSeries_two_neg_one] at h
  exact_mod_cast h.symm

/-- `Real.dilog` is continuous on `[-1, 1]`. -/
theorem Real.continuousOn_dilog : ContinuousOn Real.dilog (Icc (-1) 1) := by
  refine continuousOn_re_polylogSeries_two.congr fun x hx => ?_
  simp only [polylogSeries_two_ofReal_eq_dilog hx, ofReal_re]

end DLMF.Polylog

end
