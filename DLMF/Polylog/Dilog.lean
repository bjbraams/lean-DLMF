/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Polylog.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The real dilogarithm (Duverney §8.1.2; DLMF §25.12(i))

`Real.dilog x = ∫₀ˣ -log(1-t)/t dt` is defined for real `x ≤ 1`; the kernel is extended by its limit
`1` at `t = 0` (`dslope`). On `[-1, 1]` it agrees with the series `Li₂` of `DLMF.Polylog.Basic`;
the endpoints use integrability of the nonnegative kernel against the continuous series. Euler's
reflection formula, Landen's identity, the inversion formula and the duplication formula follow by
the derivative-equals-zero method, giving `Li₂(1/2)` and the golden-ratio values.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Polylog

/-- The kernel `-log(1-t)/t`, extended by its limit `1` at `t = 0`. -/
def dilogKernel (t : ℝ) : ℝ := dslope (fun t => -Real.log (1 - t)) 0 t

/-- The kernel away from `0`. -/
lemma dilogKernel_of_ne {t : ℝ} (ht : t ≠ 0) : dilogKernel t = -Real.log (1 - t) / t := by
  rw [dilogKernel, dslope_of_ne _ ht, slope_def_field]
  simp

/-- The kernel at `0`. -/
lemma dilogKernel_zero : dilogKernel 0 = 1 := by
  rw [dilogKernel, dslope_same]
  have h : HasDerivAt (fun t : ℝ => -Real.log (1 - t)) 1 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)).fun_neg
    convert this using 1 <;> simp
  exact h.deriv

/-- The kernel is continuous on `(-∞, 1)`. -/
lemma continuousAt_dilogKernel {t : ℝ} (ht : t < 1) : ContinuousAt dilogKernel t := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => -Real.log (1 - t)) t :=
    (((differentiableAt_id).const_sub 1).log (by simp; linarith)).fun_neg
  by_cases h0 : t = 0
  · subst h0; exact continuousAt_dslope_same.mpr hd
  · exact (continuousAt_dslope_of_ne h0).mpr hd.continuousAt

/-- The real dilogarithm `Li₂(x) = ∫₀ˣ -log(1-t)/t dt`, meaningful for `x ≤ 1` (Duverney (8.13)). -/
@[dlmf 25.12.E2]
def Real.dilog (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, dilogKernel t

/-- The kernel is continuous on `(-∞, 1)`. -/
lemma continuousOn_dilogKernel : ContinuousOn dilogKernel (Iio 1) :=
  fun _ ht => (continuousAt_dilogKernel ht).continuousWithinAt

/-- The kernel is integrable on compact subintervals of `(-∞, 1)`. -/
lemma intervalIntegrable_dilogKernel {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    IntervalIntegrable dilogKernel MeasureTheory.volume a b :=
  (continuousOn_dilogKernel.mono fun t ht => by
    rw [mem_uIcc] at ht; rcases ht with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [mem_Iio] <;>
      linarith).intervalIntegrable

/-- `Li₂' = -log(1-x)/x` on `(-∞, 1)`. -/
lemma Real.hasDerivAt_dilog {x : ℝ} (hx : x < 1) : HasDerivAt Real.dilog (dilogKernel x) x :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_dilogKernel (by norm_num) hx)
    (continuousOn_dilogKernel.stronglyMeasurableAtFilter isOpen_Iio x hx)
    (continuousAt_dilogKernel hx)

/-- `Li₂(0) = 0`. -/
lemma Real.dilog_zero : Real.dilog 0 = 0 := by simp [Real.dilog]

/-- The series of `Li_n` at a real point is real. -/
lemma polylogSeries_ofReal (n : ℕ) (x : ℝ) :
    polylogSeries n x = ((∑' k : ℕ, x ^ (k + 1) / ((k : ℝ) + 1) ^ n : ℝ) : ℂ) := by
  rw [polylogSeries, ofReal_tsum]
  push_cast
  rfl

/-- The derivative series of `Li₂` at a real point of `(-1, 1)` is the kernel. -/
lemma tsum_eq_dilogKernel {x : ℝ} (hx : |x| < 1) :
    ∑' k : ℕ, (x : ℂ) ^ k / ((k : ℂ) + 1) ^ 1 = (dilogKernel x : ℂ) := by
  have hxn : ‖(x : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_eq_abs]
  by_cases h0 : x = 0
  · subst h0
    rw [dilogKernel_zero, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
    simp
  · have hd := (hasDerivAt_polylogSeries_div 1 hxn (ofReal_ne_zero.mpr h0)).deriv
    rw [(hasDerivAt_polylogSeries 1 hxn).deriv] at hd
    rw [hd, polylogSeries_one hxn, dilogKernel_of_ne h0]
    have h1 : (0 : ℝ) < 1 - x := by linarith [abs_lt.mp hx]
    rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log h1.le]
    push_cast; ring

/-- Along the real segment `(-1, 1)` the series `Li₂` has derivative the kernel. -/
lemma hasDerivAt_polylogSeries_two_ofReal {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun t : ℝ => polylogSeries 2 t) (dilogKernel x : ℂ) x := by
  have hxn : ‖(x : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_eq_abs]
  have h := (hasDerivAt_polylogSeries 1 hxn).comp_ofReal
  exact h.congr_deriv (tsum_eq_dilogKernel hx)

/-- `Li_n` is continuous on the closed unit disk for `n ≥ 2`. -/
lemma continuousOn_polylogSeries {n : ℕ} (hn : 2 ≤ n) :
    ContinuousOn (polylogSeries n) (Metric.closedBall 0 1) :=
  continuousOn_tsum (fun k => (by fun_prop : Continuous fun z : ℂ =>
      z ^ (k + 1) / ((k : ℂ) + 1) ^ n).continuousOn) (summable_one_div_succ_pow hn)
    (fun k z hz => norm_term_le n (by simpa using hz) k)

/-- `Li_n(0) = 0`. -/
lemma polylogSeries_zero_arg (n : ℕ) : polylogSeries n 0 = 0 := by simp [polylogSeries]

/-- The series `Li₂` agrees with the integral `Real.dilog` on `(-1, 1)`. -/
lemma polylogSeries_two_ofReal_eq_dilog_of_abs_lt {x : ℝ} (hx : |x| < 1) :
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
lemma dilogKernel_nonneg {t : ℝ} (ht : |t| < 1) : 0 ≤ dilogKernel t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [dilogKernel_of_ne h.ne]
    exact div_nonneg_of_nonpos (neg_nonpos.mpr (Real.log_nonneg (by linarith))) h.le
  · subst h; rw [dilogKernel_zero]; norm_num
  · rw [dilogKernel_of_ne h.ne']
    exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (by linarith [abs_lt.mp ht])
      (by linarith))) h.le

/-- The real part of the series, continuous on `[-1, 1]`. -/
lemma continuousOn_re_polylogSeries_two :
    ContinuousOn (fun t : ℝ => (polylogSeries 2 t).re) (Icc (-1) 1) :=
  continuous_re.comp_continuousOn ((continuousOn_polylogSeries le_rfl).comp
    continuous_ofReal.continuousOn fun t ht => by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ht)

/-- The real part of the series has derivative the kernel on `(-1, 1)`. -/
lemma hasDerivAt_re_polylogSeries_two {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (fun t : ℝ => (polylogSeries 2 t).re) (dilogKernel t) t := by
  have h := reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_polylogSeries_two_ofReal ht)
  simp only [Function.comp_def, reCLM_apply, ofReal_re] at h
  exact h

/-- `∫ₐᵇ` of the kernel through the series, for `-1 ≤ a ≤ b ≤ 1`. -/
lemma integral_dilogKernel_eq {a b : ℝ} (hab : a ≤ b) (ha : -1 ≤ a) (hb : b ≤ 1) :
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
    rw [polylogSeries_ofReal]; simp
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
lemma Real.continuousOn_dilog : ContinuousOn Real.dilog (Icc (-1) 1) := by
  refine continuousOn_re_polylogSeries_two.congr fun x hx => ?_
  simp only [polylogSeries_two_ofReal_eq_dilog hx, ofReal_re]

/-- `log(1-y) log y → 0` as `y → 0⁺`. -/
lemma tendsto_log_mul_log_one_sub :
    Tendsto (fun y : ℝ => Real.log y * Real.log (1 - y)) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos).const_mul 2
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ (by simpa only [norm_zero] using h.norm)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
  obtain ⟨hy0, hy1⟩ := hy
  have hl1 : Real.log (1 - y) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hl2 : -(2 * y) ≤ Real.log (1 - y) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - y by linarith)
    have hp : 0 < 1 - y := by linarith
    have h2 : 1 - (1 - y)⁻¹ ≥ -(2 * y) := by
      rw [show 1 - (1 - y)⁻¹ = -(y / (1 - y)) by field_simp; ring, ge_iff_le, neg_le_neg_iff,
        div_le_iff₀ hp]
      nlinarith
    linarith
  rw [Real.rpow_one]
  simp only [norm_mul, Real.norm_eq_abs, abs_two, abs_of_pos hy0, abs_of_nonpos hl1]
  have : |Real.log y| * -Real.log (1 - y) ≤ |Real.log y| * (2 * y) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith

/-- **Euler's reflection formula** `Li₂(x) + Li₂(1-x) = π²/6 - ln x ln(1-x)` on `(0, 1)`
(Duverney (8.18), DLMF 25.12.6). -/
@[dlmf 25.12.E6]
theorem Real.dilog_add_dilog_one_sub {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.dilog x + Real.dilog (1 - x) = π ^ 2 / 6 - Real.log x * Real.log (1 - x) := by
  set R : ℝ → ℝ := fun x => Real.dilog x + Real.dilog (1 - x) + Real.log x * Real.log (1 - x)
  have hd (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : HasDerivAt R 0 y := by
    obtain ⟨hy0, hy1⟩ := hy
    have h1 := Real.hasDerivAt_dilog hy1
    have h2 := (Real.hasDerivAt_dilog (show 1 - y < 1 by linarith)).comp y
      ((hasDerivAt_id y).const_sub 1)
    have h3 := (Real.hasDerivAt_log hy0.ne').mul
      (((hasDerivAt_id y).const_sub 1).log (show 1 - id y ≠ 0 by simp; linarith))
    have h := (h1.add h2).add h3
    refine h.congr_deriv ?_
    rw [dilogKernel_of_ne hy0.ne', dilogKernel_of_ne (show 1 - y ≠ 0 by linarith)]
    simp only [id, sub_sub_cancel]
    have : (1 - y) ≠ 0 := by linarith
    field_simp
    ring
  have hc : ∀ y ∈ Ioo (0 : ℝ) 1, R y = R (1 / 2) := fun y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 1).isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv) hy (by norm_num)
  -- the limit at `0⁺`
  have hlim : Tendsto R (𝓝[>] 0) (𝓝 (π ^ 2 / 6)) := by
    have e1 : Tendsto Real.dilog (𝓝[>] 0) (𝓝 0) := by
      have := (Real.hasDerivAt_dilog (show (0 : ℝ) < 1 by norm_num)).continuousAt.tendsto
      rw [Real.dilog_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have e2 : Tendsto (fun y => Real.dilog (1 - y)) (𝓝[>] 0) (𝓝 (π ^ 2 / 6)) := by
      have hc1 := Real.continuousOn_dilog 1 (by norm_num)
      rw [ContinuousWithinAt, Real.dilog_one] at hc1
      refine hc1.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
      · have := ((tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have := (e1.add e2).add tendsto_log_mul_log_one_sub
    simpa using this
  have hev : R =ᶠ[𝓝[>] 0] fun _ => R (1 / 2) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy
    exact hc y hy
  have hval : R (1 / 2) = π ^ 2 / 6 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim
  have := hc x hx
  rw [hval] at this
  simp only [R] at this
  linarith

/-- `Li₂(1/2) = π²/12 - (ln 2)²/2` (Duverney (8.19)). -/
theorem Real.dilog_one_half : Real.dilog (1 / 2) = π ^ 2 / 12 - Real.log 2 ^ 2 / 2 := by
  have h := Real.dilog_add_dilog_one_sub (x := 1 / 2) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, Real.log_inv] at h
  linarith

/-- **Landen's identity** `Li₂(x) + Li₂(x/(x-1)) = -½ ln²(1-x)` for `x < 1`
(Duverney (8.20)). -/
@[dlmf 25.12.E3]
theorem Real.dilog_add_dilog_div_sub_one {x : ℝ} (hx : x < 1) :
    Real.dilog x + Real.dilog (x / (x - 1)) = -(Real.log (1 - x) ^ 2 / 2) := by
  set L : ℝ → ℝ := fun x => Real.dilog x + Real.dilog (x / (x - 1)) + Real.log (1 - x) ^ 2 / 2
  have hd (y : ℝ) (hy : y ∈ Iio (1 : ℝ)) : HasDerivAt L 0 y := by
    have hy1 : y < 1 := hy
    have hy1' : y - 1 ≠ 0 := by linarith
    have hq : HasDerivAt (fun y : ℝ => y / (y - 1)) (-1 / (y - 1) ^ 2) y := by
      have := (hasDerivAt_id y).div ((hasDerivAt_id y).sub_const 1) hy1'
      refine this.congr_deriv ?_
      simp only [id]; field_simp; ring
    have hlt : y / (y - 1) < 1 := by
      rw [div_lt_one_of_neg (by linarith)]; linarith
    have h1 := Real.hasDerivAt_dilog hy1
    have h2 := (Real.hasDerivAt_dilog hlt).comp y hq
    have h3 := ((((hasDerivAt_id y).const_sub 1).log (show 1 - id y ≠ 0 by simp; linarith)).pow
      2).div_const 2
    have h := (h1.add h2).add h3
    refine h.congr_deriv ?_
    by_cases h0 : y = 0
    · subst h0; simp [dilogKernel_zero]
    · have hq0 : y / (y - 1) ≠ 0 := div_ne_zero h0 hy1'
      have h1y : 1 - y ≠ 0 := by linarith
      rw [dilogKernel_of_ne h0, dilogKernel_of_ne hq0,
        show 1 - y / (y - 1) = (1 - y)⁻¹ by field_simp; ring, Real.log_inv]
      simp only [id]
      field_simp
      ring
  have hc := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (1 : ℝ)).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) (show x ∈ Iio (1 : ℝ) from hx)
    (show (0 : ℝ) ∈ Iio (1 : ℝ) by norm_num)
  simp only [L, zero_div, Real.dilog_zero, sub_zero, Real.log_one] at hc
  norm_num at hc
  linarith

/-- **The inversion formula** `Li₂(x) + Li₂(1/x) = -π²/6 - ½ ln²(-x)` for `x < 0`
(Duverney, Exercise 8.11). -/
@[dlmf 25.12.E4]
theorem Real.dilog_add_dilog_recip {x : ℝ} (hx : x < 0) :
    Real.dilog x + Real.dilog x⁻¹ = -(π ^ 2 / 6) - Real.log (-x) ^ 2 / 2 := by
  set I : ℝ → ℝ := fun x => Real.dilog x + Real.dilog x⁻¹ + Real.log (-x) ^ 2 / 2
  have hd (y : ℝ) (hy : y ∈ Iio (0 : ℝ)) : HasDerivAt I 0 y := by
    have hy0 : y < 0 := hy
    have hinv : y⁻¹ < 1 := by have := inv_lt_zero.mpr hy0; linarith
    have h1 := Real.hasDerivAt_dilog (show y < 1 by linarith)
    have h2 := (Real.hasDerivAt_dilog hinv).comp y (hasDerivAt_inv hy0.ne)
    have h3 := ((((hasDerivAt_id y).neg).log (show -id y ≠ 0 by simp; linarith)).pow 2).div_const 2
    have h := (h1.add h2).add h3
    refine h.congr_deriv ?_
    have hyne : y ≠ 0 := hy0.ne
    rw [dilogKernel_of_ne hy0.ne, dilogKernel_of_ne (inv_ne_zero hy0.ne),
      show 1 - y⁻¹ = (1 - y) / (-y) by field_simp; ring,
      Real.log_div (by linarith) (by linarith)]
    simp only [Pi.neg_apply, id]
    field_simp
    ring
  have hc := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) (show x ∈ Iio (0 : ℝ) from hx)
    (show (-1 : ℝ) ∈ Iio (0 : ℝ) by norm_num)
  simp only [I, inv_neg, inv_one, neg_neg, Real.log_one, Real.dilog_neg_one] at hc
  norm_num at hc
  rw [Real.log_neg_eq_log]
  linarith

/-- The duplication formula `Li₂(x) + Li₂(-x) = ½ Li₂(x²)` on `[-1, 1]` (Duverney (8.16)). -/
theorem Real.dilog_add_dilog_neg {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Real.dilog x + Real.dilog (-x) = Real.dilog (x ^ 2) / 2 := by
  have hx' : ‖(x : ℂ)‖ ≤ 1 := by rw [norm_real, Real.norm_eq_abs]; exact abs_le.mpr hx
  have h := polylogSeries_add_polylogSeries_neg_of_norm_le le_rfl hx'
  have hn : -x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hs : x ^ 2 ∈ Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith [hx.1, hx.2]⟩
  rw [← ofReal_neg, ← ofReal_pow, polylogSeries_two_ofReal_eq_dilog hx,
    polylogSeries_two_ofReal_eq_dilog hn, polylogSeries_two_ofReal_eq_dilog hs] at h
  have h' : ((Real.dilog x + Real.dilog (-x) : ℝ) : ℂ) = ((Real.dilog (x ^ 2) / 2 : ℝ) : ℂ) := by
    push_cast; rw [h]; ring
  exact_mod_cast h'

open scoped goldenRatio in
/-- The golden-ratio values `Li₂(φ⁻¹) = π²/10 - ln²φ`, `Li₂(φ⁻²) = π²/15 - ln²φ` and
`Li₂(-φ⁻¹) = -π²/15 + ½ ln²φ` (Duverney, Exercise 8.3; Landen's values). -/
theorem Real.dilog_goldenRatio :
    Real.dilog φ⁻¹ = π ^ 2 / 10 - Real.log φ ^ 2 ∧
      Real.dilog (φ⁻¹ ^ 2) = π ^ 2 / 15 - Real.log φ ^ 2 ∧
      Real.dilog (-φ⁻¹) = -(π ^ 2 / 15) + Real.log φ ^ 2 / 2 := by
  set a := φ⁻¹ with ha
  have hφ1 := Real.one_lt_goldenRatio
  have hφ0 : (0 : ℝ) < φ := by linarith
  have ha0 : 0 < a := inv_pos.mpr hφ0
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hφ1
  have hsq : a ^ 2 = 1 - a := by
    have h := Real.goldenRatio_sq
    have hm : a * φ = 1 := inv_mul_cancel₀ hφ0.ne'
    linear_combination (-a ^ 2) * h + (a * φ + 1 - a) * hm
  have hL : Real.log a = -Real.log φ := by rw [ha, Real.log_inv]
  have h1 := Real.dilog_add_dilog_one_sub (x := a) ⟨ha0, ha1⟩
  rw [← hsq, Real.log_pow] at h1
  have h2 := Real.dilog_add_dilog_div_sub_one (x := a ^ 2) (by nlinarith)
  rw [show a ^ 2 / (a ^ 2 - 1) = -a by
      rw [show a ^ 2 - 1 = -a by linarith]; field_simp,
    show 1 - a ^ 2 = a by linarith] at h2
  have h3 := Real.dilog_add_dilog_neg (x := a) ⟨by linarith, ha1.le⟩
  rw [hL] at h1 h2
  push_cast at h1
  refine ⟨by linarith, by linarith, by linarith⟩

end DLMF.Polylog

end
