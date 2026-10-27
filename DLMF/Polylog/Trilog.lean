/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Polylog.Dilog

/-!
# The real trilogarithm (Duverney §8.1.3)

`Real.trilog x = ∫₀ˣ Li₂(t)/t dt` for real `x ≤ 1`, with the kernel extended by `1` at `t = 0`.
It agrees with the series `Li₃` on `[-1, 1]` (on the open interval by the derivative, at the
endpoints by continuity), so `Li₃(1) = ζ(3)` and `Li₃(-1) = -¾ζ(3)`. Landen's identity for `Li₃`
(Duverney (8.33)) follows from the reflection, inversion and Landen identities for `Li₂` by the
derivative-equals-zero method, with the constant fixed by the limit `x → 1⁻`; at `x = 1/2` it gives
`Li₃(1/2) = (7/8)ζ(3) - (π²/12) ln 2 + (ln 2)³/6`.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Polylog

/-- The kernel `Li₂(t)/t`, extended by `1` at `t = 0`. -/
def trilogKernel (t : ℝ) : ℝ := dslope Real.dilog 0 t

/-- The kernel away from `0`. -/
theorem trilogKernel_of_ne {t : ℝ} (ht : t ≠ 0) : trilogKernel t = Real.dilog t / t := by
  rw [trilogKernel, dslope_of_ne _ ht, slope_def_field, Real.dilog_zero]
  simp

/-- The kernel at `0`. -/
theorem trilogKernel_zero : trilogKernel 0 = 1 := by
  rw [trilogKernel, dslope_same, (Real.hasDerivAt_dilog (by norm_num)).deriv, dilogKernel_zero]

/-- `Real.dilog` is continuous on `(-∞, 1)`. -/
theorem Real.continuousOn_dilog_Iio : ContinuousOn Real.dilog (Iio 1) :=
  fun _ ht => (Real.hasDerivAt_dilog ht).continuousAt.continuousWithinAt

/-- The kernel is continuous on `(-∞, 1)`. -/
theorem continuousOn_trilogKernel_Iio : ContinuousOn trilogKernel (Iio 1) :=
  (continuousOn_dslope (Iio_mem_nhds one_pos)).mpr
    ⟨Real.continuousOn_dilog_Iio, (Real.hasDerivAt_dilog (by norm_num)).differentiableAt⟩

/-- The kernel is continuous on `[-1, 1]`. -/
theorem continuousOn_trilogKernel_Icc : ContinuousOn trilogKernel (Icc (-1) 1) :=
  (continuousOn_dslope (Icc_mem_nhds (by norm_num) one_pos)).mpr
    ⟨Real.continuousOn_dilog, (Real.hasDerivAt_dilog (by norm_num)).differentiableAt⟩

/-- The real trilogarithm `Li₃(x) = ∫₀ˣ Li₂(t)/t dt` for `x ≤ 1` (Duverney (8.28)). -/
def Real.trilog (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, trilogKernel t

/-- `Li₃' = Li₂(x)/x` on `(-∞, 1)`. -/
theorem Real.hasDerivAt_trilog {x : ℝ} (hx : x < 1) : HasDerivAt Real.trilog (trilogKernel x) x := by
  have hint : IntervalIntegrable trilogKernel MeasureTheory.volume 0 x :=
    (continuousOn_trilogKernel_Iio.mono fun t ht => by
      rw [mem_uIcc] at ht; rcases ht with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [mem_Iio] <;>
        linarith).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_right hint
    (continuousOn_trilogKernel_Iio.stronglyMeasurableAtFilter isOpen_Iio x hx)
    (continuousOn_trilogKernel_Iio.continuousAt (Iio_mem_nhds hx))

/-- `Li₃(0) = 0`. -/
theorem Real.trilog_zero : Real.trilog 0 = 0 := by simp [Real.trilog]

/-- `Real.trilog` is continuous on `[-1, 1]`. -/
theorem Real.continuousOn_trilog : ContinuousOn Real.trilog (Icc (-1) 1) := by
  have hk : ContinuousOn trilogKernel (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num)]; exact continuousOn_trilogKernel_Icc
  have h := intervalIntegral.continuousOn_primitive_interval'
    (hk.intervalIntegrable (μ := MeasureTheory.volume))
    (show (0 : ℝ) ∈ uIcc (-1 : ℝ) 1 by rw [uIcc_of_le (by norm_num)]; norm_num)
  rwa [uIcc_of_le (by norm_num)] at h

/-- The series `Li₃` agrees with `Real.trilog` on `[-1, 1]`. -/
theorem polylogSeries_three_ofReal_eq_trilog {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    polylogSeries 3 x = Real.trilog x := by
  -- on the open interval by the derivative
  have hopen : EqOn (fun t : ℝ => polylogSeries 3 t) (fun t => (Real.trilog t : ℂ))
      (Ioo (-1) 1) := by
    set D : ℝ → ℂ := fun t => polylogSeries 3 t - Real.trilog t
    have hD (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt D 0 t := by
      have ht' : ‖(t : ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs]; exact abs_lt.mpr ht
      have h3 : HasDerivAt (fun s : ℝ => polylogSeries 3 s) (trilogKernel t : ℂ) t := by
        refine (hasDerivAt_polylogSeries 2 ht').comp_ofReal.congr_deriv ?_
        by_cases h0 : t = 0
        · subst h0
          rw [trilogKernel_zero, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
          simp
        · have hd := (hasDerivAt_polylogSeries_div 2 ht' (ofReal_ne_zero.mpr h0)).deriv
          rw [(hasDerivAt_polylogSeries 2 ht').deriv] at hd
          rw [hd, trilogKernel_of_ne h0,
            polylogSeries_two_ofReal_eq_dilog ⟨ht.1.le, ht.2.le⟩]
          push_cast; ring
      have h := h3.fun_sub (Real.hasDerivAt_trilog (by linarith [ht.2])).ofReal_comp
      simpa using h
    intro y hy
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (fun t ht => (hD t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hD t ht).deriv) hy (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num)
    simp only [D, ofReal_zero, polylogSeries_zero_arg, Real.trilog_zero, sub_zero] at hc
    exact sub_eq_zero.mp hc
  have hc1 : ContinuousOn (fun t : ℝ => polylogSeries 3 t) (Icc (-1) 1) :=
    (continuousOn_polylogSeries (by norm_num)).comp continuous_ofReal.continuousOn fun t ht => by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ht
  have hc2 : ContinuousOn (fun t : ℝ => (Real.trilog t : ℂ)) (Icc (-1) 1) :=
    continuous_ofReal.comp_continuousOn Real.continuousOn_trilog
  exact hopen.of_subset_closure hc1 hc2 Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num)]) hx

/-- `Li₃(1) = ζ(3)`. -/
theorem Real.trilog_one : (Real.trilog 1 : ℂ) = riemannZeta 3 := by
  rw [← polylogSeries_three_ofReal_eq_trilog (by norm_num), ofReal_one]
  exact polylogSeries_three_one_neg_one.1

/-- `Li₃(-1) = -¾ ζ(3)`. -/
theorem Real.trilog_neg_one : (Real.trilog (-1) : ℂ) = -(3 / 4) * riemannZeta 3 := by
  rw [← polylogSeries_three_ofReal_eq_trilog (by norm_num), ofReal_neg, ofReal_one]
  exact polylogSeries_three_one_neg_one.2

/-- **Landen's identity for `Li₃`** on `(0, 1)` (Duverney (8.33)):
`Li₃(x) + Li₃(1-x) + Li₃(1-1/x) = ζ(3) + ln³x/6 + (π²/6) ln x - ½ ln²x ln(1-x)`. -/
theorem Real.trilog_landen {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.trilog x + Real.trilog (1 - x) + Real.trilog (1 - x⁻¹) =
      Real.trilog 1 + Real.log x ^ 3 / 6 + π ^ 2 / 6 * Real.log x -
        Real.log x ^ 2 * Real.log (1 - x) / 2 := by
  set T : ℝ → ℝ := fun x => Real.trilog x + Real.trilog (1 - x) + Real.trilog (1 - x⁻¹) -
    Real.log x ^ 3 / 6 - π ^ 2 / 6 * Real.log x + Real.log x ^ 2 * Real.log (1 - x) / 2
  have hd (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : HasDerivAt T 0 y := by
    obtain ⟨hy0, hy1⟩ := hy
    have hyinv : 1 < y⁻¹ := one_lt_inv₀ hy0 |>.mpr hy1
    have hz : 1 - y⁻¹ < 0 := by linarith
    have h1 := Real.hasDerivAt_trilog hy1
    have h2 := (Real.hasDerivAt_trilog (show 1 - y < 1 by linarith)).comp y
      ((hasDerivAt_id y).const_sub 1)
    have h3 := (Real.hasDerivAt_trilog (show 1 - y⁻¹ < 1 by linarith)).comp y
      ((hasDerivAt_inv hy0.ne').const_sub 1)
    have hl := Real.hasDerivAt_log hy0.ne'
    have hl1 := ((hasDerivAt_id y).const_sub 1).log (show 1 - id y ≠ 0 by simp; linarith)
    have h := ((((h1.add h2).add h3).sub ((hl.pow 3).div_const 6)).sub
      (hl.const_mul (π ^ 2 / 6))).add (((hl.pow 2).mul hl1).div_const 2)
    refine h.congr_deriv ?_
    -- dilogarithm identities at the three points
    have R := Real.dilog_add_dilog_one_sub (x := y) ⟨hy0, hy1⟩
    have I := Real.dilog_add_dilog_recip hz
    have La := Real.dilog_add_dilog_div_sub_one hy1
    rw [show (1 - y⁻¹)⁻¹ = y / (y - 1) by field_simp,
      show -(1 - y⁻¹) = (1 - y) / y by field_simp; ring,
      Real.log_div (by linarith) hy0.ne'] at I
    rw [trilogKernel_of_ne hy0.ne', trilogKernel_of_ne (show 1 - y ≠ 0 by linarith),
      trilogKernel_of_ne hz.ne]
    simp only [id, Pi.pow_apply]
    have h1y : 1 - y ≠ 0 := by linarith
    have hy1' : y - 1 ≠ 0 := by linarith
    have hz' : 1 - y⁻¹ ≠ 0 := hz.ne
    linear_combination (norm := skip) (-1 / (1 - y)) * R + (1 / (y * (y - 1))) * I +
      (-1 / (y * (y - 1))) * La
    field_simp
    ring
  have hc : ∀ y ∈ Ioo (0 : ℝ) 1, T y = T (1 / 2) := fun y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 1).isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv) hy (by norm_num)
  -- the limit at `1⁻`
  have hmap : Tendsto (fun y : ℝ => 1 - y) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_id (x := 𝓝 (1 : ℝ)))).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.mpr hy
  have hlt1 : Tendsto (fun y : ℝ => y) (𝓝[<] 1) (𝓝[Icc (-1) 1] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_id.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with y hy
      exact ⟨by linarith [hy.1], hy.2.le⟩
  have hT0 : ContinuousAt Real.trilog 0 := (Real.hasDerivAt_trilog (by norm_num)).continuousAt
  have e1 : Tendsto Real.trilog (𝓝[<] 1) (𝓝 (Real.trilog 1)) :=
    (Real.continuousOn_trilog 1 (by norm_num)).tendsto.comp hlt1
  have e2 : Tendsto (fun y => Real.trilog (1 - y)) (𝓝[<] 1) (𝓝 0) := by
    have := hT0.tendsto.comp (hmap.mono_right nhdsWithin_le_nhds)
    rwa [Real.trilog_zero] at this
  have e3 : Tendsto (fun y : ℝ => Real.trilog (1 - y⁻¹)) (𝓝[<] 1) (𝓝 0) := by
    have hi : Tendsto (fun y : ℝ => 1 - y⁻¹) (𝓝[<] 1) (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub
        ((continuousAt_inv₀ (one_ne_zero)).tendsto)).mono_left
          (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    have := hT0.tendsto.comp hi
    rwa [Real.trilog_zero] at this
  have hlog : Tendsto Real.log (𝓝[<] 1) (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    rwa [Real.log_one] at this
  have e4 : Tendsto (fun y : ℝ => Real.log y ^ 2 * Real.log (1 - y)) (𝓝[<] 1) (𝓝 0) := by
    have h := tendsto_log_mul_log_one_sub.comp hmap
    have h' := (h.mul hlog)
    rw [zero_mul] at h'
    refine h'.congr' ?_
    filter_upwards with y
    simp only [Function.comp, sub_sub_cancel]
    ring
  have hlim : Tendsto T (𝓝[<] 1) (𝓝 (Real.trilog 1)) := by
    have := ((((e1.add e2).add e3).sub ((hlog.pow 3).div_const 6)).sub
      (hlog.const_mul (π ^ 2 / 6))).add (e4.div_const 2)
    simpa using this
  have hev : T =ᶠ[𝓝[<] 1] fun _ => T (1 / 2) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with y hy
    exact hc y hy
  have hval : T (1 / 2) = Real.trilog 1 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim
  have := hc x hx
  rw [hval] at this
  simp only [T] at this
  linarith

/-- `Li₃(1/2) = (7/8) ζ(3) - (π²/12) ln 2 + (ln 2)³/6` (Duverney (8.34)). -/
theorem Real.trilog_one_half :
    (Real.trilog (1 / 2) : ℂ) = 7 / 8 * riemannZeta 3 - π ^ 2 / 12 * Real.log 2 +
      Real.log 2 ^ 3 / 6 := by
  have h := Real.trilog_landen (x := 1 / 2) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) - (1 / 2)⁻¹ = -1 by norm_num,
    one_div, Real.log_inv] at h
  have h' := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at h'
  rw [Real.trilog_neg_one, Real.trilog_one] at h'
  rw [one_div]
  linear_combination h' / 2
