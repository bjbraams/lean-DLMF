/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Polylog.Basic.Dilog
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Functional equations of the real dilogarithm (Duverney §8.1.2; DLMF §25.12(i))

The classical functional equations and special values of the real dilogarithm `Real.dilog`.
The definition, its derivative and the identification with the series `Li₂` on `[-1, 1]`
(DLMF 25.12.2) are in the foundational module `DLMF.Polylog.Basic.Dilog`.

## Main results

* `Real.dilog_add_dilog_one_sub`: Euler's reflection formula (DLMF 25.12.6).
* `Real.dilog_one_half`: `Li₂(1/2) = π²/12 - (ln 2)²/2`.
* `Real.dilog_add_dilog_div_sub_one`: Landen's identity (DLMF 25.12.3).
* `Real.dilog_add_dilog_recip`: the inversion formula (DLMF 25.12.4).
* `Real.dilog_add_dilog_neg`: the duplication formula `Li₂(x) + Li₂(-x) = ½ Li₂(x²)`.
* `Real.dilog_goldenRatio`: the golden-ratio values.

## Implementation notes

The functional equations are proved by the derivative-equals-zero method.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Polylog

/-- `log(1-y) log y → 0` as `y → 0⁺`. -/
theorem tendsto_log_mul_log_one_sub :
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
  simp only [Nat.cast_ofNat] at h
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
