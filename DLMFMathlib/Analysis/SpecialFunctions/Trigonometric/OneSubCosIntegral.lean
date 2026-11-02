/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The integral of `(1 - cos x) / x²`

This file proves `∫_{-∞}^{∞} (1 - cos x) / x² dx = π`, the normalization of the Fejér kernel of
Fourier integrals.

## Main results

* `Real.integrable_one_sub_cos_div_sq`: `(1 - cos x) / x²` is integrable on `ℝ`.
* `Real.integral_one_sub_cos_div_sq`: `∫ (1 - cos x) / x² dx = π`.

## Implementation notes

On `[0, T]`, `(1 - cos x) / x² = sin x / x - h'(x)` with `h(x) = (1 - cos x) / x` (continuous at
`0` with `h(0) = 0`), so `∫_0^T (1 - cos x)/x² dx = ∫_0^T sin x / x dx - h(T)`, and the
Dirichlet integral `TauCeti.Contour.tendsto_integral_sin_div_atTop` gives the limit `π/2`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Real

/-- `(1 - cos x) / x² ≤ 4 / (1 + x²)`. -/
theorem one_sub_cos_div_sq_le_inv_one_add_sq (x : ℝ) :
    (1 - cos x) / x ^ 2 ≤ 4 * (1 + x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx2 : 0 < x ^ 2 := by positivity
  rw [div_le_iff₀ hx2, show 4 * (1 + x ^ 2)⁻¹ * x ^ 2 = 4 * x ^ 2 / (1 + x ^ 2) by
    field_simp, le_div_iff₀ (by positivity)]
  rcases le_total (x ^ 2) 1 with h | h
  · have hc : 1 - x ^ 2 / 2 ≤ cos x := one_sub_sq_div_two_le_cos
    nlinarith
  · have hc := neg_one_le_cos x
    nlinarith

/-- `(1 - cos x) / x² ≥ 0`. -/
theorem one_sub_cos_div_sq_nonneg (x : ℝ) : 0 ≤ (1 - cos x) / x ^ 2 :=
  div_nonneg (by linarith [cos_le_one x]) (sq_nonneg x)

/-- `(1 - cos x) / x²` is integrable on `ℝ`. -/
theorem integrable_one_sub_cos_div_sq : Integrable fun x : ℝ => (1 - cos x) / x ^ 2 := by
  refine (integrable_inv_one_add_sq.const_mul 4).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((continuous_const.sub continuous_cos).measurable.div
      (continuous_pow 2).measurable).aestronglyMeasurable
  · rw [norm_of_nonneg (one_sub_cos_div_sq_nonneg x)]
    exact one_sub_cos_div_sq_le_inv_one_add_sq x

/-- `∫_{-∞}^{∞} (1 - cos x) / x² dx = π`. -/
theorem integral_one_sub_cos_div_sq : ∫ x : ℝ, (1 - cos x) / x ^ 2 = π := by
  set g : ℝ → ℝ := fun x => (1 - cos x) / x ^ 2 with hgdef
  have hev : (fun x => g |x|) = g := by
    funext x; simp only [hgdef, cos_abs, sq_abs]
  have habs := integral_comp_abs (f := g)
  rw [hev] at habs
  change ∫ x, g x = π
  rw [habs]
  -- the half-line integral as a limit
  set h : ℝ → ℝ := fun x => (1 - cos x) / x with hhdef
  have hint : ∀ T : ℝ, 0 ≤ T → ∫ x in (0 : ℝ)..T, g x =
      (∫ x in (0 : ℝ)..T, sin x / x) - h T := by
    intro T hT
    have hgi : IntervalIntegrable g volume 0 T :=
      integrable_one_sub_cos_div_sq.intervalIntegrable
    have hsi : IntervalIntegrable (fun x => sin x / x) volume 0 T := by
      refine (Real.continuous_sinc.intervalIntegrable 0 T).congr fun x hx => ?_
      have hx0 : 0 < x := by rw [uIoc, min_eq_left hT] at hx; exact hx.1
      exact Real.sinc_of_ne_zero hx0.ne'
    have hcont : ContinuousOn h (Icc 0 T) := by
      intro x hx
      rcases eq_or_ne x 0 with rfl | hx0
      · have hlim : Tendsto h (𝓝 0) (𝓝 0) := by
          have hb : ∀ y : ℝ, ‖h y‖ ≤ |y| / 2 := by
            intro y
            rcases eq_or_ne y 0 with rfl | hy
            · simp [hhdef]
            rw [Real.norm_eq_abs, hhdef]
            simp only
            rw [abs_div, div_le_iff₀ (abs_pos.2 hy), abs_of_nonneg (by linarith [cos_le_one y])]
            have := one_sub_sq_div_two_le_cos (x := y)
            nlinarith [sq_abs y]
          refine squeeze_zero_norm hb ?_
          simpa using (continuous_abs.tendsto (0 : ℝ)).div_const 2
        have h0 : h 0 = 0 := by simp [hhdef]
        have hc : ContinuousAt h 0 := by rw [ContinuousAt, h0]; exact hlim
        exact hc.continuousWithinAt
      · exact ((continuous_const.sub continuous_cos).continuousAt.div continuousAt_id
          hx0).continuousWithinAt
    have hderiv : ∀ x ∈ Ioo 0 T, HasDerivAt h (sin x / x - g x) x := by
      intro x hx
      have hx0 : x ≠ 0 := hx.1.ne'
      have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_cos x)).div (hasDerivAt_id x) hx0
      convert this using 1
      · funext y; simp [hhdef]
      · simp only [hgdef, id, Pi.sub_apply]
        field_simp
        ring
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont hderiv
      (hsi.sub hgi)
    rw [intervalIntegral.integral_sub hsi hgi] at this
    have h0 : h 0 = 0 := by simp [hhdef]
    rw [h0, sub_zero] at this
    linarith
  have hhlim : Tendsto h atTop (𝓝 0) := by
    have hb : ∀ᶠ y in atTop, ‖h y‖ ≤ 2 / y := by
      filter_upwards [eventually_gt_atTop 0] with y hy
      rw [Real.norm_eq_abs, hhdef]
      simp only
      rw [abs_div, abs_of_pos hy, abs_of_nonneg (by linarith [cos_le_one y])]
      exact div_le_div_of_nonneg_right (by linarith [neg_one_le_cos y]) hy.le
    refine squeeze_zero_norm' hb ?_
    simpa using tendsto_const_nhds.div_atTop tendsto_id
  have hlim1 : Tendsto (fun T => ∫ x in (0 : ℝ)..T, g x) atTop (𝓝 (π / 2)) := by
    have := TauCeti.Contour.tendsto_integral_sin_div_atTop.sub hhlim
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with T hT using (hint T hT).symm
  have hlim2 := intervalIntegral_tendsto_integral_Ioi 0
    integrable_one_sub_cos_div_sq.integrableOn tendsto_id
  rw [tendsto_nhds_unique hlim2 hlim1]
  ring

end Real
