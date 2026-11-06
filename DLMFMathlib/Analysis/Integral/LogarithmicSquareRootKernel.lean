/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.SquareRootKernel
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic comparisons for a pair of square roots

The primitive `2 log(√(t+x)+√(t+y))` regularizes the pair-root kernel against a
simple pole. Placing that pole at `(√x+√y)²/4` gives a difference with zero integral
on the positive half-line. This cancellation is useful for weighted logarithmic asymptotics.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace MeasureTheory.LogarithmicSquareRoot

/-- A logarithmic primitive for a product of two shifted square roots. -/
theorem hasDerivAt_log_sqrt_add_sqrt {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => 2 * Real.log (√(u + x) + √(u + y)))
      (1 / (√(t + x) * √(t + y))) t := by
  have htx : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
  have hty : 0 < t + y := add_pos_of_pos_of_nonneg ht hy
  have hu : 0 < √(t + x) := Real.sqrt_pos.mpr htx
  have hv : 0 < √(t + y) := Real.sqrt_pos.mpr hty
  have H := ((((Real.hasDerivAt_sqrt htx.ne').comp t
    ((hasDerivAt_id t).add_const x)).add ((Real.hasDerivAt_sqrt hty.ne').comp t
      ((hasDerivAt_id t).add_const y))).log (by
        change √(t + x) + √(t + y) ≠ 0
        positivity)).const_mul 2
  apply H.congr_deriv
  simp only [Function.comp_apply, Pi.add_apply, id_eq, mul_one]
  field_simp
  ring

/-- The reciprocal pair-root kernel differs from any intermediate simple pole by at most
its arithmetic shift divided by `t²`. -/
theorem abs_inv_sqrt_product_sub_inv_le {x y σ t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hσ : 0 ≤ σ) (hσa : σ ≤ (x + y) / 2) (ht : 0 < t) :
    |1 / (√(t + x) * √(t + y)) - 1 / (t + σ)| ≤ ((x + y) / 2) / t ^ 2 := by
  let D : ℝ := √(t + x) * √(t + y)
  let a : ℝ := (x + y) / 2
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  change σ ≤ a at hσa
  have htx : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
  have hty : 0 < t + y := add_pos_of_pos_of_nonneg ht hy
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr htx) (Real.sqrt_pos.mpr hty)
  have hT : 0 < t + σ := add_pos_of_pos_of_nonneg ht hσ
  have hDsq : D ^ 2 = (t + x) * (t + y) := by
    dsimp only [D]
    rw [mul_pow, Real.sq_sqrt htx.le, Real.sq_sqrt hty.le]
  have hlow : t ≤ D := by nlinarith
  have hupp : D ≤ t + a := by
    dsimp only [a]
    nlinarith [sq_nonneg (x - y)]
  have hab : |(t + σ) - D| ≤ a := by
    apply abs_le.mpr
    constructor <;> linarith
  have he : 1 / D - 1 / (t + σ) = ((t + σ) - D) / (D * (t + σ)) := by
    field_simp
  change |1 / D - 1 / (t + σ)| ≤ a / t ^ 2
  rw [he, abs_div, abs_of_pos (mul_pos hD hT)]
  exact (div_le_div_of_nonneg_right hab (mul_pos hD hT).le).trans
    (div_le_div_of_nonneg_left ha (sq_pos_of_pos ht) (by nlinarith))


/-- The regularized pair-root kernel is integrable when the first shift is positive. -/
theorem integrableOn_inv_sqrt_product_sub_inv {x y σ : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hσ : 0 < σ) (hσa : σ ≤ (x + y) / 2) :
    IntegrableOn (fun t : ℝ => 1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) (Ioi 0) := by
  let a : ℝ := (x + y) / 2
  let A : ℝ := (√x)⁻¹ + σ⁻¹
  let C : ℝ := 2 * (A + a)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine (integrableOn_inv_sqrt_mul_one_add.const_mul C).mono'
    (show AEStronglyMeasurable (fun t : ℝ =>
      1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) (volume.restrict (Ioi 0)) from
        (by fun_prop : Measurable _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hu : 0 < √t := Real.sqrt_pos.mpr ht0
  have hx0 : 0 < √x := Real.sqrt_pos.mpr hx
  have htx : 0 < √(t + x) := Real.sqrt_pos.mpr (by linarith)
  have hty : 0 < √(t + y) := Real.sqrt_pos.mpr (by linarith)
  have htp : 0 < t + σ := by linarith
  rw [Real.norm_eq_abs]
  change _ ≤ C * (1 / (√t * (1 + t)))
  by_cases ht1 : t ≤ 1
  · have hs1 : √t ≤ 1 := by nlinarith [Real.sq_sqrt ht0.le]
    have hpair : 1 / (√(t + x) * √(t + y)) ≤ 1 / (√x * √t) := by
      apply one_div_le_one_div_of_le (mul_pos hx0 hu)
      exact mul_le_mul (Real.sqrt_le_sqrt (by linarith))
        (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have href : 1 / (t + σ) ≤ 1 / (σ * √t) := by
      apply one_div_le_one_div_of_le (mul_pos hσ hu)
      nlinarith
    have hb : |1 / (√(t + x) * √(t + y)) - 1 / (t + σ)| ≤ A / √t := by
      calc _ ≤ |1 / (√(t + x) * √(t + y))| + |1 / (t + σ)| := abs_sub _ _
        _ ≤ 1 / (√x * √t) + 1 / (σ * √t) := by
          rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
          exact add_le_add hpair href
        _ = A / √t := by dsimp only [A]; ring
    refine hb.trans ?_
    apply (div_le_iff₀ hu).mpr
    dsimp only [C]
    field_simp
    nlinarith [mul_nonneg hA (by linarith : 0 ≤ 1 - t)]
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hst : √t ≤ t := by nlinarith [Real.sq_sqrt ht0.le]
    have hb := abs_inv_sqrt_product_sub_inv_le hx.le hy hσ.le hσa ht0
    refine hb.trans ?_
    change a / t ^ 2 ≤ C * (1 / (√t * (1 + t)))
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    dsimp only [C]
    field_simp
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hst),
      mul_nonneg ha (by nlinarith : 0 ≤ 2 * t ^ 2 - t * (1 + t)),
      mul_nonneg hA (sq_nonneg t)]


/-- The regularized logarithmic primitive tends to `2 log 2` at infinity. -/
theorem tendsto_logarithmic_primitive {x y σ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => 2 * Real.log (√(t + x) + √(t + y)) - Real.log (t + σ))
      atTop (𝓝 (2 * Real.log 2)) := by
  have hden : Tendsto (fun t : ℝ => t + σ) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hrat (v : ℝ) : Tendsto (fun t : ℝ => (t + v) / (t + σ)) atTop (𝓝 1) := by
    have H := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := v - σ)).div_atTop hden)
    simp only [add_zero] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
    ring
  have hxs : Tendsto (fun t : ℝ => √((t + x) / (t + σ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto 1).comp (hrat x)
  have hys : Tendsto (fun t : ℝ => √((t + y) / (t + σ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto 1).comp (hrat y)
  have hsum := hxs.add hys
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num] at hsum
  have H := (((Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto).comp hsum).const_mul 2
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htx : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
  have hty : 0 < t + y := add_pos_of_pos_of_nonneg ht hy
  have htσ : 0 < t + σ := add_pos ht hσ
  have hS : 0 < √(t + x) + √(t + y) := by positivity
  have he : √((t + x) / (t + σ)) + √((t + y) / (t + σ)) =
      (√(t + x) + √(t + y)) / √(t + σ) := by
    rw [Real.sqrt_div htx.le, Real.sqrt_div hty.le, add_div]
  simp only [Function.comp_apply]
  rw [he, Real.log_div hS.ne' (Real.sqrt_pos.mpr htσ).ne', Real.log_sqrt htσ.le]
  ring

/-- The mass of the regularized pair-root kernel is an explicit logarithm. -/
theorem integral_Ioi_inv_sqrt_product_sub_inv {x y σ : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hσ : 0 < σ) (hσa : σ ≤ (x + y) / 2) :
    (∫ t in Ioi (0 : ℝ), 1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) =
      2 * Real.log 2 - (2 * Real.log (√x + √y) - Real.log σ) := by
  have hcont : ContinuousWithinAt (fun t : ℝ =>
      2 * Real.log (√(t + x) + √(t + y)) - Real.log (t + σ)) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · apply ContinuousAt.const_mul
      apply ContinuousAt.log (by fun_prop)
      simp only [zero_add]
      positivity
    · apply ContinuousAt.log (by fun_prop)
      simpa using hσ.ne'
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u : ℝ =>
      2 * Real.log (√(u + x) + √(u + y)) - Real.log (u + σ))
      (1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) t := by
    convert (hasDerivAt_log_sqrt_add_sqrt hx.le hy ht).sub
      (((hasDerivAt_id t).add_const σ).log (by linarith : t + σ ≠ 0)) using 1 <;>
        simp only [Pi.sub_def, id_eq, one_div]
  have H := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd
    (integrableOn_inv_sqrt_product_sub_inv hx hy hσ hσa)
    (tendsto_logarithmic_primitive hx.le hy hσ)
  simpa only [zero_add] using H


/-- The pole located at the squared arithmetic mean of the square roots has zero kernel mass. -/
theorem integral_Ioi_inv_sqrt_product_sub_inv_eq_zero_of_pos {x y : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) :
    (∫ t in Ioi (0 : ℝ), 1 / (√(t + x) * √(t + y)) -
      1 / (t + (√x + √y) ^ 2 / 4)) = 0 := by
  have hξ : 0 < √x + √y := by positivity
  have hσ : 0 < (√x + √y) ^ 2 / 4 := by positivity
  have hσa : (√x + √y) ^ 2 / 4 ≤ (x + y) / 2 := by
    nlinarith [sq_nonneg (√x - √y), Real.sq_sqrt hx.le, Real.sq_sqrt hy]
  rw [integral_Ioi_inv_sqrt_product_sub_inv hx hy hσ hσa,
    Real.log_div (pow_ne_zero 2 hξ.ne') (by norm_num), Real.log_pow]
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog]
  norm_num

/-- The logarithmic pair-root comparison has zero mass for all nonnegative shifts. -/
theorem integral_Ioi_inv_sqrt_product_sub_inv_eq_zero {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∫ t in Ioi (0 : ℝ), 1 / (√(t + x) * √(t + y)) -
      1 / (t + (√x + √y) ^ 2 / 4)) = 0 := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    rcases hy.eq_or_lt with hy | hy
    · subst y
      calc
        _ = ∫ t in Ioi (0 : ℝ), (0 : ℝ) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          simp only [add_zero, Real.sqrt_zero, zero_pow (by norm_num : 2 ≠ 0),
            zero_div, Real.mul_self_sqrt ht.le, sub_self]
        _ = 0 := integral_zero _ _
    · simpa only [mul_comm, add_comm] using
        integral_Ioi_inv_sqrt_product_sub_inv_eq_zero_of_pos hy (by norm_num : (0 : ℝ) ≤ 0)
  · exact integral_Ioi_inv_sqrt_product_sub_inv_eq_zero_of_pos hx hy


/-- A primitive of the product of two shifted reciprocal linear factors. -/
theorem hasDerivAt_log_difference_div {a z t : ℝ} (ha : 0 < a) (haz : a < z)
    (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (Real.log (u + a) - Real.log (u + z)) / (z - a))
      (1 / ((t + a) * (t + z))) t := by
  have hta : 0 < t + a := by linarith
  have htz : 0 < t + z := by linarith
  have H := ((((hasDerivAt_id t).add_const a).log hta.ne').sub
    (((hasDerivAt_id t).add_const z).log htz.ne')).div_const (z - a)
  apply H.congr_deriv
  simp only [id_eq]
  field_simp [hta.ne', htz.ne', sub_ne_zero.mpr haz.ne']
  ring

/-- The logarithmic difference primitive vanishes at infinity. -/
theorem tendsto_log_difference_div {a z : ℝ} (ha : 0 < a) (haz : a < z) :
    Tendsto (fun t : ℝ => (Real.log (t + a) - Real.log (t + z)) / (z - a))
      atTop (𝓝 0) := by
  have H := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := a - z)).div_atTop
      (tendsto_atTop_add_const_right _ z tendsto_id))
  simp only [add_zero] at H
  have Hr : Tendsto (fun t : ℝ => (t + a) / (t + z)) atTop (𝓝 1) := by
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [id_eq]
    field_simp [show t + z ≠ 0 by linarith]
    ring
  have HL := (((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp Hr).div_const
    (z - a)
  simp only [Real.log_one, zero_div] at HL
  apply HL.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply]
  rw [Real.log_div (by linarith : t + a ≠ 0) (by linarith : t + z ≠ 0)]

/-- Products of two positively shifted reciprocal linear factors are integrable. -/
theorem integrableOn_inv_mul_add {a z : ℝ} (ha : 0 < a) (haz : a < z) :
    IntegrableOn (fun t : ℝ => 1 / ((t + a) * (t + z))) (Ioi 0) := by
  have hz : 0 < z := ha.trans haz
  apply integrableOn_Ioi_deriv_of_nonneg
    (show ContinuousWithinAt (fun t : ℝ =>
      (Real.log (t + a) - Real.log (t + z)) / (z - a)) (Ici 0) 0 from
        (by fun_prop (disch := positivity)))
    (fun t ht => hasDerivAt_log_difference_div ha haz ht)
    (fun t ht => by have ht0 : 0 < t := ht; have hz : 0 < z := ha.trans haz; positivity)
  exact tendsto_log_difference_div ha haz

/-- The integral of a product of two shifted reciprocal factors is a logarithmic quotient. -/
theorem integral_Ioi_inv_mul_add {a z : ℝ} (ha : 0 < a) (haz : a < z) :
    ∫ t in Ioi (0 : ℝ), 1 / ((t + a) * (t + z)) = Real.log (z / a) / (z - a) := by
  have hz : 0 < z := ha.trans haz
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    (show ContinuousWithinAt (fun t : ℝ =>
      (Real.log (t + a) - Real.log (t + z)) / (z - a)) (Ici 0) 0 from
        (by fun_prop (disch := positivity)))
    (fun t ht => hasDerivAt_log_difference_div ha haz ht)
    (integrableOn_inv_mul_add ha haz) (tendsto_log_difference_div ha haz)
  rw [Real.log_div (ha.trans haz).ne' ha.ne']
  simpa only [zero_add, zero_sub, ← neg_div, neg_sub] using H

/-- A reciprocal square-root shift is bounded by a rational tail kernel. -/
theorem inv_sqrt_sub_inv_sqrt_add_le_tail {z t : ℝ} (hz : 0 < z) (ht : 0 ≤ t) :
    0 ≤ (√z)⁻¹ - (√(t + z))⁻¹ ∧
      (√z)⁻¹ - (√(t + z))⁻¹ ≤ t / (√z * (t + z)) := by
  have htz : 0 < t + z := add_pos_of_nonneg_of_pos ht hz
  have hu := Real.sqrt_pos.mpr hz
  have hv := Real.sqrt_pos.mpr htz
  have he : (√z)⁻¹ - (√(t + z))⁻¹ =
      t / (√z * √(t + z) * (√z + √(t + z))) := by
    field_simp
    nlinarith [Real.sq_sqrt hz.le, Real.sq_sqrt htz.le]
  rw [he]
  refine ⟨by positivity, ?_⟩
  apply div_le_div_of_nonneg_left ht (mul_pos hu htz)
  have H := mul_nonneg (sq_nonneg (√z)) (Real.sqrt_nonneg (t + z))
  have heq : √z * (t + z) = √z * √(t + z) ^ 2 := by rw [Real.sq_sqrt htz.le]
  nlinarith only [H, heq]


/-- A rational majorant for the weighted logarithmic pair-root error. -/
theorem abs_pair_kernel_mul_sqrt_shift_le {x y σ z t : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hσ : 0 ≤ σ) (hσa : σ ≤ (x + y) / 2)
    (hz : 0 < z) (ht : 0 < t) :
    |(1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) *
      ((√z)⁻¹ - (√(t + z))⁻¹)| ≤
      (4 * ((x + y) / 2) / √z) * (1 / ((t + (x + y) / 2) * (t + z))) := by
  let a : ℝ := (x + y) / 2
  let d : ℝ := 1 / (√(t + x) * √(t + y)) - 1 / (t + σ)
  let B : ℝ := √z * (t + z)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hu : 0 < √t := Real.sqrt_pos.mpr ht
  have hzroot : 0 < √z := Real.sqrt_pos.mpr hz
  have htx : 0 < √(t + x) := Real.sqrt_pos.mpr (by linarith)
  have hty : 0 < √(t + y) := Real.sqrt_pos.mpr (by linarith)
  have hta : 0 < t + a := add_pos_of_pos_of_nonneg ht ha
  have htz : 0 < t + z := add_pos ht hz
  have htσ : 0 < t + σ := add_pos_of_pos_of_nonneg ht hσ
  have hB : 0 < B := mul_pos hzroot htz
  have hlow : t ≤ √(t + x) * √(t + y) := by
    calc t = √t * √t := (Real.mul_self_sqrt ht.le).symm
      _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt (by linarith))
        (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcrude : |d| ≤ 2 / t := by
    calc |d| ≤ |1 / (√(t + x) * √(t + y))| + |1 / (t + σ)| := abs_sub _ _
      _ ≤ 1 / t + 1 / t := by
        rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
        exact add_le_add (one_div_le_one_div_of_le ht hlow)
          (one_div_le_one_div_of_le ht (by linarith))
      _ = _ := by ring
  have hraw : |d| ≤ a / t ^ 2 := abs_inv_sqrt_product_sub_inv_le hx hy hσ hσa ht
  have hshift := inv_sqrt_sub_inv_sqrt_add_le_tail hz ht.le
  have hR : (4 * a / √z) * (1 / ((t + a) * (t + z))) = 4 * a / (B * (t + a)) := by
    dsimp only [B]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  change |d * ((√z)⁻¹ - (√(t + z))⁻¹)| ≤ _
  rw [abs_mul, abs_of_nonneg hshift.1, hR]
  by_cases hsmall : t ≤ a
  · calc
      _ ≤ (2 / t) * (t / B) := mul_le_mul hcrude hshift.2 hshift.1 (by positivity)
      _ = 2 / B := by field_simp
      _ ≤ 4 * a / (B * (t + a)) := by
        apply (div_le_div_iff₀ hB (mul_pos hB hta)).mpr
        have H := mul_le_mul_of_nonneg_left (show 2 * (t + a) ≤ 4 * a by linarith) hB.le
        nlinarith only [H]
  · calc
      _ ≤ (a / t ^ 2) * (t / B) := mul_le_mul hraw hshift.2 hshift.1 (by positivity)
      _ = a / (t * B) := by field_simp
      _ ≤ 4 * a / (B * (t + a)) := by
        apply (div_le_div_iff₀ (mul_pos ht hB) (mul_pos hB hta)).mpr
        have H := mul_le_mul_of_nonneg_left (show t + a ≤ 4 * t by linarith)
          (mul_nonneg ha hB.le)
        nlinarith only [H]

/-- The weighted logarithmic pair-root error is integrable. -/
theorem integrableOn_pair_kernel_mul_sqrt_shift {x y σ z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hσ : 0 ≤ σ) (hσa : σ ≤ (x + y) / 2)
    (ha : 0 < (x + y) / 2) (haz : (x + y) / 2 < z) :
    IntegrableOn (fun t : ℝ =>
      (1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) *
        ((√z)⁻¹ - (√(t + z))⁻¹)) (Ioi 0) := by
  refine ((integrableOn_inv_mul_add ha haz).const_mul (4 * ((x + y) / 2) / √z)).mono'
    (show AEStronglyMeasurable (fun t : ℝ =>
      (1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) *
        ((√z)⁻¹ - (√(t + z))⁻¹)) (volume.restrict (Ioi 0)) from
          (by fun_prop : Measurable _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact abs_pair_kernel_mul_sqrt_shift_le hx hy hσ hσa (ha.trans haz) ht

/-- The weighted comparison error is bounded by a logarithmic rational-tail integral. -/
theorem abs_integral_pair_kernel_mul_sqrt_shift_le {x y σ z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hσ : 0 ≤ σ) (hσa : σ ≤ (x + y) / 2)
    (ha : 0 < (x + y) / 2) (haz : (x + y) / 2 < z) :
    |∫ t in Ioi (0 : ℝ), (1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) *
      ((√z)⁻¹ - (√(t + z))⁻¹)| ≤
      (4 * ((x + y) / 2) / √z) * (Real.log (z / ((x + y) / 2)) / (z - (x + y) / 2)) := by
  let a : ℝ := (x + y) / 2
  let F : ℝ → ℝ := fun t => (1 / (√(t + x) * √(t + y)) - 1 / (t + σ)) *
    ((√z)⁻¹ - (√(t + z))⁻¹)
  have hz : 0 < z := ha.trans haz
  have hi := (integrableOn_inv_mul_add ha haz).const_mul (4 * a / √z)
  have hf : IntegrableOn F (Ioi 0) :=
    integrableOn_pair_kernel_mul_sqrt_shift hx hy hσ hσa ha haz
  change |∫ t in Ioi (0 : ℝ), F t| ≤ _
  calc
    _ = ‖∫ t in Ioi (0 : ℝ), F t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), (4 * a / √z) * (1 / ((t + a) * (t + z))) := by
      exact integral_mono_ae hf.norm hi
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          change ‖F t‖ ≤ _
          rw [Real.norm_eq_abs]
          exact abs_pair_kernel_mul_sqrt_shift_le hx hy hσ hσa hz ht)
    _ = _ := by rw [integral_const_mul, integral_Ioi_inv_mul_add ha haz]

end MeasureTheory.LogarithmicSquareRoot
