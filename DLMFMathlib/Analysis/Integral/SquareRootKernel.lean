/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Square-root kernels on a half-line

The difference `t⁻¹ᐟ² - (t+x)⁻¹ᐟ²` is integrable on the positive half-line and has integral
`2√x`. This identity controls the dependence of regularized Stieltjes kernels on small
nonnegative shifts. A numerator vanishing linearly at zero gives a linear weighted error.
The elementary arctangent integral `∫₀∞ dt/(√t(t+p)) = π/√p` supplies a comparison kernel
for the simultaneous limit of three square-root factors.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Real Topology

namespace MeasureTheory

namespace SquareRootShift

/-- A primitive for the difference between two reciprocal square roots. -/
theorem hasDerivAt_primitive {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => 2 * (√u - √(u + x)))
      ((√t)⁻¹ - (√(t + x))⁻¹) t := by
  have htx : 0 < t + x := by linarith
  have H := ((Real.hasDerivAt_sqrt ht.ne').sub
    ((Real.hasDerivAt_sqrt htx.ne').comp t ((hasDerivAt_id t).add_const x))).const_mul 2
  convert H using 1 <;> simp only [Pi.sub_apply, Function.comp_def, id_eq, mul_one]; ring

/-- The square-root difference vanishes at infinity. -/
theorem tendsto_primitive {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun t : ℝ => 2 * (√t - √(t + x))) atTop (𝓝 0) := by
  have hden : Tendsto (fun t : ℝ => √t + √(t + x)) atTop atTop :=
    tendsto_atTop_mono (fun t => le_add_of_nonneg_right (Real.sqrt_nonneg (t + x)))
      Real.tendsto_sqrt_atTop
  have H := (tendsto_const_nhds (x := -2 * x)).div_atTop hden
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htx : 0 < t + x := by linarith
  have hsq := Real.sq_sqrt ht.le
  have hsqx := Real.sq_sqrt htx.le
  have hs : √t + √(t + x) ≠ 0 := by positivity
  apply (div_eq_iff hs).mpr
  nlinarith

/-- A rational square-root kernel is controlled by twice the reciprocal square-root difference. -/
theorem div_sqrt_mul_add_le_two_sub {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) :
    p / (√t * (t + p)) ≤ 2 * ((√t)⁻¹ - (√(t + p))⁻¹) := by
  have htp : 0 < t + p := by linarith
  have hu : 0 < √t := Real.sqrt_pos.mpr ht
  have hv : 0 < √(t + p) := Real.sqrt_pos.mpr htp
  have hU := Real.sq_sqrt ht.le
  have hV := Real.sq_sqrt htp.le
  apply (div_le_iff₀ (mul_pos hu htp)).mpr
  nth_rw 2 [← hV]
  have he : 2 * ((√t)⁻¹ - (√(t + p))⁻¹) * (√t * √(t + p) ^ 2) =
      2 * √(t + p) ^ 2 - 2 * √t * √(t + p) := by
    field_simp
  rw [he]
  nlinarith [sq_nonneg (√(t + p) - √t)]

/-- The reciprocal square root has a uniform linear decrement on a positive half-line. -/
theorem inv_sqrt_sub_inv_sqrt_add_le {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    (√y)⁻¹ - (√(y + t))⁻¹ ≤ t / (y * √y) := by
  have hyt : 0 < y + t := by linarith
  have hu := Real.sqrt_pos.mpr hy
  have hv := Real.sqrt_pos.mpr hyt
  have huv : √y ≤ √(y + t) := Real.sqrt_le_sqrt (by linarith)
  have hEq : (√y)⁻¹ - (√(y + t))⁻¹ = t / (√y * √(y + t) * (√(y + t) + √y)) := by
    field_simp
    nlinarith [Real.sq_sqrt hy.le, Real.sq_sqrt hyt.le]
  rw [hEq]
  apply div_le_div_of_nonneg_left ht (mul_pos hy hu)
  calc y * √y = √y * √y * √y := by rw [Real.mul_self_sqrt hy.le]
    _ ≤ √y * √(y + t) * (√(y + t) + √y) := by gcongr; linarith

/-- Three nonnegative square-root shifts are bounded by the sum of their separate shifts. -/
theorem inv_sqrt_sub_div_sqrt_product_le {t x y z : ℝ} (ht : 0 < t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (√t)⁻¹ - t / (√(t + x) * √(t + y) * √(t + z)) ∧
      (√t)⁻¹ - t / (√(t + x) * √(t + y) * √(t + z)) ≤
        ((√t)⁻¹ - (√(t + x))⁻¹) + ((√t)⁻¹ - (√(t + y))⁻¹) +
          ((√t)⁻¹ - (√(t + z))⁻¹) := by
  let a : ℝ := √t / √(t + x)
  let b : ℝ := √t / √(t + y)
  let c : ℝ := √t / √(t + z)
  have hu : 0 < √t := Real.sqrt_pos.mpr ht
  have hA : 0 < √(t + x) := Real.sqrt_pos.mpr (by linarith)
  have hB : 0 < √(t + y) := Real.sqrt_pos.mpr (by linarith)
  have hD : 0 < √(t + z) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 ≤ a ∧ a ≤ 1 := ⟨by dsimp [a]; positivity,
    (div_le_one hA).mpr (Real.sqrt_le_sqrt (by linarith))⟩
  have hb : 0 ≤ b ∧ b ≤ 1 := ⟨by dsimp [b]; positivity,
    (div_le_one hB).mpr (Real.sqrt_le_sqrt (by linarith))⟩
  have hc : 0 ≤ c ∧ c ≤ 1 := ⟨by dsimp [c]; positivity,
    (div_le_one hD).mpr (Real.sqrt_le_sqrt (by linarith))⟩
  have hab : a * b ≤ 1 := (mul_le_mul_of_nonneg_right ha.2 hb.1).trans (by simpa using hb.2)
  have habc : a * b * c ≤ 1 :=
    (mul_le_mul_of_nonneg_right hab hc.1).trans (by simpa using hc.2)
  have hprod : (√t)⁻¹ * a * b * c = t / (√(t + x) * √(t + y) * √(t + z)) := by
    dsimp only [a, b, c]
    field_simp
    nlinarith [Real.sq_sqrt ht.le]
  have hpa : (√t)⁻¹ * a = (√(t + x))⁻¹ := by dsimp only [a]; field_simp
  have hpb : (√t)⁻¹ * b = (√(t + y))⁻¹ := by dsimp only [b]; field_simp
  have hpc : (√t)⁻¹ * c = (√(t + z))⁻¹ := by dsimp only [c]; field_simp
  have hpos := mul_nonneg (inv_nonneg.mpr hu.le) (sub_nonneg.mpr habc)
  have hsum : 1 - a * b * c ≤ (1 - a) + (1 - b) + (1 - c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2),
      mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hab)]
  have hsum' := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hu.le)
  constructor
  · rw [← hprod]
    nlinarith only [hpos]
  · rw [← hprod, ← hpa, ← hpb, ← hpc]
    nlinarith only [hsum']

/-- A linear bound at zero controls the change of a regularized square-root kernel. -/
theorem regularized_kernel_sub_le {h : ℝ → ℝ} {C x p t : ℝ}
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hp : 0 ≤ p) (ht : 0 < t)
    (hh : 0 ≤ h t) (hb : h t ≤ C * t) :
    0 ≤ h t / (√t * t) - h t / (√(t + x) * (t + p)) ∧
      h t / (√t * t) - h t / (√(t + x) * (t + p)) ≤
        C * (((√t)⁻¹ - (√(t + x))⁻¹) + 2 * ((√t)⁻¹ - (√(t + p))⁻¹)) := by
  have htx : 0 < t + x := by linarith
  have htp : 0 < t + p := by linarith
  have hu := Real.sqrt_pos.mpr ht
  have hv := Real.sqrt_pos.mpr htx
  have huv : √t ≤ √(t + x) := Real.sqrt_le_sqrt (by linarith)
  have hden : √t * t ≤ √(t + x) * (t + p) :=
    mul_le_mul huv (by linarith) ht.le (Real.sqrt_nonneg _)
  have hnon : 0 ≤ (√t * t)⁻¹ - (√(t + x) * (t + p))⁻¹ :=
    sub_nonneg.mpr (inv_anti₀ (mul_pos hu ht) hden)
  constructor
  · simpa only [div_eq_mul_inv, mul_sub] using mul_nonneg hh hnon
  calc h t / (√t * t) - h t / (√(t + x) * (t + p)) =
      h t * ((√t * t)⁻¹ - (√(t + x) * (t + p))⁻¹) := by ring
    _ ≤ (C * t) * ((√t * t)⁻¹ - (√(t + x) * (t + p))⁻¹) :=
      mul_le_mul_of_nonneg_right hb hnon
    _ = C * (((√t)⁻¹ - (√(t + x))⁻¹) + p / (√(t + x) * (t + p))) := by
      field_simp
      ring
    _ ≤ C * (((√t)⁻¹ - (√(t + x))⁻¹) + p / (√t * (t + p))) := by
      gcongr
    _ ≤ C * (((√t)⁻¹ - (√(t + x))⁻¹) + 2 * ((√t)⁻¹ - (√(t + p))⁻¹)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (div_sqrt_mul_add_le_two_sub ht hp)) hC

end SquareRootShift

/-- A reciprocal square-root difference is integrable over the positive half-line. -/
theorem integrableOn_inv_sqrt_sub_inv_sqrt_add {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => (√t)⁻¹ - (√(t + x))⁻¹) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    (show ContinuousWithinAt (fun t : ℝ => 2 * (√t - √(t + x))) (Ici 0) 0 by fun_prop)
    (fun t ht => SquareRootShift.hasDerivAt_primitive hx ht)
  · intro t ht
    exact sub_nonneg.mpr (inv_anti₀ (Real.sqrt_pos.mpr ht)
      (Real.sqrt_le_sqrt (by linarith)))
  · exact SquareRootShift.tendsto_primitive hx

/-- The reciprocal square-root difference has integral `2√x`. -/
theorem integral_Ioi_inv_sqrt_sub_inv_sqrt_add {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Ioi (0 : ℝ), ((√t)⁻¹ - (√(t + x))⁻¹) = 2 * √x := by
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    (show ContinuousWithinAt (fun t : ℝ => 2 * (√t - √(t + x))) (Ici 0) 0 by fun_prop)
    (fun t ht => SquareRootShift.hasDerivAt_primitive hx ht)
    (integrableOn_inv_sqrt_sub_inv_sqrt_add hx) (SquareRootShift.tendsto_primitive hx)
  simpa using H

namespace SquareRootShift

/-- An arctangent primitive of the shifted reciprocal square-root kernel. -/
theorem hasDerivAt_arctan_primitive {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (2 / √p) * Real.arctan (√u / √p))
      (1 / (√t * (t + p))) t := by
  have H := ((Real.hasDerivAt_arctan (√t / √p)).comp t
    ((Real.hasDerivAt_sqrt ht.ne').div_const (√p))).const_mul (2 / √p)
  apply H.congr_deriv
  field_simp
  nlinarith [Real.sq_sqrt ht.le, Real.sq_sqrt hp.le]

/-- The arctangent primitive has the finite limit `π/√p` at infinity. -/
theorem tendsto_arctan_primitive {p : ℝ} (hp : 0 < p) :
    Tendsto (fun u : ℝ => (2 / √p) * Real.arctan (√u / √p)) atTop (𝓝 (π / √p)) := by
  have H := ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
    (Real.tendsto_sqrt_atTop.atTop_div_const (Real.sqrt_pos.mpr hp))).const_mul (2 / √p)
  change Tendsto (fun u : ℝ => (2 / √p) * Real.arctan (√u / √p))
    atTop (𝓝 ((2 / √p) * (π / 2))) at H
  convert H using 1; ring

end SquareRootShift

/-- The kernel `1/(√t(t+p))` is integrable for every positive `p`. -/
theorem integrableOn_inv_sqrt_mul_add {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => 1 / (√t * (t + p))) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    (show ContinuousWithinAt (fun t : ℝ => (2 / √p) * Real.arctan (√t / √p))
      (Ici 0) 0 by fun_prop)
    (fun t ht => SquareRootShift.hasDerivAt_arctan_primitive hp ht)
    (fun t ht => by have ht0 : 0 < t := ht; positivity)
  exact SquareRootShift.tendsto_arctan_primitive hp

/-- The reciprocal square-root kernel has integral `π/√p`. -/
theorem integral_Ioi_inv_sqrt_mul_add {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), 1 / (√t * (t + p)) = π / √p := by
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    (show ContinuousWithinAt (fun t : ℝ => (2 / √p) * Real.arctan (√t / √p))
      (Ici 0) 0 by fun_prop)
    (fun t ht => SquareRootShift.hasDerivAt_arctan_primitive hp ht)
    (integrableOn_inv_sqrt_mul_add hp) (SquareRootShift.tendsto_arctan_primitive hp)
  simpa using H

/-- The profile `1/(√t(1+t))` is integrable on the positive half-line. -/
theorem integrableOn_inv_sqrt_mul_one_add :
    IntegrableOn (fun t : ℝ => 1 / (√t * (1 + t))) (Ioi 0) := by
  simpa only [add_comm] using integrableOn_inv_sqrt_mul_add (p := 1) (by norm_num)

/-- A bounded numerator that vanishes linearly gives an integrable limiting square-root kernel. -/
theorem integrableOn_div_sqrt_mul_self {h : ℝ → ℝ} {C M : ℝ} (hh : Measurable h)
    (hpos : ∀ t > 0, 0 ≤ h t) (hlinear : ∀ t > 0, h t ≤ C * t)
    (hbounded : ∀ t > 0, h t ≤ M) :
    IntegrableOn (fun t : ℝ => h t / (√t * t)) (Ioi 0) := by
  refine (integrableOn_inv_sqrt_mul_one_add.const_mul (C + M)).mono'
    (show AEStronglyMeasurable (fun t : ℝ => h t / (√t * t)) (volume.restrict (Ioi 0)) from
      (by fun_prop : Measurable (fun t : ℝ => h t / (√t * t))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hs : 0 < √t := Real.sqrt_pos.mpr ht0
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hpos t ht0) (by positivity))]
  have H : h t / t ≤ (C + M) / (1 + t) := by
    apply (div_le_div_iff₀ ht0 (by linarith : 0 < 1 + t)).mpr
    nlinarith [hlinear t ht0, mul_le_mul_of_nonneg_right (hbounded t ht0) ht0.le]
  convert div_le_div_of_nonneg_right H hs.le using 1 <;> field_simp

/-- A regular numerator turns a square-root shift into a linear integral error. -/
theorem integral_mul_inv_sqrt_sub_inv_sqrt_add_le {h : ℝ → ℝ} {x : ℝ}
    (hh : Measurable h) (hx : 0 ≤ x) (hpos : ∀ t > 0, 0 ≤ h t)
    (hi : IntegrableOn (fun t : ℝ => h t / (√t * t)) (Ioi 0)) :
    0 ≤ (∫ t in Ioi (0 : ℝ), h t * ((√t)⁻¹ - (√(t + x))⁻¹)) ∧
      (∫ t in Ioi (0 : ℝ), h t * ((√t)⁻¹ - (√(t + x))⁻¹)) ≤
        x * ∫ t in Ioi (0 : ℝ), h t / (√t * t) := by
  have hb (t : ℝ) (ht : 0 < t) :
      0 ≤ h t * ((√t)⁻¹ - (√(t + x))⁻¹) ∧
      h t * ((√t)⁻¹ - (√(t + x))⁻¹) ≤ x * (h t / (√t * t)) := by
    have hd : 0 ≤ (√t)⁻¹ - (√(t + x))⁻¹ := by
      apply sub_nonneg.mpr
      exact inv_anti₀ (Real.sqrt_pos.mpr ht) (Real.sqrt_le_sqrt (by linarith))
    refine ⟨mul_nonneg (hpos t ht) hd, ?_⟩
    calc _ ≤ h t * (x / (t * √t)) := mul_le_mul_of_nonneg_left
          (SquareRootShift.inv_sqrt_sub_inv_sqrt_add_le ht hx) (hpos t ht)
      _ = x * (h t / (√t * t)) := by ring
  have hf : IntegrableOn (fun t : ℝ => h t * ((√t)⁻¹ - (√(t + x))⁻¹)) (Ioi 0) := by
    refine (hi.const_mul x).mono'
      (show AEStronglyMeasurable (fun t : ℝ => h t * ((√t)⁻¹ - (√(t + x))⁻¹))
        (volume.restrict (Ioi 0)) from (by fun_prop : Measurable _).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hb t ht).1]
    exact (hb t ht).2
  refine ⟨integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi
    fun t ht => (hb t ht).1), ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae hf (hi.const_mul x)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hb t ht).2)

/-- A nonnegative integrable limiting kernel dominates all its nonnegative shifts. -/
theorem integrableOn_div_sqrt_mul_add {h : ℝ → ℝ} {x p : ℝ}
    (hh : Measurable h) (hx : 0 ≤ x) (hp : 0 ≤ p) (hpos : ∀ t > 0, 0 ≤ h t)
    (hi : IntegrableOn (fun t : ℝ => h t / (√t * t)) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => h t / (√(t + x) * (t + p))) (Ioi 0) := by
  refine hi.mono' (show AEStronglyMeasurable
    (fun t : ℝ => h t / (√(t + x) * (t + p))) (volume.restrict (Ioi 0)) from
    (by fun_prop : Measurable (fun t : ℝ => h t / (√(t + x) * (t + p)))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hpos t ht0) (by positivity))]
  apply div_le_div_of_nonneg_left (hpos t ht0) (mul_pos (Real.sqrt_pos.mpr ht0) ht0)
  exact mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (by linarith) ht0.le
    (Real.sqrt_nonneg _)

/-- Regularized Stieltjes kernels vary at most by a constant times `√x + √p`. -/
theorem abs_integral_div_sqrt_mul_add_sub_le {h : ℝ → ℝ} {C x p : ℝ}
    (hh : Measurable h) (hC : 0 ≤ C) (hx : 0 ≤ x) (hp : 0 ≤ p)
    (hpos : ∀ t > 0, 0 ≤ h t) (hbound : ∀ t > 0, h t ≤ C * t)
    (hi : IntegrableOn (fun t : ℝ => h t / (√t * t)) (Ioi 0)) :
    |(∫ t in Ioi (0 : ℝ), h t / (√(t + x) * (t + p))) -
      ∫ t in Ioi (0 : ℝ), h t / (√t * t)| ≤ C * (2 * √x + 4 * √p) := by
  have hf := integrableOn_div_sqrt_mul_add hh hx hp hpos hi
  have hxI := integrableOn_inv_sqrt_sub_inv_sqrt_add hx
  have hpI := integrableOn_inv_sqrt_sub_inv_sqrt_add hp
  have hR := (hxI.add (hpI.const_mul 2)).const_mul C
  have hle : (∫ t in Ioi (0 : ℝ), h t / (√(t + x) * (t + p))) ≤
      ∫ t in Ioi (0 : ℝ), h t / (√t * t) := by
    refine integral_mono_ae hf hi ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact sub_nonneg.mp (SquareRootShift.regularized_kernel_sub_le hC hx hp ht
      (hpos t ht) (hbound t ht)).1
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle), ← integral_sub hi hf]
  calc (∫ t in Ioi (0 : ℝ), h t / (√t * t) - h t / (√(t + x) * (t + p))) ≤
      ∫ t in Ioi (0 : ℝ), C * (((√t)⁻¹ - (√(t + x))⁻¹) +
        2 * ((√t)⁻¹ - (√(t + p))⁻¹)) := by
        refine integral_mono_ae (hi.sub hf) hR ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (SquareRootShift.regularized_kernel_sub_le hC hx hp ht
          (hpos t ht) (hbound t ht)).2
    _ = C * (2 * √x + 4 * √p) := by
      rw [integral_const_mul, integral_add hxI (hpI.const_mul 2), integral_const_mul,
        integral_Ioi_inv_sqrt_sub_inv_sqrt_add hx, integral_Ioi_inv_sqrt_sub_inv_sqrt_add hp]
      ring

/-- The simultaneous zero-node error has a uniform square-root bound. -/
theorem abs_integral_div_sqrt_product_sub_le {x y z p : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hp : 0 < p) :
    |(∫ t in Ioi (0 : ℝ), t / (√(t + x) * √(t + y) * √(t + z) * (t + p))) -
      π / √p| ≤ (2 / p) * (√x + √y + √z) := by
  let T : ℝ → ℝ := fun t => t / (√(t + x) * √(t + y) * √(t + z) * (t + p))
  let Q : ℝ → ℝ := fun t => 1 / (√t * (t + p))
  let R : ℝ → ℝ := fun t => (((√t)⁻¹ - (√(t + x))⁻¹) +
    ((√t)⁻¹ - (√(t + y))⁻¹) + ((√t)⁻¹ - (√(t + z))⁻¹)) / p
  have hQ : IntegrableOn Q (Ioi 0) := integrableOn_inv_sqrt_mul_add hp
  have hR : IntegrableOn R (Ioi 0) :=
    (((integrableOn_inv_sqrt_sub_inv_sqrt_add hx).add
      (integrableOn_inv_sqrt_sub_inv_sqrt_add hy)).add
        (integrableOn_inv_sqrt_sub_inv_sqrt_add hz)).div_const p
  have hpoint (t : ℝ) (ht : 0 < t) : 0 ≤ Q t - T t ∧ Q t - T t ≤ R t := by
    have H := SquareRootShift.inv_sqrt_sub_div_sqrt_product_le ht hx hy hz
    have htp : 0 < t + p := add_pos ht hp
    have he : Q t - T t = ((√t)⁻¹ - t / (√(t + x) * √(t + y) * √(t + z))) /
        (t + p) := by simp only [Q, T, div_eq_mul_inv, mul_inv]; ring
    rw [he]
    refine ⟨div_nonneg H.1 htp.le, ?_⟩
    calc _ ≤ (((√t)⁻¹ - (√(t + x))⁻¹) + ((√t)⁻¹ - (√(t + y))⁻¹) +
        ((√t)⁻¹ - (√(t + z))⁻¹)) / (t + p) := div_le_div_of_nonneg_right H.2 htp.le
      _ ≤ R t := div_le_div_of_nonneg_left (H.1.trans H.2) hp (by linarith)
  have hT : IntegrableOn T (Ioi 0) := by
    refine hQ.mono' (show AEStronglyMeasurable T (volume.restrict (Ioi 0)) from
      (by dsimp only [T]; fun_prop : Measurable T).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ T t by dsimp only [T]; positivity)]
    exact sub_nonneg.mp (hpoint t ht).1
  have hle : (∫ t in Ioi (0 : ℝ), T t) ≤ ∫ t in Ioi (0 : ℝ), Q t :=
    integral_mono_ae hT hQ
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => sub_nonneg.mp (hpoint t ht).1)
  rw [← integral_Ioi_inv_sqrt_mul_add hp, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hle), ← integral_sub hQ hT]
  calc
    (∫ t in Ioi (0 : ℝ), Q t - T t) ≤ (∫ t in Ioi (0 : ℝ), R t) := by
      exact integral_mono_ae (hQ.sub hT) hR
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpoint t ht).2)
    _ = (2 / p) * (√x + √y + √z) := by
      dsimp only [R]
      have hxy : IntegrableOn (fun t : ℝ => ((√t)⁻¹ - (√(t + x))⁻¹) +
          ((√t)⁻¹ - (√(t + y))⁻¹)) (Ioi 0) :=
        (integrableOn_inv_sqrt_sub_inv_sqrt_add hx).add
          (integrableOn_inv_sqrt_sub_inv_sqrt_add hy)
      rw [integral_div, integral_add hxy
        (integrableOn_inv_sqrt_sub_inv_sqrt_add hz),
        integral_add (integrableOn_inv_sqrt_sub_inv_sqrt_add hx)
          (integrableOn_inv_sqrt_sub_inv_sqrt_add hy),
        integral_Ioi_inv_sqrt_sub_inv_sqrt_add hx,
        integral_Ioi_inv_sqrt_sub_inv_sqrt_add hy,
        integral_Ioi_inv_sqrt_sub_inv_sqrt_add hz]
      ring

end MeasureTheory
