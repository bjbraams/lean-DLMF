/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import DLMFMathlib.Analysis.Integral.SquareRootKernel
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Reciprocal cubic and quartic square-root kernels

Positive shifts give integrable reciprocal square-root products on the positive half-line.
A positive linear scaling reduces two linear factors to their standard shifted form.
The substitution `t = xyz/u` identifies a reciprocal quartic square-root integral
with a cubic one, and therefore proves its integrability as well.

The change of variables and linear scaling use Mathlib's
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` and
`MeasureTheory.integral_comp_mul_left_Ioi`.
-/

public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Real

/-- The reciprocal of three positive shifted square roots is integrable on `(0, ∞)`. -/
lemma integrableOn_inv_sqrt_add_mul_sqrt_add_mul_sqrt_add
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => (Real.sqrt (t + x) * Real.sqrt (t + y) *
      Real.sqrt (t + z))⁻¹) (Ioi 0) := by
  let m : ℝ := min x (min y z)
  have hm : 0 < m := lt_min hx (lt_min hy hz)
  have hmx : m ≤ x := min_le_left _ _
  have hmy : m ≤ y := (min_le_right _ _).trans (min_le_left _ _)
  have hmz : m ≤ z := (min_le_right _ _).trans (min_le_right _ _)
  have hdom := integrableOn_add_rpow_Ioi_of_lt (a := (-3 / 2 : ℝ))
    (c := 0) (m := m) (by norm_num) (by linarith)
  refine hdom.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have htm : 0 < t + m := by linarith
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.sqrt (t + m) ^ 3)⁻¹ := by
      apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      calc Real.sqrt (t + m) ^ 3 = Real.sqrt (t + m) * Real.sqrt (t + m) *
          Real.sqrt (t + m) := by ring
        _ ≤ Real.sqrt (t + x) * Real.sqrt (t + y) * Real.sqrt (t + z) := by
          gcongr
    _ = (t + m) ^ (-3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast htm.le, ← Real.rpow_neg htm.le]
      norm_num

/-- The substitution `t = xyz/u` removes the unshifted root in a reciprocal quartic kernel. -/
lemma integral_inv_sqrt_mul_sqrt_add_mul_sqrt_add_mul_sqrt_add
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∫ t in Ioi (0 : ℝ), (Real.sqrt t * (Real.sqrt (t + x) * Real.sqrt (t + y) *
      Real.sqrt (t + z)))⁻¹ =
    ∫ u in Ioi (0 : ℝ), (Real.sqrt (u + x * y) * Real.sqrt (u + x * z) *
      Real.sqrt (u + y * z))⁻¹ := by
  set c : ℝ := x * y * z
  have hc : 0 < c := by positivity
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => c / u) (-c / u ^ 2)
      (Ioi 0) u := by
    intro u hu
    simpa only [div_eq_mul_inv, mul_neg, neg_mul] using
      ((hasDerivAt_inv hu.ne').const_mul c).hasDerivWithinAt
  have hi : InjOn (fun u : ℝ => c / u) (Ioi 0) := by
    intro u hu v hv h
    field_simp [hu.ne', hv.ne'] at h
    exact h.symm
  have him : (fun u : ℝ => c / u) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact div_pos hc hv
    · intro hu
      refine ⟨c / u, div_pos hc hu, ?_⟩
      field_simp [hc.ne', hu.ne']
  have H := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hi
    (fun t : ℝ => (Real.sqrt t * (Real.sqrt (t + x) * Real.sqrt (t + y) *
      Real.sqrt (t + z)))⁻¹)
  rw [him] at H
  rw [H]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : 0 < u := hu
  simp only [smul_eq_mul]
  rw [abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hc) (sq_pos_of_pos hu'))]
  have h1 : c / u + x = x * (u + y * z) / u := by dsimp only [c]; field_simp [hu'.ne']; ring
  have h2 : c / u + y = y * (u + x * z) / u := by dsimp only [c]; field_simp [hu'.ne']; ring
  have h3 : c / u + z = z * (u + x * y) / u := by dsimp only [c]; field_simp [hu'.ne']; ring
  rw [h1, h2, h3, Real.sqrt_div hc.le, Real.sqrt_div (by positivity : 0 ≤ x * (u + y * z)),
    Real.sqrt_div (by positivity : 0 ≤ y * (u + x * z)),
    Real.sqrt_div (by positivity : 0 ≤ z * (u + x * y)),
    Real.sqrt_mul hx.le, Real.sqrt_mul hy.le, Real.sqrt_mul hz.le]
  have hs : Real.sqrt c = Real.sqrt x * Real.sqrt y * Real.sqrt z := by
    dsimp only [c]
    rw [Real.sqrt_mul (by positivity : 0 ≤ x * y), Real.sqrt_mul hx.le]
  rw [hs]
  have hsu : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hcu : c ≠ 0 := hc.ne'
  have hu0 : u ≠ 0 := hu.ne'
  have hsur : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  field_simp [hcu, hu0, hsur]
  have hfour : Real.sqrt u ^ 4 = u ^ 2 := by
    rw [show Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 by ring, hsu]
  rw [hfour,
    Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le]
  dsimp only [c]
  ring

/-- The reciprocal cubic square-root kernel has a positive integral on `(0, ∞)`. -/
lemma integral_inv_sqrt_add_mul_sqrt_add_mul_sqrt_add_pos
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < ∫ t in Ioi (0 : ℝ), (Real.sqrt (t + x) * Real.sqrt (t + y) *
      Real.sqrt (t + z))⁻¹ := by
  have hi := integrableOn_inv_sqrt_add_mul_sqrt_add_mul_sqrt_add hx hy hz
  have hn : ∀ t : ℝ, 0 ≤ (Real.sqrt (t + x) * Real.sqrt (t + y) *
      Real.sqrt (t + z))⁻¹ := fun _ => by positivity
  refine (integral_pos_iff_support_of_nonneg hn hi).mpr ?_
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun t : ℝ =>
      (Real.sqrt (t + x) * Real.sqrt (t + y) * Real.sqrt (t + z))⁻¹) := by
    intro t ht
    have ht0 : 0 < t := ht
    exact ne_of_gt (by positivity)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp

/-- The reciprocal quartic square-root kernel is integrable on `(0, ∞)`. -/
lemma integrableOn_inv_sqrt_mul_sqrt_add_mul_sqrt_add_mul_sqrt_add
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => (Real.sqrt t * (Real.sqrt (t + x) * Real.sqrt (t + y) *
      Real.sqrt (t + z)))⁻¹) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_inv_sqrt_mul_sqrt_add_mul_sqrt_add_mul_sqrt_add hx hy hz]
  exact ne_of_gt (integral_inv_sqrt_add_mul_sqrt_add_mul_sqrt_add_pos
    (mul_pos hx hy) (mul_pos hx hz) (mul_pos hy hz))

/-- A reciprocal square root times a positive linear factor is integrable on `(0, ∞)`. -/
lemma integrableOn_inv_sqrt_add_mul_add {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => (Real.sqrt (v + p) * (v + x))⁻¹) (Ioi 0) := by
  have hi := integrableOn_inv_sqrt_add_mul_sqrt_add_mul_sqrt_add hp hx hx
  refine hi.congr_fun (fun v hv => ?_) measurableSet_Ioi
  have hv0 : 0 < v := hv
  dsimp only
  rw [mul_assoc, Real.mul_self_sqrt (by positivity : 0 ≤ v + x)]

/-- Scaling the two positive linear factors reduces their common constant term to one. -/
lemma integral_inv_sqrt_add_mul_add_linear {u p x : ℝ} (hu : 0 < u) (hp : 0 < p) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), (Real.sqrt (u + x * t) * (u + p * t))⁻¹) =
      (Real.sqrt p * Real.sqrt u)⁻¹ *
        ∫ v in Ioi (0 : ℝ), (Real.sqrt (v + p) * (v + x))⁻¹ := by
  let c : ℝ := p * x / u
  have hc : 0 < c := by dsimp [c]; positivity
  have he (t : ℝ) (ht : 0 < t) :
      (Real.sqrt (u + x * t) * (u + p * t))⁻¹ =
      (x * Real.sqrt (p / u) / u) * (Real.sqrt (c * t + p) * (c * t + x))⁻¹ := by
    have h1 : c * t + p = (p / u) * (u + x * t) := by dsimp [c]; field_simp; ring
    have h2 : c * t + x = (x / u) * (u + p * t) := by dsimp [c]; field_simp; ring
    rw [h1,h2, Real.sqrt_mul (by positivity : 0 ≤ p / u)]
    field_simp
  calc
    _ = ∫ t in Ioi (0 : ℝ), (x * Real.sqrt (p / u) / u) *
        (Real.sqrt (c * t + p) * (c * t + x))⁻¹ :=
      setIntegral_congr_fun measurableSet_Ioi he
    _ = (x * Real.sqrt (p / u) / u) * (c⁻¹ *
        ∫ v in Ioi (0 : ℝ), (Real.sqrt (v + p) * (v + x))⁻¹) := by
      rw [integral_const_mul]
      congr 1
      simpa only [mul_zero, smul_eq_mul] using integral_comp_mul_left_Ioi
        (fun v : ℝ => (Real.sqrt (v + p) * (v + x))⁻¹) 0 hc
    _ = _ := by
      rw [Real.sqrt_div hp.le]
      dsimp [c]
      field_simp
      rw [Real.sq_sqrt hp.le]

/-- Reciprocal square-root kernels with two positive linear factors are integrable. -/
lemma integrableOn_inv_sqrt_add_mul_add_linear {u p x : ℝ} (hu : 0 < u) (hp : 0 < p) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (Real.sqrt (u + x * t) * (u + p * t))⁻¹) (Ioi 0) := by
  let c : ℝ := p * x / u
  have hc : 0 < c := by dsimp [c]; positivity
  have hbase := integrableOn_inv_sqrt_add_mul_add hp hx
  have hs : IntegrableOn (fun t : ℝ => (Real.sqrt (c * t + p) * (c * t + x))⁻¹) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun v : ℝ => (Real.sqrt (v + p) * (v + x))⁻¹) 0 hc).mpr
    simpa only [mul_zero] using hbase
  apply IntegrableOn.congr_fun (hs.const_mul (x * Real.sqrt (p / u) / u)) ?_ measurableSet_Ioi
  intro t _
  dsimp only
  have h1 : c * t + p = (p / u) * (u + x * t) := by dsimp [c]; field_simp; ring
  have h2 : c * t + x = (x / u) * (u + p * t) := by dsimp [c]; field_simp; ring
  rw [h1,h2, Real.sqrt_mul (by positivity : 0 ≤ p / u)]
  field_simp


/-- One unshifted root and two positive shifted roots give an integrable kernel. -/
lemma integrableOn_inv_sqrt_mul_sqrt_add_mul_sqrt_add {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => (Real.sqrt u * Real.sqrt (u + y) *
      Real.sqrt (u + z))⁻¹) (Ioi 0) := by
  let m : ℝ := min y z
  have hm : 0 < m := lt_min hy hz
  have hmy : m ≤ y := min_le_left _ _
  have hmz : m ≤ z := min_le_right _ _
  refine (MeasureTheory.integrableOn_inv_sqrt_mul_add hm).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  rw [Real.norm_of_nonneg (by positivity), one_div]
  apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
  have he : u + m = Real.sqrt (u + m) * Real.sqrt (u + m) := by
    rw [Real.mul_self_sqrt (by positivity : 0 ≤ u + m)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg u)
  rw [he]
  gcongr

end Real
