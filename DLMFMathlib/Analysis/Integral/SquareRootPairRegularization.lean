/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.LogarithmicSquareRootKernel
public import Mathlib.Analysis.Asymptotics.Ring

/-!
# Regularization of a pair of square roots

For nonnegative shifts `x,y`, the numerator `1-t/√((t+x)(t+y))` lies between zero
and `a/(t+a)`, where `a=(x+y)/2`. A positive shifted square-root and linear factor
then give an integrable kernel with a logarithmic rational-tail bound. Reciprocal logarithms
with different positive numerator constants have the same asymptotic order at zero.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Real

namespace MeasureTheory.SquareRootPairRegularization

/-- The numerator obtained by removing the zero-node limit of a pair-root kernel. -/
def numerator (x y t : ℝ) : ℝ := 1 - t / (√(t + x) * √(t + y))

/-- The arithmetic mean controls the regularized pair-root numerator. -/
theorem numerator_bounds {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t) :
    0 ≤ numerator x y t ∧ numerator x y t ≤ ((x + y) / 2) / (t + (x + y) / 2) := by
  let D : ℝ := √(t + x) * √(t + y)
  let a : ℝ := (x + y) / 2
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have htx : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
  have hty : 0 < t + y := add_pos_of_pos_of_nonneg ht hy
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr htx) (Real.sqrt_pos.mpr hty)
  have hDsq : D ^ 2 = (t + x) * (t + y) := by
    dsimp only [D]
    rw [mul_pow, Real.sq_sqrt htx.le, Real.sq_sqrt hty.le]
  have hlow : t ≤ D := by nlinarith
  have hupp : D ≤ t + a := by dsimp only [a]; nlinarith [sq_nonneg (x - y)]
  have hta : 0 < t + a := add_pos_of_pos_of_nonneg ht ha
  change 0 ≤ 1 - t / D ∧ 1 - t / D ≤ a / (t + a)
  refine ⟨sub_nonneg.mpr ((div_le_one hD).mpr hlow), ?_⟩
  have H := div_le_div_of_nonneg_left ht.le hD hupp
  calc _ ≤ 1 - t / (t + a) := by linarith
    _ = a / (t + a) := by field_simp; ring

/-- The regularized pair-root kernel with positive outer parameters. -/
def kernel (x y z p t : ℝ) : ℝ := numerator x y t / (√(t + z) * (t + p))

/-- A rational profile majorizes the regularized pair-root kernel. -/
theorem kernel_bounds {x y z p t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 < z) (hp : 0 < p) (ht : 0 < t) :
    0 ≤ kernel x y z p t ∧ kernel x y z p t ≤
      (((x + y) / 2) / √z) * (1 / ((t + (x + y) / 2) * (t + p))) := by
  have H := numerator_bounds hx hy ht
  have htz : 0 < t + z := add_pos ht hz
  have htp : 0 < t + p := add_pos ht hp
  have hta : 0 < t + (x + y) / 2 := by linarith
  refine ⟨div_nonneg H.1 (by positivity), ?_⟩
  unfold kernel
  calc _ ≤ (((x + y) / 2) / (t + (x + y) / 2)) / (√(t + z) * (t + p)) :=
      div_le_div_of_nonneg_right H.2 (by positivity)
    _ ≤ (((x + y) / 2) / (t + (x + y) / 2)) / (√z * (t + p)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) htp.le
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

/-- The regularized pair-root kernel is integrable when its arithmetic shift is below `p`. -/
theorem integrableOn_kernel {x y z p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 < z) (ha : 0 < (x + y) / 2) (hap : (x + y) / 2 < p) :
    IntegrableOn (kernel x y z p) (Ioi 0) := by
  refine ((LogarithmicSquareRoot.integrableOn_inv_mul_add ha hap).const_mul
    (((x + y) / 2) / √z)).mono'
      (show AEStronglyMeasurable (kernel x y z p) (volume.restrict (Ioi 0)) from
        (by unfold kernel numerator; fun_prop : Measurable _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have H := kernel_bounds hx hy hz (ha.trans hap) ht
  rw [Real.norm_eq_abs, abs_of_nonneg H.1]
  exact H.2

/-- The regularized kernel integral has a logarithmic tail bound. -/
theorem integral_kernel_bounds {x y z p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 < z) (ha : 0 < (x + y) / 2) (hap : (x + y) / 2 < p) :
    0 ≤ (∫ t in Ioi (0 : ℝ), kernel x y z p t) ∧
      (∫ t in Ioi (0 : ℝ), kernel x y z p t) ≤
        (((x + y) / 2) / √z) * (Real.log (p / ((x + y) / 2)) / (p - (x + y) / 2)) := by
  have hi := integrableOn_kernel hx hy hz ha hap
  have hR := (LogarithmicSquareRoot.integrableOn_inv_mul_add ha hap).const_mul
    (((x + y) / 2) / √z)
  refine ⟨integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    (kernel_bounds hx hy hz (ha.trans hap) ht).1), ?_⟩
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), (((x + y) / 2) / √z) *
        (1 / ((t + (x + y) / 2) * (t + p))) :=
      integral_mono_ae hi hR (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        (kernel_bounds hx hy hz (ha.trans hap) ht).2)
    _ = _ := by rw [integral_const_mul, LogarithmicSquareRoot.integral_Ioi_inv_mul_add ha hap]


/-- Uniform logarithmic control when the linear parameter stays in a positive interval. -/
theorem integral_kernel_le_uniform {x y z p m P : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 < z) (ha : 0 < (x + y) / 2) (hm : 0 < m) (hmp : m ≤ p) (hpP : p ≤ P)
    (ham : (x + y) / 2 ≤ m / 2) :
    (∫ t in Ioi (0 : ℝ), kernel x y z p t) ≤
      (2 / (m * √z)) * (((x + y) / 2) * Real.log (P / ((x + y) / 2))) := by
  let a : ℝ := (x + y) / 2
  have hap : a < p := by dsimp only [a]; linarith
  have hlog : 0 ≤ Real.log (p / a) :=
    Real.log_nonneg ((le_div_iff₀ ha).mpr (by simpa only [one_mul] using hap.le))
  have hlogP : Real.log (p / a) ≤ Real.log (P / a) :=
    Real.log_le_log (div_pos (hm.trans_le hmp) ha) (div_le_div_of_nonneg_right hpP ha.le)
  calc
    _ ≤ (a / √z) * (Real.log (p / a) / (p - a)) :=
      (integral_kernel_bounds hx hy hz ha hap).2
    _ ≤ (a / √z) * (Real.log (p / a) / (m / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left hlog (half_pos hm) (by dsimp only [a]; linarith)
    _ ≤ (a / √z) * (Real.log (P / a) / (m / 2)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogP (half_pos hm).le)
        (by positivity)
    _ = _ := by ring

end MeasureTheory.SquareRootPairRegularization

namespace Real

open Asymptotics
open scoped Topology

/-- Constants are negligible relative to the logarithm of a positive reciprocal near zero. -/
theorem isLittleO_const_log_const_div_nhdsGT_zero {p : ℝ} (hp : 0 < p) (c : ℝ) :
    (fun _ : ℝ => c) =o[𝓝[>] 0] (fun x : ℝ => log (p / x)) := by
  simpa only [Function.comp_def, div_eq_mul_inv] using
    (isLittleO_const_log_atTop (c := c)).comp_tendsto
      ((tendsto_inv_nhdsGT_zero : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop).const_mul_atTop hp)

/-- Positive constants inside a reciprocal logarithm do not change its order near zero. -/
theorem isBigO_log_const_div_log_const_div_nhdsGT_zero {k p : ℝ}
    (hk : 0 < k) (hp : 0 < p) :
    (fun x : ℝ => log (k / x)) =O[𝓝[>] 0] (fun x : ℝ => log (p / x)) := by
  have H := (isLittleO_const_log_const_div_nhdsGT_zero hp (log (k / p))).isBigO.add
    (isBigO_refl (fun x : ℝ => log (p / x)) (𝓝[>] (0 : ℝ)))
  apply H.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [log_div hk.ne' hp.ne', log_div hp.ne' hx.ne', log_div hk.ne' hx.ne']
  ring

/-- A reciprocal logarithm with positive numerator has the order of `log x` near zero. -/
theorem isBigO_log_const_div_log_nhdsGT_zero {k : ℝ} (hk : 0 < k) :
    (fun x : ℝ => log (k / x)) =O[𝓝[>] 0] log := by
  have H := ((isLittleO_const_id_atBot (log k)).comp_tendsto tendsto_log_nhdsGT_zero).isBigO.sub
    (isBigO_refl log (𝓝[>] (0 : ℝ)))
  apply H.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply]
  rw [log_div hk.ne' hx.ne']

/-- A linear error is dominated by `x log x` at a positive zero endpoint. -/
theorem isBigO_id_mul_log_nhdsGT_zero :
    (fun x : ℝ => x) =O[𝓝[>] 0] (fun x : ℝ => x * log x) := by
  have H := ((isLittleO_const_id_atBot (1 : ℝ)).comp_tendsto tendsto_log_nhdsGT_zero).isBigO
  simpa only [Function.comp_def, id_eq, mul_one] using
    (isBigO_refl (fun x : ℝ => x) (𝓝[>] (0 : ℝ))).mul H

end Real
