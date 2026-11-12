/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Fourier.HyperbolicSecantLog
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# An integrable hyperbolic comparison remainder

The primitive `coth u - 1/u` increases from zero to one on the positive axis. Its
derivative `u⁻²-csch² u` is therefore absolutely integrable with integral one.
The proof uses the improper fundamental theorem of calculus and the hyperbolic
inequalities `u ≤ sinh u ≤ u cosh u`.
-/

open Filter Set MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section
namespace Real

/-- For nonnegative argument, `sinh u ≤ u cosh u`. -/
lemma sinh_le_mul_cosh {u : ℝ} (hu : 0 ≤ u) : sinh u ≤ u*cosh u := by
  let f : ℝ → ℝ := fun u => u*cosh u-sinh u
  have hd (u : ℝ) : HasDerivAt f (u*sinh u) u := by
    convert ((hasDerivAt_id u).mul (hasDerivAt_cosh u)).sub (hasDerivAt_sinh u) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun u _ => (hd u).continuousAt.continuousWithinAt)
      (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
    intro u hu
    rw [interior_Ici] at hu
    rw [(hd u).deriv]
    exact mul_nonneg hu.le (sinh_nonneg_iff.mpr hu.le)
  have h := hm (by simp) hu hu
  simpa only [f, zero_mul, sinh_zero, sub_zero, sub_nonneg] using h

/-- For positive argument, `0 ≤ coth u - 1/u ≤ sinh u`. -/
lemma cosh_div_sinh_sub_inv_bounds {u : ℝ} (hu : 0 < u) :
    0 ≤ cosh u/sinh u-u⁻¹ ∧ cosh u/sinh u-u⁻¹ ≤ sinh u := by
  have hs : 0 < sinh u := sinh_pos_iff.mpr hu
  have he : cosh u/sinh u-u⁻¹ = (u*cosh u-sinh u)/(u*sinh u) := by field_simp
  rw [he]
  constructor
  · exact div_nonneg (sub_nonneg.mpr (sinh_le_mul_cosh hu.le)) (mul_nonneg hu.le hs.le)
  · rw [div_le_iff₀ (mul_pos hu hs)]
    have hc : cosh u-1 ≤ sinh u^2 := by
      nlinarith [cosh_sq_sub_sinh_sq u, one_le_cosh u, sq_nonneg (cosh u-1)]
    have hc' := mul_le_mul_of_nonneg_left hc hu.le
    nlinarith [self_le_sinh_iff.mpr hu.le]

/-- The derivative of `coth u - 1/u` is `u⁻² - csch² u` on the positive axis. -/
lemma hasDerivAt_cosh_div_sinh_sub_inv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => cosh u/sinh u-u⁻¹)
      (u⁻¹^2-(sinh u)⁻¹^2) u := by
  have hs : sinh u ≠ 0 := (sinh_pos_iff.mpr hu).ne'
  convert ((hasDerivAt_cosh u).div (hasDerivAt_sinh u) hs).sub
    ((hasDerivAt_id u).inv hu.ne') using 1
  · rfl
  · simp only [id_eq]
    field_simp
    nlinarith [cosh_sq_sub_sinh_sq u]

/-- The nonnegative hyperbolic comparison remainder has total integral one. -/
private lemma integral_and_integrable_inv_sq_sub_inv_sinh_sq :
    (∫ u : ℝ in Ioi 0, u⁻¹^2-(sinh u)⁻¹^2) = 1 ∧
      IntegrableOn (fun u : ℝ => u⁻¹^2-(sinh u)⁻¹^2) (Ioi 0) := by
  have hzero : Tendsto (fun u : ℝ => cosh u/sinh u-u⁻¹) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' ?_ ?_
      (continuous_sinh.tendsto' 0 0 (by simp) |>.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with u hu using (cosh_div_sinh_sub_inv_bounds hu).1
    · filter_upwards [self_mem_nhdsWithin] with u hu using (cosh_div_sinh_sub_inv_bounds hu).2
  have hcont : ContinuousWithinAt (fun u : ℝ => cosh u/sinh u-u⁻¹) (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    simpa only [ContinuousWithinAt, cosh_zero, sinh_zero, div_zero, inv_zero, sub_self] using hzero
  have htop : Tendsto (fun u : ℝ => cosh u/sinh u-u⁻¹) atTop (𝓝 1) := by
    have h := (tendsto_tanh_atTop.inv₀ one_ne_zero).sub tendsto_inv_atTop_zero
    simpa only [tanh_eq_sinh_div_cosh, inv_div, inv_one, sub_zero] using h
  have hpos : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ u⁻¹^2-(sinh u)⁻¹^2 := by
    intro u hu
    have hs := self_le_sinh_iff.mpr hu.le
    have hsi : (sinh u)⁻¹ ≤ u⁻¹ := inv_anti₀ hu hs
    have hsn : 0 ≤ (sinh u)⁻¹ := inv_nonneg.mpr (sinh_nonneg_iff.mpr hu.le)
    nlinarith
  have hderiv := fun u (hu : u ∈ Ioi (0 : ℝ)) => hasDerivAt_cosh_div_sinh_sub_inv hu
  refine ⟨?_, integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos htop⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos htop
  simpa using h

/-- The difference `u⁻²-csch² u` is absolutely integrable on the positive axis. -/
lemma integrableOn_inv_sq_sub_inv_sinh_sq :
    IntegrableOn (fun u : ℝ => u⁻¹ ^ 2 - (sinh u)⁻¹ ^ 2) (Ioi 0) :=
  integral_and_integrable_inv_sq_sub_inv_sinh_sq.2

/-- The total variation of the primitive `coth u - 1/u` on `(0,∞)` is one. -/
lemma integral_Ioi_inv_sq_sub_inv_sinh_sq :
    (∫ u : ℝ in Ioi 0, u⁻¹ ^ 2 - (sinh u)⁻¹ ^ 2) = 1 :=
  integral_and_integrable_inv_sq_sub_inv_sinh_sq.1

/-- For positive argument, the hyperbolic cotangent is greater than one. -/
lemma one_lt_cosh_div_sinh {u : ℝ} (hu : 0 < u) : 1 < cosh u / sinh u := by
  have hs := sinh_pos_iff.mpr hu
  rw [lt_div_iff₀ hs, one_mul]
  have hc := cosh_pos u
  nlinarith [cosh_sq_sub_sinh_sq u]
/-- The hyperbolic cotangent identity on the positive axis. -/
lemma one_sub_cosh_div_sinh_sq {u : ℝ} (hu : 0 < u) :
    1 - (cosh u / sinh u)^2 = -1 / sinh u^2 := by
  have hs := (sinh_pos_iff.mpr hu).ne'
  field_simp
  nlinarith [cosh_sq_sub_sinh_sq u]
/-- The derivative of the hyperbolic cotangent on the positive axis. -/
lemma hasDerivAt_cosh_div_sinh {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => cosh u / sinh u) (1-(cosh u/sinh u)^2) u := by
  convert (hasDerivAt_cosh u).div (hasDerivAt_sinh u) (sinh_pos_iff.mpr hu).ne' using 1
  field_simp
/-- The hyperbolic cotangent tends to one at positive infinity. -/
lemma tendsto_cosh_div_sinh_atTop :
    Tendsto (fun u : ℝ => cosh u / sinh u) atTop (𝓝 1) := by
  simpa only [tanh_eq_sinh_div_cosh, inv_div, inv_one] using
    tendsto_tanh_atTop.inv₀ one_ne_zero


/-- The real logarithmic coordinate of the hyperbolic cotangent. -/
lemma log_cosh_div_sinh_ratio {u : ℝ} (hu : 0 < u) :
    log (cosh u / sinh u + 1) - log (cosh u / sinh u - 1) = 2*u := by
  have hs : sinh u ≠ 0 := (sinh_pos_iff.mpr hu).ne'
  have hp : cosh u/sinh u+1 = exp u/sinh u := by
    rw [← cosh_add_sinh]; field_simp
  have hm : cosh u/sinh u-1 = exp (-u)/sinh u := by
    rw [← cosh_sub_sinh]; field_simp
  rw [hp, hm, log_div (exp_ne_zero _) hs, log_div (exp_ne_zero _) hs, log_exp, log_exp]
  ring

/-- The comparison remainder `u⁻²-csch² u` is nonnegative for positive `u`. -/
lemma inv_sq_sub_inv_sinh_sq_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ u⁻¹^2-(Real.sinh u)⁻¹^2 := by
  have hs := Real.self_le_sinh_iff.mpr hu.le
  have hi := inv_anti₀ hu hs
  have hn : 0 ≤ (Real.sinh u)⁻¹ := inv_nonneg.mpr (Real.sinh_nonneg_iff.mpr hu.le)
  nlinarith

end Real

namespace Complex

/-- The positive hyperbolic coordinate lies on the principal exterior sheet. -/
lemma cosh_div_sinh_sub_one_mem_slitPlane {u : ℝ} (hu : 0 < u) :
    (Real.cosh u / Real.sinh u : ℂ)-1 ∈ slitPlane := by
  rw [← ofReal_div, ← ofReal_one, ← ofReal_sub, ofReal_mem_slitPlane]
  linarith [Real.one_lt_cosh_div_sinh hu]
/-- The principal logarithmic gauge becomes a decreasing exponential. -/
lemma exp_mul_log_cosh_div_sinh_ratio (μ : ℂ) {u : ℝ} (hu : 0 < u) :
    exp (μ/2 * (log ((Real.cosh u / Real.sinh u : ℂ)+1) -
      log ((Real.cosh u / Real.sinh u : ℂ)-1))) = exp (μ*u) := by
  have hp : 0 < Real.cosh u / Real.sinh u + 1 := by
    linarith [Real.one_lt_cosh_div_sinh hu]
  have hm : 0 < Real.cosh u / Real.sinh u - 1 := by
    linarith [Real.one_lt_cosh_div_sinh hu]
  have hl : log ((Real.cosh u / Real.sinh u : ℂ)+1) -
      log ((Real.cosh u / Real.sinh u : ℂ)-1) = (2*u : ℝ) := by
    rw [← ofReal_div, ← ofReal_one, ← ofReal_add, ← ofReal_sub,
      ← ofReal_log hp.le, ← ofReal_log hm.le, ← ofReal_sub,
      Real.log_cosh_div_sinh_ratio hu]
  rw [hl]
  congr 1
  push_cast
  ring

end Complex
