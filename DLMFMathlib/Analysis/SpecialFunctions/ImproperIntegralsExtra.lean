/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Elementary improper integrals on `(0, ∞)`

* integrability of `t^r e^{-s t}` (`r > -1`, `s > 0`) and of its complex analogue
  `v^{b-1} e^{-z v}` (`Re b > 0`, `Re z > 0`);
* the Frullani-type integral `∫₀^∞ ((1+τ)⁻¹ - (1+xτ)⁻¹)/τ dτ = log x` for `x > 0`.
-/

@[expose] public section
open Filter Set MeasureTheory
open scoped Topology

/-- `t ↦ t^r e^{-s t}` is integrable on `(0, ∞)` for `r > -1` and `s > 0`. -/
theorem integrableOn_rpow_mul_exp_neg_mul {r s : ℝ} (hr : -1 < r) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-(s * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := r) (b := s) hr one_pos hs
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- `v ↦ v^{b-1} e^{-z v}` is integrable on `(0, ∞)` for `Re b > 0` and `Re z > 0`. -/
theorem Complex.integrableOn_cpow_mul_exp_neg_mul {b z : ℂ} (hb : 0 < b.re) (hz : 0 < z.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (b - 1) * Complex.exp (-(z * v))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b.re - 1) (b := z.re)
    (by linarith) one_pos hz
  refine Integrable.mono' h (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp, Real.rpow_one]
  simp

/-- A Frullani-type integral: for `x > 0` the function `((1+τ)⁻¹ - (1+xτ)⁻¹)/τ` is integrable
on `(0, ∞)` with integral `log x`. -/
theorem integrableOn_and_integral_inv_one_add_sub_inv_one_add_mul_div {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / (1 + τ) - 1 / (1 + x * τ)) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / (1 + τ) - 1 / (1 + x * τ)) / τ = Real.log x := by
  set G : ℝ → ℝ := fun τ => Real.log (1 + x * τ) - Real.log (1 + τ) with hG
  have hderiv : ∀ τ ∈ Ioi (0 : ℝ), HasDerivAt G ((1 / (1 + τ) - 1 / (1 + x * τ)) / τ) τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have h1 : HasDerivAt (fun τ : ℝ => Real.log (1 + x * τ)) (x / (1 + x * τ)) τ := by
      have hp : (1 : ℝ) + x * id τ ≠ 0 := by simp only [id_eq]; positivity
      have := (((hasDerivAt_id τ).const_mul x).const_add 1).log hp
      simpa using this
    have h2 : HasDerivAt (fun τ : ℝ => Real.log (1 + τ)) (1 / (1 + τ)) τ := by
      have := ((hasDerivAt_id τ).const_add 1).log (by simp; linarith)
      simpa using this
    convert h1.sub h2 using 1
    have : 0 < 1 + x * τ := by positivity
    field_simp
    ring
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    have : ContinuousAt G 0 := by
      refine ContinuousAt.sub ?_ ?_
      · exact (continuousAt_const.add (continuousAt_id.const_mul x)).log (by norm_num)
      · exact (continuousAt_const.add continuousAt_id).log (by norm_num)
    exact this.continuousWithinAt
  have hlim : Tendsto G atTop (𝓝 (Real.log x)) := by
    set h : ℝ → ℝ := fun u => Real.log ((u + x) / (u + 1)) with hh
    have hhc : ContinuousAt h 0 := by
      refine ContinuousAt.log ?_ (by simp; exact hx.ne')
      exact (continuousAt_id.add continuousAt_const).div (continuousAt_id.add continuousAt_const)
        (by norm_num)
    have h0 : h 0 = Real.log x := by simp [hh]
    have ht := (hhc.tendsto.comp tendsto_inv_atTop_zero)
    rw [h0] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    simp only [Function.comp, hh, hG]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hint : IntegrableOn (fun τ : ℝ => (1 / (1 + τ) - 1 / (1 + x * τ)) / τ) (Ioi 0) := by
    refine Integrable.mono'
      ((integrable_inv_one_add_sq.const_mul (|x - 1| * (1 + 1 / x))).integrableOn)
      ((ContinuousOn.div (ContinuousOn.sub
        (continuousOn_const.div (by fun_prop) fun τ (hτ : 0 < τ) => by positivity)
        (continuousOn_const.div (by fun_prop) fun τ (hτ : 0 < τ) => by positivity)) continuousOn_id
        fun τ hτ => (ne_of_gt (show (0 : ℝ) < τ from hτ))).aestronglyMeasurable
          measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hτ0 : (0 : ℝ) < τ := hτ
    have e : (1 / (1 + τ) - 1 / (1 + x * τ)) / τ = (x - 1) / ((1 + τ) * (1 + x * τ)) := by
      have : 0 < 1 + x * τ := by positivity
      field_simp; ring
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (1 + τ) * (1 + x * τ)),
      div_eq_mul_inv |x - 1|, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < 1 / x := by positivity
    have hx1 : (1 + 1 / x) * x = x + 1 := by field_simp
    nlinarith [mul_pos hτ0 hτ0, mul_pos this hτ0, mul_pos hx hτ0]
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp [hG]
