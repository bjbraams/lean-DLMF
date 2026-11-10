/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Fourier.HyperbolicSecant
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# A logarithmic hyperbolic secant integral

The identity `2 sinh(x/3) / cosh(x) = tanh(x) - tanh(x/3)` reduces the integral of
`sinh(x/3) / (x cosh(x))` to Frullani's formula. The quotient has a removable
singularity at zero and exponential decay at both infinities.

## Main results

* `Real.integrable_sinh_div_three_div_mul_cosh`: absolute integrability of the kernel.
* `Real.integral_sinh_div_three_div_mul_cosh`: its integral is `log 3`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology

namespace Real

/-- A hyperbolic secant kernel is a difference of two hyperbolic tangents. -/
lemma sinh_div_three_div_cosh_eq_tanh_sub (x : ℝ) :
    sinh (x / 3) / cosh x = (tanh x - tanh (x / 3)) / 2 := by
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
  have h := sinh_sub x (x / 3)
  have h2 := sinh_two_mul (x / 3)
  rw [show x - x / 3 = 2 * (x / 3) by ring, h2] at h
  field_simp
  nlinarith [h]

/-- The continuous extension of the quotient at its removable singularity at zero. -/
private lemma continuous_sinh_div_three_extension :
    Continuous fun x : ℝ => dslope (fun u : ℝ => sinh (u / 3)) 0 x / cosh x := by
  apply Continuous.div _ continuous_cosh (fun x => (cosh_pos x).ne')
  rw [← continuousOn_univ, continuousOn_dslope (univ_mem : univ ∈ 𝓝 (0 : ℝ))]
  exact ⟨by fun_prop, by fun_prop⟩

/-- The hyperbolic tangent tends to one at positive infinity. -/
lemma tendsto_tanh_atTop : Tendsto tanh atTop (𝓝 1) := by
  have h (x : ℝ) : tanh x = (1 - exp (-2 * x)) / (1 + exp (-2 * x)) := by
    rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq]
    have he := exp_pos x
    have he2 : exp (-(x * 2)) * exp x = exp (-x) := by
      rw [← exp_add]; congr 1; ring
    field_simp
    nlinarith
  change Tendsto (fun x : ℝ => tanh x) atTop (𝓝 1)
  simp_rw [h]
  have hz : Tendsto (fun x : ℝ => exp (-2 * x)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have ho : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hd := (ho.sub hz).div (ho.add hz) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  convert hd using 1
  norm_num


/-- The logarithmic hyperbolic secant kernel is absolutely integrable. -/
lemma integrable_sinh_div_three_div_mul_cosh :
    Integrable (fun x : ℝ => sinh (x / 3) / (x * cosh x)) := by
  let k : ℝ → ℝ := fun x => dslope (fun u : ℝ => sinh (u / 3)) 0 x / cosh x
  have hk : Continuous k := continuous_sinh_div_three_extension
  have heq {x : ℝ} (hx : x ≠ 0) : k x = sinh (x / 3) / (x * cosh x) := by
    dsimp [k]
    rw [dslope_of_ne _ hx]
    simp [slope, smul_eq_mul, div_eq_mul_inv]
    ring
  have htail : IntegrableOn k (Ioi 1) := by
    have hb := (Complex.integral_exp_div_cosh (c := 1 / 6) (by norm_num)).1.re
    have hreal : Integrable (fun x : ℝ => exp (x / 3) / cosh x) := by
      convert hb using 1
      ext x
      change exp (x / 3) / cosh x =
        (Complex.exp (2 * (1 / 6 : ℂ) * x) / (cosh x : ℂ)).re
      rw [show 2 * (1 / 6 : ℂ) * x = ((x / 3 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, ← Complex.ofReal_div, Complex.ofReal_re]
    refine hreal.integrableOn.mono' hk.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    rw [heq hx0.ne', norm_eq_abs, abs_of_nonneg (by positivity)]
    have hs : sinh (x / 3) ≤ exp (x / 3) := by
      rw [sinh_eq]
      linarith [exp_pos (x / 3), exp_pos (-(x / 3))]
    have hb : sinh (x / 3) ≤ x * exp (x / 3) := by
      nlinarith [exp_pos (x / 3)]
    exact (div_le_div_iff₀ (by positivity) (cosh_pos x)).mpr (by
      nlinarith [cosh_pos x])
  have hIcc : IntegrableOn k (Ioc 0 1) := hk.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpos : IntegrableOn k (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hIcc.union htail
  have hneg : IntegrableOn k (Iic 0) := by
    have h := hpos.comp_neg
    simp only [neg_Ioi, neg_zero] at h
    have hi : IntegrableOn k (Iio 0) := by
      refine h.congr_fun (fun x hx => ?_) measurableSet_Iio
      have hx0 : x ≠ 0 := ne_of_lt hx
      change k (-x) = k x
      rw [heq (neg_ne_zero.mpr hx0), heq hx0]
      simp [neg_div, sinh_neg, cosh_neg, div_neg]
    exact (integrableOn_Iic_iff_integrableOn_Iio).mpr hi
  have hi : Integrable k := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hneg.union hpos
  refine hi.congr ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  exact heq hx

/-- Frullani's formula evaluates a logarithmic hyperbolic secant integral. -/
lemma integral_sinh_div_three_div_mul_cosh :
    (∫ x : ℝ, sinh (x / 3) / (x * cosh x)) = log 3 := by
  have hf : Continuous tanh := by
    change Continuous (fun x : ℝ => tanh x)
    simp only [tanh_eq_sinh_div_cosh]
    exact continuous_sinh.div continuous_cosh (fun x => (cosh_pos x).ne')
  have hp := integrable_sinh_div_three_div_mul_cosh.integrableOn (s := Ioi (0 : ℝ))
  have hpt (x : ℝ) : x⁻¹ • (tanh (1 * x) - tanh ((1 / 3) * x)) =
      2 * (sinh (x / 3) / (x * cosh x)) := by
    rw [one_mul, show (1 / 3 : ℝ) * x = x / 3 by ring]
    have h := sinh_div_three_div_cosh_eq_tanh_sub x
    simp only [smul_eq_mul]
    have hh : tanh x - tanh (x / 3) = 2 * (sinh (x / 3) / cosh x) := by linarith [h]
    rw [hh]
    ring
  have hf0 : Tendsto tanh (𝓝[>] 0) (𝓝 0) := by
    simpa [tanh_eq_sinh_div_cosh] using
      (hf.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hfr := Frullani.integral_Ioi_eq (f := tanh) (a := 1) (b := 1 / 3)
    (hf.locallyIntegrable.locallyIntegrableOn _) (by norm_num) (by norm_num)
    hf0 tendsto_tanh_atTop
    (IntegrableOn.congr_fun (hp.const_mul 2)
      (fun x _ => (hpt x).symm) measurableSet_Ioi)
  simp only [hpt, integral_const_mul, div_one, zero_sub, smul_eq_mul,
    mul_neg, mul_one] at hfr
  have heven : ∫ x : ℝ, sinh (x / 3) / (x * cosh x) =
      2 * ∫ x in Ioi (0 : ℝ), sinh (x / 3) / (x * cosh x) := by
    have ha := integral_comp_abs (f := fun x : ℝ => sinh (x / 3) / (x * cosh x))
    have habs (x : ℝ) : sinh (|x| / 3) / (|x| * cosh |x|) =
        sinh (x / 3) / (x * cosh x) := by
      rcases abs_choice x with h | h <;> rw [h]
      simp only [neg_div, sinh_neg, cosh_neg, neg_mul, div_neg, neg_neg]
    simpa only [habs] using ha
  rw [heven, hfr, log_div (by norm_num) (by norm_num), log_one]
  ring

end Real
