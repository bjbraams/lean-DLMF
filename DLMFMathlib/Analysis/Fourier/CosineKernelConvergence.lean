/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMFMathlib.Analysis.Fourier.CosinePartialSumKernel
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import DLMFMathlib.Analysis.Fourier.DirichletJordan
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.BoundedVariation
import Mathlib.Tactic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Reparam
/-!
# Convergence of the cosine partial-sum kernel

The one-sided Dirichlet–Jordan theorem, with the analytic sinc correction, gives pointwise
Fourier-kernel convergence for bounded-variation data with one-sided limits. The proof uses
Mathlib's analytic
divided differences and absolute continuity APIs, together with the real Fourier-integral
Dirichlet–Jordan theorem in `DLMFMathlib.Analysis.Fourier.DirichletJordan`. The existing
absolutely continuous forms follow as corollaries.
-/

public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace Real
/-- A one-sided cosine-kernel integral of bounded-variation data tends to half its right
limit, on an interval shorter than a full period. -/
lemma tendsto_integral_cosinePartialSumKernel_oneSided_of_boundedVariationOn
    {g : ℝ → ℂ} {δ : ℝ} {L : ℂ}
    (hδ : 0 < δ) (hδπ : δ < 2 * π)
    (hg : BoundedVariationOn g (Icc 0 δ)) (hL : Tendsto g (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun N : ℕ => (1 / π : ℂ) * ∫ t in (0 : ℝ)..δ,
      g t * (cosinePartialSumKernel N t : ℂ)) atTop (𝓝 (L / 2)) := by
  let H : ℝ → ℂ := fun t => ((sinc (t / 2) : ℂ))⁻¹
  let F : ℝ → ℂ := fun t => H t * g t
  have hs (t : ℝ) (ht : t ∈ Icc 0 δ) : 0 < sinc (t / 2) := by
    apply sinc_pos
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  have hHcd : ContDiffOn ℝ 1 H (uIcc 0 δ) := by
    apply ContDiffOn.inv
    · exact (Complex.ofRealCLM.contDiff.comp
        (contDiff_sinc.comp (contDiff_id.div_const 2))).contDiffOn
    · intro t ht
      exact Complex.ofReal_ne_zero.mpr (hs t (by simpa only [uIcc_of_le hδ.le] using ht)).ne'
  have hH : BoundedVariationOn H (Icc 0 δ) := by
    simpa only [uIcc_of_le hδ.le] using
      hHcd.absolutelyContinuousOnInterval.boundedVariationOn
  have hF : BoundedVariationOn F (Icc 0 δ) := by
    simpa only [F, smul_eq_mul] using hH.fun_smul hg
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 L) := by
    have ht : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝[uIcc 0 δ] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with t ht0 htδ
      rw [uIcc_of_le hδ.le]
      exact ⟨ht0.le, htδ.le⟩
    have h := (hHcd.continuousOn 0 left_mem_uIcc).tendsto.comp ht
    simpa only [Function.comp_def, id_eq, F, H, zero_div, sinc_zero,
      ofReal_one, inv_one, one_mul] using h.mul hL
  have hdir := (tendsto_intervalIntegral_mul_sin_div_of_boundedVariationOn hδ
    hF hlim).2
  have hη : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine (hdir.comp hη).congr fun N => ?_
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht htI
  have hsine : 2 * sin (t / 2) * cosinePartialSumKernel N t = sin ((N + 1 / 2) * t) :=
    two_mul_sin_mul_cosinePartialSumKernel N t
  rw [← hsine]
  simp only [F, H, sinc_of_ne_zero (div_ne_zero ht two_ne_zero), ofReal_div, inv_div,
    ofReal_ofNat]
  have htpos : 0 < t := by simpa only [min_eq_left hδ.le] using htI.1
  have htδ : t ≤ δ := by simpa only [max_eq_right hδ.le] using htI.2
  have hs0 : sin (t / 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith [hδπ])).ne'
  simp only [ofReal_mul, ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr hs0, Complex.ofReal_ne_zero.mpr ht,
    Complex.ofReal_ne_zero.mpr pi_ne_zero]
  ring_nf
  have hcs0 : ((sin (t * (1 / 2)) : ℝ) : ℂ) ≠ 0 := by
    simpa only [div_eq_mul_inv, one_mul] using Complex.ofReal_ne_zero.mpr hs0
  field_simp [hcs0, Complex.ofReal_ne_zero.mpr hs0]
  rw [mul_assoc, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hs0)]

/-- A one-sided cosine-kernel integral of an absolutely continuous function tends to half
its endpoint value, on intervals shorter than a full period. -/
lemma tendsto_integral_cosinePartialSumKernel_oneSided {g : ℝ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < 2 * π)
    (hg : AbsolutelyContinuousOnInterval g 0 δ) :
    Tendsto (fun N : ℕ => (1 / π : ℂ) * ∫ t in (0 : ℝ)..δ,
      g t * (cosinePartialSumKernel N t : ℂ)) atTop (𝓝 (g 0 / 2)) := by
  apply tendsto_integral_cosinePartialSumKernel_oneSided_of_boundedVariationOn hδ hδπ
    (by simpa only [uIcc_of_le hδ.le] using hg.boundedVariationOn)
  have h := (hg.continuousOn 0 left_mem_uIcc).tendsto
  simp only [uIcc_of_le hδ.le, nhdsWithin_Icc_eq_nhdsGE hδ] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- The cosine kernel converges to the value at an interior point of a full period. -/
lemma tendsto_integral_cosinePartialSumKernel_of_mem_Ioo {g : ℝ → ℂ}
    (hg : AbsolutelyContinuousOnInterval g 0 (2 * π)) {x : ℝ}
    (hx0 : 0 < x) (hxπ : x < 2 * π) :
    Tendsto (fun N : ℕ => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π,
      g t * (cosinePartialSumKernel N (t - x) : ℂ)) atTop (𝓝 (g x)) := by
  have hminus : AbsolutelyContinuousOnInterval (fun u => g (x - u)) 0 x := by
    convert hg.comp_affine (-1) x (a := 0) (b := x) ?_ using 1
    · ext u
      simp only [Function.comp_apply, neg_one_mul, sub_eq_add_neg, add_comm]
    · intro u hu
      rw [uIcc_of_le hx0.le] at hu
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
      constructor <;> linarith [hu.1, hu.2]
  have hplus : AbsolutelyContinuousOnInterval (fun u => g (x + u)) 0 (2 * π - x) := by
    convert hg.comp_affine 1 x (a := 0) (b := 2 * π - x) ?_ using 1
    · ext u
      simp only [Function.comp_apply, one_mul, add_comm]
    · intro u hu
      rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * π - x)] at hu
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
      constructor <;> linarith [hu.1, hu.2]
  have hm := tendsto_integral_cosinePartialSumKernel_oneSided hx0 hxπ hminus
  have hp := tendsto_integral_cosinePartialSumKernel_oneSided
    (by linarith : 0 < 2 * π - x) (by linarith : 2 * π - x < 2 * π) hplus
  have hsum := hm.add hp
  simp only [sub_zero, add_zero, add_halves] at hsum
  refine hsum.congr fun N => ?_
  let f : ℝ → ℂ := fun t => g t * (cosinePartialSumKernel N (t - x) : ℂ)
  have hi : IntervalIntegrable f volume 0 (2 * π) :=
    hg.continuousOn.mul ((Complex.continuous_ofReal.comp
      (continuous_cosinePartialSumKernel N)).comp
      (continuous_sub_right x)).continuousOn |>.intervalIntegrable
  have hl := intervalIntegral.integral_comp_sub_left f x (a := 0) (b := x)
  have hr := intervalIntegral.integral_comp_add_left f x (a := 0) (b := 2 * π - x)
  simp only [sub_self, sub_zero] at hl
  have hend : x + (2 * π - x) = 2 * π := by ring
  simp only [add_zero, hend] at hr
  have hl' : (∫ u in (0 : ℝ)..x, g (x - u) * (cosinePartialSumKernel N u : ℂ)) =
      ∫ t in (0 : ℝ)..x, f t := by
    convert hl using 1
    congr 1
    ext u
    dsimp only [f]
    rw [show x - u - x = -u by ring, cosinePartialSumKernel_neg]
  have hr' : (∫ u in (0 : ℝ)..(2 * π - x),
      g (x + u) * (cosinePartialSumKernel N u : ℂ)) = ∫ t in x..2 * π, f t := by
    simpa only [f, add_sub_cancel_left] using hr
  have hx : x ∈ uIcc (0 : ℝ) (2 * π) := by
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    exact ⟨hx0.le, hxπ.le⟩
  have hi1 : IntervalIntegrable f volume 0 x :=
    hi.mono_set (uIcc_subset_uIcc left_mem_uIcc hx)
  have hi2 : IntervalIntegrable f volume x (2 * π) :=
    hi.mono_set (uIcc_subset_uIcc hx right_mem_uIcc)
  rw [← mul_add, hl', hr', intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
/-- For continuous bounded-variation data, the endpoint cosine-kernel integral converges
to the average of the two endpoint values. -/
lemma tendsto_integral_cosinePartialSumKernel_zero_of_boundedVariationOn {g : ℝ → ℂ}
    (hg : BoundedVariationOn g (Icc 0 (2 * π)))
    (hc : ContinuousOn g (Icc 0 (2 * π))) :
    Tendsto (fun N : ℕ => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π,
      g t * (cosinePartialSumKernel N t : ℂ)) atTop (𝓝 ((g 0 + g (2 * π)) / 2)) := by
  have hmap : MapsTo (fun u : ℝ => 2 * π - u) (Icc 0 π) (Icc 0 (2 * π)) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2, pi_pos]
  have href : BoundedVariationOn (fun u => g (2 * π - u)) (Icc 0 π) := by
    exact ne_of_lt ((eVariationOn.comp_le_of_antitoneOn g (fun u : ℝ => 2 * π - u)
      (fun _ _ _ _ h => sub_le_sub_left h _) hmap).trans_lt hg.lt_top)
  have hrefc : ContinuousOn (fun u => g (2 * π - u)) (Icc 0 π) :=
    hc.comp (by fun_prop) hmap
  have hfirst : BoundedVariationOn g (Icc 0 π) :=
    hg.mono (Icc_subset_Icc le_rfl (by linarith [pi_pos]))
  have hL1 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
    have h := (hc 0 ⟨le_rfl, by positivity⟩).tendsto
    rw [nhdsWithin_Icc_eq_nhdsGE (by positivity : (0 : ℝ) < 2 * π)] at h
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hL2 : Tendsto (fun u => g (2 * π - u)) (𝓝[>] 0) (𝓝 (g (2 * π))) := by
    have h := (hrefc 0 ⟨le_rfl, pi_pos.le⟩).tendsto
    rw [nhdsWithin_Icc_eq_nhdsGE pi_pos] at h
    simpa only [sub_zero] using h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h1 := tendsto_integral_cosinePartialSumKernel_oneSided_of_boundedVariationOn pi_pos
    (by linarith [pi_pos] : π < 2 * π) hfirst hL1
  have h2 := tendsto_integral_cosinePartialSumKernel_oneSided_of_boundedVariationOn pi_pos
    (by linarith [pi_pos] : π < 2 * π) href hL2
  have hsum := h1.add h2
  simp only [← add_div] at hsum
  refine hsum.congr fun N => ?_
  let f : ℝ → ℂ := fun t => g t * (cosinePartialSumKernel N t : ℂ)
  have hi : IntervalIntegrable f volume 0 (2 * π) :=
    hc.mul (Complex.continuous_ofReal.comp
      (continuous_cosinePartialSumKernel N)).continuousOn |>.intervalIntegrable_of_Icc
        (by positivity)
  have hmid : π ∈ uIcc (0 : ℝ) (2 * π) := by
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    exact ⟨pi_pos.le, by linarith [pi_pos]⟩
  have hleft : IntervalIntegrable f volume 0 π :=
    hi.mono_set (uIcc_subset_uIcc left_mem_uIcc hmid)
  have hright : IntervalIntegrable f volume π (2 * π) :=
    hi.mono_set (uIcc_subset_uIcc hmid right_mem_uIcc)
  have hrefint := intervalIntegral.integral_comp_sub_left f (2 * π) (a := 0) (b := π)
  have hpi : 2 * π - π = π := by ring
  simp only [hpi, sub_zero] at hrefint
  have hrefint' : (∫ u in (0 : ℝ)..π,
      g (2 * π - u) * (cosinePartialSumKernel N u : ℂ)) = ∫ t in π..2 * π, f t := by
    convert hrefint using 1
    congr 1
    ext u
    dsimp only [f]
    have hu : 2 * π - u = -u + 2 * π := by ring
    rw [hu, cosinePartialSumKernel_add_two_pi, cosinePartialSumKernel_neg]
  rw [← mul_add, hrefint', intervalIntegral.integral_add_adjacent_intervals hleft hright]

/-- At an endpoint, the cosine kernel converges to the average of the two endpoint values. -/
lemma tendsto_integral_cosinePartialSumKernel_zero {g : ℝ → ℂ}
    (hg : AbsolutelyContinuousOnInterval g 0 (2 * π)) :
    Tendsto (fun N : ℕ => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π,
      g t * (cosinePartialSumKernel N t : ℂ)) atTop (𝓝 ((g 0 + g (2 * π)) / 2)) := by
  apply tendsto_integral_cosinePartialSumKernel_zero_of_boundedVariationOn
  · simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)] using hg.boundedVariationOn
  · simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)] using hg.continuousOn

end Real
