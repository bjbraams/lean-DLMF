/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.PrincipalValue
public import DLMFMathlib.Analysis.Complex.BarnesResidue
public import DLMFMathlib.Analysis.Complex.ParameterContinuity
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Boundary limits of Cauchy integrals

Subtracting the value at an interior point gives an integrable difference quotient.
Dominated convergence then gives the regular part of a boundary limit, while the
constant kernel contributes the imaginary jump. These formulas support indented
contour representations such as DLMF 8.6.9. Positive-power substitutions preserve the
principal value because their two excision widths have ratio tending to one. An integrable
density also defines a holomorphic quadratic Cauchy transform on the right half-plane.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

namespace Complex

/-- Moving a real denominator off the real axis increases its norm. -/
theorem abs_le_norm_add_mul_I (t η : ℝ) : |t| ≤ ‖(t : ℂ) + η * I‖ := by
  simpa using abs_re_le_norm ((t : ℂ) + η * I)

/-- A real denominator shifted by a nonzero imaginary part never vanishes. -/
theorem ofReal_add_mul_I_ne_zero_of_im_ne_zero {η : ℝ} (hη : η ≠ 0) (t : ℝ) :
    (t : ℂ) + η * I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  exact hη hi

/-- The constant Cauchy kernel on a symmetric interval is an arctangent. -/
theorem integral_horizontal_inv_add_mul_I {η : ℝ} (hη : η ≠ 0) (r : ℝ) :
    (∫ t : ℝ in -r..r, ((t : ℂ) + η * I)⁻¹) =
      -2 * I * (Real.arctan (r / η) : ℂ) := by
  have he (t : ℝ) : ((t : ℂ) + η * I)⁻¹ =
      -I * ((η : ℂ) + (-t : ℝ) * I)⁻¹ := by
    rw [show (t : ℂ) + η * I = I * ((η : ℂ) + (-t : ℝ) * I) by
      push_cast
      ring_nf
      simp [I_sq], mul_inv, inv_I]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hn := intervalIntegral.integral_comp_neg
    (fun t : ℝ => ((η : ℂ) + t * I)⁻¹) (a := -r) (b := r)
  rw [neg_neg] at hn
  rw [hn, BarnesResidue.integral_inv hη]
  ring

/-- The constant Cauchy kernel approaches the upper boundary value `-πi`. -/
theorem tendsto_integral_inv_add_mul_I {r : ℝ} (hr : 0 < r) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in -r..r, ((t : ℂ) + η * I)⁻¹)
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ) * I)) := by
  have ht : Tendsto (fun η : ℝ => r / η) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hr
  have ha : Tendsto (fun η : ℝ => Real.arctan (r / η)) (𝓝[>] 0)
      (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp ht
  have hc := (continuous_ofReal.continuousAt.tendsto.comp ha).const_mul (-2 * I)
  have he : -2 * I * ((Real.pi / 2 : ℝ) : ℂ) = -(Real.pi : ℂ) * I := by
    push_cast
    ring
  rw [he] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (integral_horizontal_inv_add_mul_I (ne_of_gt hη) r).symm

end Complex

namespace MeasureTheory

/-- The regular part of a Cauchy integral converges by domination with the difference
quotient at its real boundary point. -/
theorem tendsto_intervalIntegral_sub_div_add_mul_I {f : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : IntegrableOn f (Icc (-r) r)) (hd : DifferentiableAt ℝ f 0) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in -r..r,
        (f t - f 0) / ((t : ℂ) + η * I)) (𝓝 0)
      (𝓝 (∫ t : ℝ in -r..r, (f t - f 0) / (t : ℂ))) := by
  have hq : IntegrableOn (fun t : ℝ => (f t - f 0) / (t : ℂ)) (Icc (-r) r) := by
    simpa only [ofReal_zero, sub_zero, ← sub_div] using
      pv_integrableOn_sub_of_differentiableAt hf hd
  have hqi : IntervalIntegrable (fun t : ℝ => (f t - f 0) / (t : ℂ)) volume (-r) r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hq
  have hfi : IntervalIntegrable f volume (-r) r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hf
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t => ‖(f t - f 0) / (t : ℂ)‖)
  · exact Eventually.of_forall fun η => by
      have hc : Measurable (fun t : ℝ => ((t : ℂ) + η * I)⁻¹) := by fun_prop
      simpa only [div_eq_mul_inv, uIoc_of_le (show -r ≤ r by linarith),
        Pi.mul_apply] using!
        (hfi.sub (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f 0)
          volume (-r) r)).aestronglyMeasurable.mul hc.aestronglyMeasurable
  · exact Eventually.of_forall fun η => ae_of_all _ fun t _ => by
      by_cases ht : t = 0
      · simp [ht]
      · rw [norm_div, norm_div, norm_real, Real.norm_eq_abs]
        exact div_le_div_of_nonneg_left (norm_nonneg _)
          (abs_pos.mpr ht) (Complex.abs_le_norm_add_mul_I t η)
  · exact hqi.norm
  · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht _
    have hden : Tendsto (fun η : ℝ => (t : ℂ) + η * I) (𝓝 0) (𝓝 (t : ℂ)) := by
      have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝 0) (𝓝 0) := by
        simpa only [ofReal_zero] using
          (continuous_ofReal.tendsto (0 : ℝ))
      simpa only [zero_mul, add_zero] using
        (tendsto_const_nhds (x := (t : ℂ))).add (hη.mul_const I)
    exact tendsto_const_nhds.div hden (ofReal_ne_zero.mpr ht)

/-- The upper boundary value of a Cauchy integral on a symmetric interval is its
regularized real integral minus `πi` times the value at the center. -/
theorem tendsto_intervalIntegral_div_add_mul_I {f : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : IntegrableOn f (Icc (-r) r)) (hd : DifferentiableAt ℝ f 0) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in -r..r, f t / ((t : ℂ) + η * I)) (𝓝[>] 0)
      (𝓝 ((∫ t : ℝ in -r..r, (f t - f 0) / (t : ℂ)) -
        (Real.pi : ℂ) * I * f 0)) := by
  have h := ((tendsto_intervalIntegral_sub_div_add_mul_I hr hf hd).mono_left
    nhdsWithin_le_nhds).add
    ((Complex.tendsto_integral_inv_add_mul_I hr).const_mul (f 0))
  have he : (∫ t : ℝ in -r..r, (f t - f 0) / (t : ℂ)) +
      f 0 * (-(Real.pi : ℂ) * I) =
      (∫ t : ℝ in -r..r, (f t - f 0) / (t : ℂ)) - (Real.pi : ℂ) * I * f 0 := by ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hc : Continuous (fun t : ℝ => ((t : ℂ) + η * I)⁻¹) :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + η * I).inv₀
      (Complex.ofReal_add_mul_I_ne_zero_of_im_ne_zero (ne_of_gt hη))
  have hfi : IntervalIntegrable f volume (-r) r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hf
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  · simpa only [div_eq_mul_inv] using
      (hfi.sub (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f 0)
        volume (-r) r)).mul_continuousOn hc.continuousOn
  · exact (hc.intervalIntegrable _ _).const_mul (f 0)

end MeasureTheory


namespace Complex

/-- The constant Cauchy kernel has jump `-επi` when approached with imaginary sign `ε`. -/
theorem tendsto_integral_inv_add_sign_mul_I {r ε : ℝ} (hr : 0 < r)
    (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in -r..r, ((t : ℂ) + (ε * η : ℝ) * I)⁻¹)
      (𝓝[>] 0) (𝓝 (-(ε : ℂ) * Real.pi * I)) := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have ht : Tendsto (fun η : ℝ => r / η) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hr
  have ha : Tendsto (fun η : ℝ => Real.arctan (r / η)) (𝓝[>] 0)
      (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp ht
  have hl := (continuous_ofReal.continuousAt.tendsto.comp ha).const_mul (-2 * I * ε)
  have he : (-2 * I * (ε : ℂ)) * ((Real.pi / 2 : ℝ) : ℂ) =
      -(ε : ℂ) * Real.pi * I := by push_cast; ring
  rw [he] at hl
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [integral_horizontal_inv_add_mul_I (mul_ne_zero hε0 (ne_of_gt hη))]
  have har : Real.arctan (r / (ε * η)) = ε * Real.arctan (r / η) := by
    rcases hε with rfl | rfl <;> simp [div_neg, Real.arctan_neg]
  rw [har, ofReal_mul]
  dsimp only [Function.comp_def]
  ring

end Complex

namespace MeasureTheory

/-- Either boundary value of a Cauchy integral on a symmetric interval is its regular
part minus `επi` times the value at the center. -/
theorem tendsto_intervalIntegral_div_add_sign_mul_I {f : ℝ → ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : ε = 1 ∨ ε = -1)
    (hf : IntegrableOn f (Icc (-r) r)) (hd : DifferentiableAt ℝ f 0) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in -r..r, f t / ((t : ℂ) + (ε * η : ℝ) * I))
      (𝓝[>] 0) (𝓝 ((∫ t : ℝ in -r..r, (f t - f 0) / (t : ℂ)) -
        (ε : ℂ) * Real.pi * I * f 0)) := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hη : Tendsto (fun η : ℝ => ε * η) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using hi.const_mul ε
  have h := ((tendsto_intervalIntegral_sub_div_add_mul_I hr hf hd).comp hη).add
    ((Complex.tendsto_integral_inv_add_sign_mul_I hr hε).const_mul (f 0))
  have he : (∫ t : ℝ in -r..r, (f t - f 0) / (t : ℂ)) +
      f 0 * (-(ε : ℂ) * Real.pi * I) =
      (∫ t : ℝ in -r..r, (f t - f 0) / (t : ℂ)) -
        (ε : ℂ) * Real.pi * I * f 0 := by ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hc : Continuous (fun t : ℝ => ((t : ℂ) + (ε * η : ℝ) * I)⁻¹) :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (ε * η : ℝ) * I).inv₀
      (Complex.ofReal_add_mul_I_ne_zero_of_im_ne_zero (mul_ne_zero hε0 (ne_of_gt hη)))
  have hfi : IntervalIntegrable f volume (-r) r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hf
  dsimp only [Function.comp_def]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  · simpa only [div_eq_mul_inv] using
      (hfi.sub (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f 0)
        volume (-r) r)).mul_continuousOn hc.continuousOn
  · exact (hc.intervalIntegrable _ _).const_mul (f 0)

end MeasureTheory


namespace Complex

/-- On a real half-line separated from `c`, a Cauchy kernel has a uniform inverse-distance
bound, independently of its imaginary displacement. -/
theorem norm_div_sub_add_mul_I_le {c d t : ℝ} (hcd : c < d) (ht : d ≤ t)
    (v : ℂ) (η : ℝ) :
    ‖v / ((t : ℂ) - c + η * I)‖ ≤ ‖v‖ / (d - c) := by
  rw [norm_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hcd)
  calc d - c ≤ |t - c| := by rw [abs_of_pos (by linarith)]; linarith
    _ ≤ ‖(t : ℂ) - c + η * I‖ := by
      simpa only [ofReal_sub] using abs_le_norm_add_mul_I (t - c) η

end Complex

namespace MeasureTheory

/-- An integrable function remains integrable after division by a Cauchy kernel whose
real pole is separated from the integration half-line. -/
theorem integrableOn_Ioi_div_sub_add_mul_I {f : ℝ → ℂ} {c d : ℝ} (hcd : c < d)
    (hf : IntegrableOn f (Ioi d)) (η : ℝ) :
    IntegrableOn (fun t : ℝ => f t / ((t : ℂ) - c + η * I)) (Ioi d) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => f t / ((t : ℂ) - c + η * I))
      (volume.restrict (Ioi d)) := by
    have hi : Measurable (fun t : ℝ => ((t : ℂ) - c + η * I)⁻¹) := by fun_prop
    simpa only [div_eq_mul_inv, Pi.mul_apply] using! hf.aestronglyMeasurable.mul
      hi.aestronglyMeasurable
  refine (hf.norm.div_const (d - c)).mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact Complex.norm_div_sub_add_mul_I_le hcd (show d ≤ t from ht.le) (f t) η

/-- Away from its real pole, a Cauchy integral tends to the integral with the real
kernel, from either side of the boundary. -/
theorem tendsto_integral_Ioi_div_sub_add_mul_I {f : ℝ → ℂ} {c d : ℝ} (hcd : c < d)
    (hf : IntegrableOn f (Ioi d)) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in Ioi d, f t / ((t : ℂ) - c + η * I)) (𝓝 0)
      (𝓝 (∫ t : ℝ in Ioi d, f t / ((t : ℂ) - c))) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun t => ‖f t‖ / (d - c))
  · exact Eventually.of_forall fun η =>
      (integrableOn_Ioi_div_sub_add_mul_I hcd hf η).aestronglyMeasurable
  · exact Eventually.of_forall fun η => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Complex.norm_div_sub_add_mul_I_le hcd (show d ≤ t from ht.le) (f t) η
  · exact hf.norm.div_const (d - c)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : (t : ℂ) - c ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (show t ≠ c by linarith [show d < t from ht]))
    have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa only [ofReal_zero] using continuous_ofReal.tendsto (0 : ℝ)
    have hden := (tendsto_const_nhds (x := (t : ℂ) - c)).add (hη.mul_const I)
    simpa only [zero_mul, add_zero, Pi.div_apply] using!
      tendsto_const_nhds.div hden (by simpa only [zero_mul, add_zero] using he)

/-- The two Cauchy boundary values on the positive real axis, with a pole at `c > 0`.
The regular part is the symmetric principal value split at `2c`. -/
theorem tendsto_integral_Ioi_div_sub_add_sign_mul_I {f : ℝ → ℂ} {c ε : ℝ}
    (hc : 0 < c) (hε : ε = 1 ∨ ε = -1) (hf : IntegrableOn f (Ioi 0))
    (hd : DifferentiableAt ℝ f c) :
    Tendsto (fun η : ℝ => ∫ t : ℝ in Ioi 0,
        f t / ((t : ℂ) - c + (ε * η : ℝ) * I)) (𝓝[>] 0)
      (𝓝 ((∫ t : ℝ in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) +
        (∫ t : ℝ in Ioi (2 * c), f t / ((t : ℂ) - c)) -
        (ε : ℂ) * Real.pi * I * f c)) := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hf02 : IntervalIntegrable f volume 0 (2 * c) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
      (hf.mono_set Ioc_subset_Ioi_self)
  have hfsh : IntervalIntegrable (fun t : ℝ => f (t + c)) volume (-c) c := by
    simpa only [zero_sub, show 2 * c - c = c by ring] using hf02.comp_add_right c
  have hdsh : DifferentiableAt ℝ (fun t : ℝ => f (t + c)) 0 := by
    have hd' : DifferentiableAt ℝ f ((0 : ℝ) + c) := by simpa only [zero_add] using hd
    simpa only [Function.comp_def] using
      hd'.comp (0 : ℝ) (show DifferentiableAt ℝ (fun t : ℝ => t + c) 0 from
        differentiableAt_id.add_const c)
  have hsh := tendsto_intervalIntegral_div_add_sign_mul_I hc hε
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp hfsh) hdsh
  have hchange (g : ℝ → ℂ) : (∫ t : ℝ in -c..c, g (t + c)) =
      ∫ t : ℝ in 0..2 * c, g t := by
    simpa only [neg_add_cancel, ← two_mul] using
      intervalIntegral.integral_comp_add_right g c (a := -c) (b := c)
  have hk (η : ℝ) : (∫ t : ℝ in -c..c,
      f (t + c) / ((t : ℂ) + (ε * η : ℝ) * I)) =
      ∫ t : ℝ in 0..2 * c, f t / ((t : ℂ) - c + (ε * η : ℝ) * I) := by
    rw [show (fun t : ℝ => f (t + c) / ((t : ℂ) + (ε * η : ℝ) * I)) =
      (fun t : ℝ => (fun u : ℝ => f u / ((u : ℂ) - c + (ε * η : ℝ) * I)) (t + c)) by
        funext t; congr 1; push_cast; ring]
    simpa only [] using! hchange
      (fun u : ℝ => f u / ((u : ℂ) - c + (ε * η : ℝ) * I))
  have hq : (∫ t : ℝ in -c..c, (f (t + c) - f c) / (t : ℂ)) =
      ∫ t : ℝ in 0..2 * c, (f t - f c) / ((t : ℂ) - c) := by
    rw [show (fun t : ℝ => (f (t + c) - f c) / (t : ℂ)) =
      (fun t : ℝ => (fun u : ℝ => (f u - f c) / ((u : ℂ) - c)) (t + c)) by
        funext t; congr 1; push_cast; ring]
    simpa only [] using! hchange
      (fun u : ℝ => (f u - f c) / ((u : ℂ) - c))
  have hcompact : Tendsto (fun η : ℝ => ∫ t : ℝ in 0..2 * c,
      f t / ((t : ℂ) - c + (ε * η : ℝ) * I)) (𝓝[>] 0)
      (𝓝 ((∫ t : ℝ in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) -
        (ε : ℂ) * Real.pi * I * f c)) := by
    simpa only [zero_add, hk, hq] using hsh
  have hft : IntegrableOn f (Ioi (2 * c)) :=
    hf.mono_set (Ioi_subset_Ioi (by linarith))
  have hη : Tendsto (fun η : ℝ => ε * η) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using hi.const_mul ε
  have htail := (tendsto_integral_Ioi_div_sub_add_mul_I (c := c) (by linarith) hft).comp hη
  have h := hcompact.add htail
  have he : ((∫ t : ℝ in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) -
      (ε : ℂ) * Real.pi * I * f c) + (∫ t : ℝ in Ioi (2 * c), f t / ((t : ℂ) - c)) =
      (∫ t : ℝ in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) +
        (∫ t : ℝ in Ioi (2 * c), f t / ((t : ℂ) - c)) -
        (ε : ℂ) * Real.pi * I * f c := by ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  dsimp only [Function.comp_def]
  have hcden : Continuous (fun t : ℝ => ((t : ℂ) - c + (ε * η : ℝ) * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t
    simpa only [ofReal_sub] using Complex.ofReal_add_mul_I_ne_zero_of_im_ne_zero
      (mul_ne_zero hε0 (ne_of_gt hη)) (t - c)
  have hci : IntegrableOn (fun t : ℝ => f t / ((t : ℂ) - c + (ε * η : ℝ) * I))
      (Ioc 0 (2 * c)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
    simpa only [div_eq_mul_inv] using hf02.mul_continuousOn hcden.continuousOn
  have hti := integrableOn_Ioi_div_sub_add_mul_I (c := c) (by linarith) hft (ε * η)
  have hdisj : Disjoint (Ioc (0 : ℝ) (2 * c)) (Ioi (2 * c)) :=
    disjoint_left.mpr fun _ ht ht' => not_lt_of_ge ht.2 ht'
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 * c by linarith),
    setIntegral_union hdisj
      measurableSet_Ioi hci hti, ← intervalIntegral.integral_of_le (show 0 ≤ 2 * c by linarith)]

end MeasureTheory


namespace Complex

/-- The exponential difference quotient at the real point one, with its removable value. -/
def exponentialDifferenceQuotient (z : ℂ) (t : ℝ) : ℂ :=
  exp (-z) * dslope (fun u : ℂ => exp (-z*u)) 0 ((t:ℂ)-1)

/-- The removable exponential difference quotient is jointly continuous. -/
theorem continuous_exponentialDifferenceQuotient :
    Continuous (fun p : ℂ × ℝ => exponentialDifferenceQuotient p.1 p.2) := by
  have h := continuousOn_dslope_param (s := (univ : Set ℂ)) isOpen_univ
    (f := fun z u : ℂ => exp (-z*u)) (by fun_prop)
    (fun z _ => by fun_prop) 0
  have hc : Continuous (fun p : ℂ × ℂ => dslope (fun u : ℂ => exp (-p.1*u)) 0 p.2) := by
    exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using h)
  exact (by fun_prop : Continuous (fun p : ℂ × ℝ => exp (-p.1))).mul
    (hc.comp (show Continuous (fun p : ℂ × ℝ => (p.1, (p.2:ℂ)-1)) by fun_prop))

/-- Away from one, the removable quotient agrees with the ordinary exponential quotient. -/
theorem exponentialDifferenceQuotient_eq {t : ℝ} (ht : t ≠ 1) (z : ℂ) :
    exponentialDifferenceQuotient z t = (exp (-z*t)-exp (-z))/((t:ℂ)-1) := by
  have htc : (t:ℂ)-1 ≠ 0 := by exact_mod_cast sub_ne_zero.mpr ht
  have he : exp (-z)*exp (-z*((t:ℂ)-1)) = exp (-z*t) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold exponentialDifferenceQuotient
  rw [dslope_of_ne _ htc, slope_def_field]
  simp only [mul_zero, exp_zero, sub_zero]
  field_simp
  simp only [neg_mul] at he ⊢
  linear_combination he

end Complex

namespace Complex

/-- The approach `-x + iεxη` to the negative axis for real parameters; `ε = ±1` selects the side. -/
def negativeAxisApproach (x ε η : ℝ) : ℂ :=
  -(x:ℂ)+(ε*x*η:ℝ)*I

/-- The signed imaginary approach tends to its point on the negative real axis. -/
theorem tendsto_negativeAxisApproach (x ε : ℝ) :
    Tendsto (negativeAxisApproach x ε) (𝓝[>] (0:ℝ)) (𝓝 (-(x:ℂ))) := by
  have hc : Continuous (negativeAxisApproach x ε) := by unfold negativeAxisApproach; fun_prop
  simpa [negativeAxisApproach] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The logarithm approaches the signed branch value at a negative real argument. -/
theorem tendsto_log_negativeAxisApproach {x ε : ℝ} (hx : 0 < x) (hε : ε=1 ∨ ε = -1) :
    Tendsto (fun η : ℝ => log (negativeAxisApproach x ε η)) (𝓝[>] (0:ℝ))
      (𝓝 (log (x:ℂ)+(ε:ℂ)*Real.pi*I)) := by
  rcases hε with rfl | rfl
  · have hq : Tendsto (negativeAxisApproach x 1) (𝓝[>] (0:ℝ))
        (𝓝[{z : ℂ | 0 ≤ z.im}] (-(x:ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_negativeAxisApproach x 1, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with η hη
      have hη : 0 < η := hη
      simp only [negativeAxisApproach, neg_im, ofReal_im, neg_zero, add_im, mul_im,
        ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, zero_add]
      positivity
    have hl := (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := -(x:ℂ)) (by simp; linarith) (by simp)).comp hq
    simpa [Function.comp_def, Complex.norm_real, abs_of_pos hx, ← ofReal_log hx.le] using hl
  · have hq : Tendsto (negativeAxisApproach x (-1)) (𝓝[>] (0:ℝ))
        (𝓝[{z : ℂ | z.im < 0}] (-(x:ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_negativeAxisApproach x (-1), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with η hη
      have hη : 0 < η := hη
      simp only [negativeAxisApproach, neg_im, ofReal_im, neg_zero, add_im, mul_im,
        ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, zero_add, neg_one_mul]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hx) hη
    have hl := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (z := -(x:ℂ)) (by simp; linarith) (by simp)).comp hq
    simpa [Function.comp_def, Complex.norm_real, abs_of_pos hx,
      ← ofReal_log hx.le, sub_eq_add_neg] using hl

/-- A signed approach with positive distance and height lies in the principal slit plane. -/
theorem negativeAxisApproach_mem_slitPlane {x ε η : ℝ} (hx : 0<x)
    (hε : ε=1 ∨ ε = -1) (hη : 0<η) : negativeAxisApproach x ε η ∈ slitPlane := by
  right
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  simpa [negativeAxisApproach] using mul_ne_zero (mul_ne_zero hε0 hx.ne') hη.ne'

/-- Principal powers approach the signed boundary value at a negative real argument. -/
theorem tendsto_cpow_negativeAxisApproach {x ε : ℝ} (hx : 0 < x)
    (hε : ε = 1 ∨ ε = -1) (p : ℂ) :
    Tendsto (fun η : ℝ => negativeAxisApproach x ε η ^ p) (𝓝[>] 0)
      (𝓝 ((x : ℂ) ^ p * exp ((ε : ℂ) * Real.pi * I * p))) := by
  have h := ((tendsto_log_negativeAxisApproach hx hε).mul_const p).cexp
  rw [add_mul, Complex.exp_add, ← Complex.cpow_def_of_ne_zero
    (ofReal_ne_zero.mpr hx.ne')] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [Complex.cpow_def_of_ne_zero (slitPlane_ne_zero
    (negativeAxisApproach_mem_slitPlane hx hε hη))]

/-- Positive real scaling puts the Gamma Cauchy kernel at a pole of real part one. -/
theorem integral_cpow_mul_exp_neg_div_negativeAxisApproach (a : ℂ) {x : ℝ} (hx : 0<x) (ε η : ℝ) :
    (∫ t : ℝ in Ioi 0, (t:ℂ)^a*exp (-(t:ℂ))/(negativeAxisApproach x ε η+t)) =
      (x:ℂ)^a * ∫ t : ℝ in Ioi 0,
        (t:ℂ)^a*exp (-(x:ℂ)*t)/((t:ℂ)-1+(ε*η:ℝ)*I) := by
  let F : ℝ → ℂ := fun t => (t:ℂ)^a*exp (-(t:ℂ))/(negativeAxisApproach x ε η+t)
  have hs := integral_comp_mul_left_Ioi' F 0 hx
  rw [mul_zero, Complex.real_smul] at hs
  rw [← hs, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0<t := ht
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hp : ((x*t:ℝ):ℂ)^a = (x:ℂ)^a*(t:ℂ)^a :=
    by simpa only [ofReal_mul] using Complex.mul_cpow_ofReal_nonneg hx.le ht0.le a
  have hd : negativeAxisApproach x ε η+((x*t:ℝ):ℂ) =
      (x:ℂ)*((t:ℂ)-1+(ε*η:ℝ)*I) := by unfold negativeAxisApproach; push_cast; ring
  dsimp only [F]
  rw [hp, hd]
  push_cast
  simp only [neg_mul]
  rw [← mul_div_assoc, mul_div_mul_left _ _ hxc]
  ring

end Complex

/-- A differentiable change of coordinate gives asymptotically equal excision widths. -/
theorem HasDerivAt.tendsto_left_right_increment_ratio {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hd : d ≠ 0) :
    Tendsto (fun ε : ℝ => (f x - f (x - ε)) / (f (x + ε) - f x))
      (𝓝[>] 0) (𝓝 1) := by
  have hleft : HasDerivAt (fun ε : ℝ => f x - f (x - ε)) d 0 := by
    have hf' : HasDerivAt f d (x - (0 : ℝ)) := by simpa using hf
    have h := (hasDerivAt_const (0 : ℝ) (f x)).sub
      (hf'.comp 0 ((hasDerivAt_const (0 : ℝ) x).sub (hasDerivAt_id 0)))
    convert h using 1 <;> norm_num [Function.comp_def, Pi.sub_def]
  have hright : HasDerivAt (fun ε : ℝ => f (x + ε) - f x) d 0 := by
    have hf' : HasDerivAt f d (x + (0 : ℝ)) := by simpa using hf
    simpa only [add_zero, Function.comp_def, Pi.add_apply, id_eq, zero_add,
      mul_one] using
      (hf'.comp 0 ((hasDerivAt_const (0 : ℝ) x).add (hasDerivAt_id 0))).sub_const (f x)
  have hL := hleft.tendsto_slope_zero_right
  have hR := hright.tendsto_slope_zero_right
  simp only [zero_add, sub_zero, sub_self, smul_eq_mul] at hL hR
  have h := hL.div hR hd
  rw [div_self hd] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply, add_zero, sub_self, sub_zero]
  rw [mul_div_mul_left _ _ (inv_ne_zero hε0)]

namespace intervalIntegral
/-- Substitution by a positive real power on a compact interval in the nonnegative axis. -/
theorem integral_deriv_rpow_smul_comp_of_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) (g : ℝ → E) :
    (∫ t in a..b, (p * t ^ (p - 1)) • g (t ^ p)) =
      ∫ u in a ^ p..b ^ p, g u := by
  apply integral_deriv_smul_comp_of_deriv_nonneg
  · exact (Real.continuous_rpow_const hp.le).continuousOn
  · intro t ht
    have hmin : 0 ≤ min a b := le_min ha hb
    have ht0 : 0 < t := lt_of_le_of_lt hmin ht.1
    exact Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
  · intro t ht
    exact mul_nonneg hp.le (Real.rpow_nonneg (le_trans (le_min ha hb) ht.1.le) _)
end intervalIntegral

namespace MeasureTheory

/-- Positive-power substitution preserves the finite part of a Cauchy half-line integral. -/
theorem pv_tendsto_rpow_div_sub {p x : ℝ} (hp : 0 < p) (hx : 0 < x)
    {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) (hd : DifferentiableAt ℝ g (x ^ p)) :
    Tendsto (fun ε : ℝ =>
      (∫ t in 0..x - ε, (p * t ^ (p - 1)) • (g (t ^ p) / (↑(t ^ p) - ↑(x ^ p) : ℂ))) +
      ∫ t in Ioi (x + ε), (p * t ^ (p - 1)) • (g (t ^ p) / (↑(t ^ p) - ↑(x ^ p) : ℂ)))
      (𝓝[>] 0)
      (𝓝 ((∫ u in 0..2 * x ^ p, (g u - g (x ^ p)) / ((u : ℂ) - (x ^ p : ℝ))) +
        ∫ u in Ioi (2 * x ^ p), g u / ((u : ℂ) - (x ^ p : ℝ)))) := by
  let c : ℝ := x ^ p
  let F : ℝ → ℂ := fun u => g u / ((u : ℂ) - c)
  have hc : 0 < c := Real.rpow_pos_of_pos hx _
  have h2c : c < 2 * c := by linarith
  have hgi : IntegrableOn g (Icc 0 (2 * c)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
    exact hg.mono_set Ioc_subset_Ioi_self
  have hsub : IntegrableOn (fun t => F t - g c / ((t : ℂ) - c)) (Icc 0 (2 * c)) :=
    pv_integrableOn_sub_of_differentiableAt hgi hd
  have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun ε : ℝ => (x - ε) ^ p) (𝓝[>] 0) (𝓝 c) := by
    simpa only [sub_zero, Function.comp_def, c] using
      (Real.continuous_rpow_const hp.le).continuousAt.tendsto.comp
        (tendsto_const_nhds.sub hi)
  have hright : Tendsto (fun ε : ℝ => (x + ε) ^ p) (𝓝[>] 0) (𝓝 c) := by
    simpa only [add_zero, Function.comp_def, c] using
      (Real.continuous_rpow_const hp.le).continuousAt.tendsto.comp
        (tendsto_const_nhds.add hi)
  have hcut : ∀ᶠ ε : ℝ in 𝓝[>] 0, (x - ε) ^ p < c ∧ c < (x + ε) ^ p := by
    filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεx : ε < x := hε.2
    exact ⟨Real.rpow_lt_rpow (by linarith) (by linarith) hp,
      Real.rpow_lt_rpow hx.le (by linarith) hp⟩
  have hratio :=
    (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).tendsto_left_right_increment_ratio
    (mul_ne_zero hp.ne' (Real.rpow_pos_of_pos hx _).ne')
  have hfinite := pv_tendsto_of_integrableOn_sub_of_tendsto_ratio
    (g c) hc h2c hsub hleft hright hcut hratio
  have hlog : Real.log ((2 * c - c) / (c - 0)) = 0 := by
    rw [show 2 * c - c = c by ring, sub_zero, div_self hc.ne', Real.log_one]
  rw [hlog, Complex.ofReal_zero, mul_zero, add_zero] at hfinite
  have htail := hfinite.add_const (∫ u in Ioi (2 * c), F u)
  have hvalue : (∫ t in 0..2 * c, F t - g c / ((t : ℂ) - c)) +
      (∫ u in Ioi (2 * c), F u) =
      (∫ t in 0..2 * c, (g t - g c) / ((t : ℂ) - c)) +
      (∫ u in Ioi (2 * c), F u) := by
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [F]
    ring
  rw [hvalue] at htail
  refine htail.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hx,
    hright.eventually (Iio_mem_nhds h2c)] with ε hε hvB
  have hv : c < (x + ε) ^ p := Real.rpow_lt_rpow hx.le (by linarith [hε.1]) hp
  have hft : IntegrableOn F (Ioi ((x + ε) ^ p)) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, F] using
      integrableOn_Ioi_div_sub_add_mul_I hv (hg.mono_set (Ioi_subset_Ioi (hc.trans hv).le)) 0
  have hftB : IntegrableOn F (Ioi (2 * c)) :=
    hft.mono_set (Ioi_subset_Ioi hvB.le)
  have hftI : IntegrableOn F (Ioc ((x + ε) ^ p) (2 * c)) :=
    hft.mono_set Ioc_subset_Ioi_self
  have hdis : Disjoint (Ioc ((x + ε) ^ p) (2 * c)) (Ioi (2 * c)) :=
    disjoint_left.mpr fun t ht ht' => not_lt_of_ge ht.2 ht'
  have hsplit : (∫ u in (x + ε) ^ p..2 * c, F u) +
      (∫ u in Ioi (2 * c), F u) = ∫ u in Ioi ((x + ε) ^ p), F u := by
    rw [intervalIntegral.integral_of_le hvB.le, ← setIntegral_union hdis
      measurableSet_Ioi hftI hftB, Ioc_union_Ioi_eq_Ioi hvB.le]
  rw [add_assoc, hsplit]
  have ht0 : 0 ≤ x - ε := by linarith [hε.2]
  rw [intervalIntegral.integral_deriv_rpow_smul_comp_of_nonneg hp (by norm_num) ht0 F,
    Real.zero_rpow hp.ne']
  have htailSub := integral_comp_rpow_Ioi_of_pos' (g := F) hp
    (Real.rpow_nonneg (show 0 ≤ x + ε by linarith [hε.1]) p)
  rw [Real.rpow_rpow_inv (by linarith [hε.1]) hp.ne'] at htailSub
  rw [htailSub]

end MeasureTheory


namespace Complex

/-- A quadratic Cauchy denominator is bounded below by the square of its parameter's real part. -/
lemma sq_re_le_norm_sq_add_sq (z : ℂ) (t : ℝ) : z.re ^ 2 ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ := by
  have he : z ^ 2 + (t : ℂ) ^ 2 = (z + (t : ℂ) * I) * (z - (t : ℂ) * I) := by
    calc _ = z ^ 2 - (t : ℂ) ^ 2 * I ^ 2 := by rw [I_sq]; ring
        _ = _ := by ring
  rw [he, norm_mul]
  calc z.re ^ 2 = |z.re| * |z.re| := by rw [← sq_abs]; ring
    _ ≤ _ := mul_le_mul
      (by simpa using abs_re_le_norm (z + (t : ℂ) * I))
      (by simpa using abs_re_le_norm (z - (t : ℂ) * I)) (abs_nonneg _) (norm_nonneg _)

end Complex

namespace MeasureTheory

/-- An integrable density has a holomorphic quadratic Cauchy transform on the right half-plane. -/
lemma differentiableOn_integral_div_sq_add_sq {μ : Measure ℝ} {g : ℝ → ℂ}
    (hg : Integrable g μ) :
    DifferentiableOn ℂ (fun z => ∫ t, g t / (z ^ 2 + (t : ℂ) ^ 2) ∂μ)
      {z : ℂ | 0 < z.re} := by
  intro z₀ hz₀
  let δ : ℝ := z₀.re / 2
  have hδ : 0 < δ := half_pos hz₀
  have hlocal : ∀ z ∈ Metric.ball z₀ δ, δ ≤ z.re ∧ ‖z‖ ≤ ‖z₀‖ + δ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre := (abs_le.mp ((abs_re_le_norm (z - z₀)).trans hz.le)).1
    simp only [sub_re] at hre
    constructor
    · dsimp only [δ] at *
      linarith
    · calc ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
            have h := norm_add_le (z - z₀) z₀
            rw [sub_add_cancel] at h
            exact h.trans_eq (add_comm _ _)
        _ ≤ _ := add_le_add_right hz.le _
  have hden : ∀ z ∈ Metric.ball z₀ δ, ∀ t : ℝ,
      δ ^ 2 ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ := by
    intro z hz t
    exact (pow_le_pow_left₀ hδ.le (hlocal z hz).1 2).trans (sq_re_le_norm_sq_add_sq z t)
  have hne : ∀ z ∈ Metric.ball z₀ δ, ∀ t : ℝ, z ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
    intro z hz t hn
    have h := hden z hz t
    rw [hn, norm_zero] at h
    have : 0 < δ ^ 2 := sq_pos_of_pos hδ
    linarith
  have hmi (z : ℂ) : AEStronglyMeasurable
      (fun t : ℝ => (z ^ 2 + (t : ℂ) ^ 2)⁻¹) μ := by fun_prop
  have hmd : AEStronglyMeasurable
      (fun t : ℝ => ((z₀ ^ 2 + (t : ℂ) ^ 2) ^ 2)⁻¹) μ := by fun_prop
  have hmd' : AEStronglyMeasurable
      (fun t : ℝ => -(2 * z₀ * g t / (z₀ ^ 2 + (t : ℂ) ^ 2) ^ 2)) μ := by
    simpa only [Pi.neg_def, Pi.mul_def, div_eq_mul_inv] using
      ((hg.aestronglyMeasurable.const_mul (2 * z₀)).mul hmd).neg
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t => g t / (z ^ 2 + (t : ℂ) ^ 2)) μ := by
    intro z
    exact hg.aestronglyMeasurable.mul (hmi z)
  have hint : Integrable (fun t => g t / (z₀ ^ 2 + (t : ℂ) ^ 2)) μ := by
    refine (hg.norm.div_const (δ ^ 2)).mono' (hmeas z₀) ?_
    filter_upwards [] with t
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hδ)
      (hden z₀ (Metric.mem_ball_self hδ) t)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun z t => g t / (z ^ 2 + (t : ℂ) ^ 2))
    (F' := fun z t => -(2 * z * g t / (z ^ 2 + (t : ℂ) ^ 2) ^ 2))
    (bound := fun t => (2 * (‖z₀‖ + δ) / (δ ^ 2) ^ 2) * ‖g t‖)
    (Metric.ball_mem_nhds _ hδ) (Eventually.of_forall hmeas) hint
    hmd'
    ?_ (hg.norm.const_mul _) ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [] with t z hz
    rw [norm_neg, norm_div, norm_mul, norm_mul, norm_pow, norm_ofNat]
    calc
      (2 * ‖z‖ * ‖g t‖) / ‖z ^ 2 + (t : ℂ) ^ 2‖ ^ 2 ≤
          (2 * (‖z₀‖ + δ) * ‖g t‖) / (δ ^ 2) ^ 2 := by
        gcongr
        · exact (hlocal z hz).2
        · exact hden z hz t
      _ = _ := by ring
  · filter_upwards [] with t z hz
    have h := (((hasDerivAt_id z).pow 2).add_const ((t : ℂ) ^ 2)).inv (hne z hz t)
    convert h.const_mul (g t) using 1
    · ext w
      simp only [div_eq_mul_inv, Pi.inv_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring

end MeasureTheory


namespace MeasureTheory

set_option maxHeartbeats 800000 in
/-- Dividing a density by `t+c` splits its Cauchy finite part into the original finite part
and an ordinary Cauchy transform with a pole on the negative axis. -/
lemma cauchy_finitePart_div_add {f : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hf : IntegrableOn f (Ioi 0)) (hd : DifferentiableAt ℝ f c) :
    (∫ t in 0..2 * c,
      (f t / ((t : ℂ) + c) - f c / ((c : ℂ) + c)) / ((t : ℂ) - c)) +
      (∫ t in Ioi (2 * c), (f t / ((t : ℂ) + c)) / ((t : ℂ) - c)) =
    ((∫ t in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) +
      (∫ t in Ioi (2 * c), f t / ((t : ℂ) - c)) -
        ∫ t in Ioi 0, f t / ((t : ℂ) + c)) / (2 * c) := by
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hreg : IntegrableOn (fun t : ℝ => f t / ((t : ℂ) + c)) (Ioi 0) := by
    simpa only [sub_neg_eq_add, ofReal_neg, ofReal_zero, zero_mul, add_zero] using
      integrableOn_Ioi_div_sub_add_mul_I (c := -c) (d := 0) (by linarith) hf 0
  have hfi : IntegrableOn f (Icc 0 (2 * c)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
    exact hf.mono_set Ioc_subset_Ioi_self
  have hdiff : IntervalIntegrable (fun t : ℝ => (f t - f c) / ((t : ℂ) - c))
      volume 0 (2 * c) := by
    have h := pv_integrableOn_sub_of_differentiableAt hfi hd
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le
      (show (0 : ℝ) ≤ 2 * c by linarith)).mpr h
    simpa only [← sub_div] using hi
  have hrI : IntervalIntegrable (fun t : ℝ => f t / ((t : ℂ) + c)) volume 0 (2 * c) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
      (hreg.mono_set Ioc_subset_Ioi_self)
  have htail : IntegrableOn (fun t : ℝ => f t / ((t : ℂ) - c)) (Ioi (2 * c)) := by
    simpa only [ofReal_zero, zero_mul, add_zero] using integrableOn_Ioi_div_sub_add_mul_I
      (c := c) (by linarith : c < 2 * c)
      (hf.mono_set (Ioi_subset_Ioi (by linarith))) 0
  have hrT := hreg.mono_set (Ioi_subset_Ioi (show 0 ≤ 2 * c by linarith))
  have hpoint (t : ℝ) (ht : 0 ≤ t) (htc : t ≠ c) :
      (f t / ((t : ℂ) + c) - f c / ((c : ℂ) + c)) / ((t : ℂ) - c) =
      (((f t - f c) / ((t : ℂ) - c)) - f t / ((t : ℂ) + c)) / (2 * c) := by
    have htne : (t : ℂ) - c ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast htc)
    have htcne : (t : ℂ) + c ≠ 0 := by
      rw [← ofReal_add]
      exact ofReal_ne_zero.mpr (by linarith : t + c ≠ 0)
    field_simp
    ring
  have hcompact : (∫ t in 0..2 * c,
      (f t / ((t : ℂ) + c) - f c / ((c : ℂ) + c)) / ((t : ℂ) - c)) =
      ((∫ t in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) -
        (∫ t in 0..2 * c, f t / ((t : ℂ) + c))) / (2 * c) := by
    rw [← intervalIntegral.integral_sub hdiff hrI, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne c] with t htc ht
    rw [uIoc_of_le (show (0 : ℝ) ≤ 2 * c by linarith)] at ht
    exact hpoint t ht.1.le htc
  have htail' : (∫ t in Ioi (2 * c), (f t / ((t : ℂ) + c)) / ((t : ℂ) - c)) =
      ((∫ t in Ioi (2 * c), f t / ((t : ℂ) - c)) -
        (∫ t in Ioi (2 * c), f t / ((t : ℂ) + c))) / (2 * c) := by
    rw [← integral_sub htail hrT, ← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := by linarith [show 2 * c < t from ht]
    have htne : (t : ℂ) - c ≠ 0 := sub_ne_zero.mpr (by
      exact_mod_cast (show t ≠ c by linarith [show 2 * c < t from ht]))
    have htcne : (t : ℂ) + c ≠ 0 := by
      rw [← ofReal_add]
      exact ofReal_ne_zero.mpr (by linarith : t + c ≠ 0)
    field_simp
    ring
  have hsplit : (∫ t in 0..2 * c, f t / ((t : ℂ) + c)) +
      (∫ t in Ioi (2 * c), f t / ((t : ℂ) + c)) =
      ∫ t in Ioi 0, f t / ((t : ℂ) + c) := by
    have hdis : Disjoint (Ioc (0 : ℝ) (2 * c)) (Ioi (2 * c)) :=
      disjoint_left.mpr fun t ht ht' => not_lt_of_ge ht.2 ht'
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * c by linarith),
      ← setIntegral_union hdis
        measurableSet_Ioi (hreg.mono_set Ioc_subset_Ioi_self) hrT,
      Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 * c by linarith)]
  rw [hcompact, htail', ← hsplit]
  ring

set_option maxHeartbeats 800000 in
/-- Boundary values of the quadratic Cauchy transform are the finite part of the density
`f(t)/(t+c)` and its signed residue. -/
lemma tendsto_integral_Ioi_div_quadratic_sign_mul_I {f : ℝ → ℂ} {c ε : ℝ}
    (hc : 0 < c) (hε : ε = 1 ∨ ε = -1) (hf : IntegrableOn f (Ioi 0))
    (hd : DifferentiableAt ℝ f c) :
    Tendsto (fun η : ℝ => ∫ t in Ioi 0,
      f t / (((η : ℂ) + (ε * c : ℝ) * I) ^ 2 + (t : ℂ) ^ 2)) (𝓝[>] 0)
      (𝓝 (((∫ t in 0..2 * c,
        (f t / ((t : ℂ) + c) - f c / ((c : ℂ) + c)) / ((t : ℂ) - c)) +
          ∫ t in Ioi (2 * c), (f t / ((t : ℂ) + c)) / ((t : ℂ) - c)) -
            (ε : ℂ) * Real.pi * I * (f c / ((c : ℂ) + c)))) := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hi : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hη : Tendsto (fun η : ℝ => -ε * η) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hi.const_mul (-ε)
  have hB := (tendsto_integral_Ioi_div_sub_add_mul_I
    (c := -c) (d := 0) (by linarith) hf).comp hη
  simp only [Function.comp_def, ofReal_neg, sub_neg_eq_add] at hB
  have hA := tendsto_integral_Ioi_div_sub_add_sign_mul_I hc hε hf hd
  have hζ : Tendsto (fun η : ℝ => (η : ℂ) + (ε * c : ℝ) * I) (𝓝[>] 0)
      (𝓝 ((ε * c : ℝ) * I)) := by
    simpa only [ofReal_zero, zero_add] using
      ((continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).add_const
        ((ε * c : ℝ) * I)
  have hpre := (tendsto_const_nhds (x := (ε : ℂ))).div
    (hζ.const_mul (2 * I)) (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (mul_ne_zero (ofReal_ne_zero.mpr (mul_ne_zero hε0 hc.ne')) I_ne_zero))
  have hval : (ε : ℂ) / (2 * I * ((ε * c : ℝ) * I)) = -1 / (2 * c) := by
    rcases hε with rfl | rfl <;> push_cast <;> field_simp <;> simp [I_sq]
  rw [hval] at hpre
  have h := hpre.mul (hB.sub hA)
  have hvalue : (-1 / (2 * (c : ℂ))) *
      ((∫ t in Ioi 0, f t / ((t : ℂ) + c)) -
        (((∫ t in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) +
          ∫ t in Ioi (2 * c), f t / ((t : ℂ) - c)) -
            (ε : ℂ) * Real.pi * I * f c)) =
      ((∫ t in 0..2 * c,
        (f t / ((t : ℂ) + c) - f c / ((c : ℂ) + c)) / ((t : ℂ) - c)) +
          ∫ t in Ioi (2 * c), (f t / ((t : ℂ) + c)) / ((t : ℂ) - c)) -
            (ε : ℂ) * Real.pi * I * (f c / ((c : ℂ) + c)) := by
    rw [cauchy_finitePart_div_add hc hf hd]
    ring
  rw [hvalue] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη0 : 0 < η := hη
  dsimp only [Pi.div_def]
  have hAint : IntegrableOn
      (fun t : ℝ => f t / ((t : ℂ) - c + (ε * η : ℝ) * I)) (Ioi 0) := by
    have hm : AEStronglyMeasurable
        (fun t : ℝ => f t / ((t : ℂ) - c + (ε * η : ℝ) * I))
          (volume.restrict (Ioi 0)) := by
      simpa only [div_eq_mul_inv, Pi.mul_def] using hf.aestronglyMeasurable.mul
        (Measurable.aestronglyMeasurable (by fun_prop : Measurable
          (fun t : ℝ => ((t : ℂ) - c + (ε * η : ℝ) * I)⁻¹)))
    refine (hf.norm.div_const η).mono' hm ?_
    filter_upwards [] with t
    have hnorm : η ≤ ‖(t : ℂ) - c + (ε * η : ℝ) * I‖ := by
      have h' := abs_im_le_norm ((t : ℂ) - c + (ε * η : ℝ) * I)
      rcases hε with rfl | rfl <;> simpa [abs_of_pos hη0] using h'
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hη0 hnorm
  have hBint : IntegrableOn
      (fun t : ℝ => f t / ((t : ℂ) + c + (-ε * η : ℝ) * I)) (Ioi 0) := by
    simpa only [ofReal_neg, sub_neg_eq_add] using
      integrableOn_Ioi_div_sub_add_mul_I (c := -c) (d := 0) (by linarith) hf (-ε * η)
  rw [← integral_sub hBint hAint, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have hAn : (t : ℂ) - c + (ε * η : ℝ) * I ≠ 0 := by
    simpa only [ofReal_sub] using Complex.ofReal_add_mul_I_ne_zero_of_im_ne_zero
      (mul_ne_zero hε0 hη0.ne') (t - c)
  have hBn : (t : ℂ) + c + (-ε * η : ℝ) * I ≠ 0 := by
    simpa only [ofReal_add] using Complex.ofReal_add_mul_I_ne_zero_of_im_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr hε0) hη0.ne') (t + c)
  have hζn : (η : ℂ) + (ε * c : ℝ) * I ≠ 0 :=
    ne_zero_of_re_pos (by simpa using hη0)
  have halg (A B Z Q F e : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hZ : Z ≠ 0)
      (h1 : Q = A * B) (h2 : B - A = 2 * I * e * Z) (he : e ^ 2 = 1) :
      e / (2 * I * Z) * (F / A - F / B) = F / Q := by
    rw [h1, div_sub_div _ _ hA hB]
    field_simp
    calc _ = F * ((B - A) * e) := by ring
      _ = _ := by rw [h2]; linear_combination (2 * I * Z * F) * he
  refine halg _ _ _ _ _ _ hBn hAn hζn ?_ ?_ ?_
  · rcases hε with rfl | rfl <;> push_cast <;> ring_nf <;> simp only [I_sq] <;> ring
  · rcases hε with rfl | rfl <;> push_cast <;> ring_nf <;> simp only [I_sq] <;> ring
  · rcases hε with rfl | rfl <;> norm_num

set_option maxHeartbeats 800000 in
/-- The symmetric principal value of a quadratic real kernel is the negative finite part
of the density divided by `t+c`. -/
lemma pv_tendsto_div_sq_sub_sq {f : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hf : IntegrableOn f (Ioi 0)) (hd : DifferentiableAt ℝ f c) :
    Tendsto (fun ε : ℝ =>
      (∫ t in 0..c - ε, f t / ((c : ℂ) ^ 2 - (t : ℂ) ^ 2)) +
        ∫ t in Ioi (c + ε), f t / ((c : ℂ) ^ 2 - (t : ℂ) ^ 2)) (𝓝[>] 0)
      (𝓝 (-((∫ t in 0..2 * c,
        (f t / ((t : ℂ) + c) - f c / ((c : ℂ) + c)) / ((t : ℂ) - c)) +
          ∫ t in Ioi (2 * c), (f t / ((t : ℂ) + c)) / ((t : ℂ) - c)))) := by
  let g : ℝ → ℂ := fun t => f t / ((t : ℂ) + c)
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [ofReal_neg, sub_neg_eq_add, ofReal_zero, zero_mul, add_zero] using
      integrableOn_Ioi_div_sub_add_mul_I (c := -c) (d := 0) (by linarith) hf 0
  have hgc : (c : ℂ) + c ≠ 0 := by
    rw [← ofReal_add]
    exact ofReal_ne_zero.mpr (by linarith : c + c ≠ 0)
  have hdg : DifferentiableAt ℝ g (c ^ (1 : ℝ)) := by
    rw [Real.rpow_one]
    exact hd.div (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) + c) c) hgc
  have h := pv_tendsto_rpow_div_sub (p := 1) (by norm_num) hc hg hdg
  simp only [Real.rpow_one, sub_self, Real.rpow_zero, mul_one, one_smul] at h
  have hpoint (t : ℝ) : -(g t / ((t : ℂ) - c)) =
      f t / ((c : ℂ) ^ 2 - (t : ℂ) ^ 2) := by
    dsimp only [g]
    rw [div_div, ← div_neg]
    congr 1
    ring
  refine h.neg.congr fun ε => ?_
  rw [neg_add, ← intervalIntegral.integral_neg, ← integral_neg]
  simp_rw [hpoint]

end MeasureTheory

namespace MeasureTheory

/-- Removing an interval around a real pole makes division by its distance integrable. -/
lemma integrableOn_Ioi_cut_div_sub {f : ℝ → ℂ} {c ε : ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => f t / ((t : ℂ) - c))
      {t : ℝ | 0 < t ∧ ε < |t - c|} := by
  have hfi := hf.mono_set (show {t : ℝ | 0 < t ∧ ε < |t - c|} ⊆ Ioi 0 from fun t ht => ht.1)
  refine (hfi.norm.div_const ε).mono' ?_ ?_
  · simpa only [div_eq_mul_inv, Pi.mul_apply] using! hfi.aestronglyMeasurable.mul
      (by fun_prop : Measurable (fun t : ℝ => ((t : ℂ) - c)⁻¹)).aestronglyMeasurable
  · have hm : MeasurableSet {t : ℝ | 0 < t ∧ ε < |t - c|} := by measurability
    filter_upwards [ae_restrict_mem hm] with t ht
    rw [norm_div, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hε ht.2.le

/-- The symmetric Cauchy principal value written as a set integral on the positive half-line. -/
lemma pv_tendsto_setIntegral_Ioi_div_sub {f : ℝ → ℂ} {c : ℝ}
    (hc : 0 < c) (hf : IntegrableOn f (Ioi 0)) (hd : DifferentiableAt ℝ f c) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in {t : ℝ | 0 < t ∧ ε < |t - c|},
        f t / ((t : ℂ) - c)) (𝓝[>] 0)
      (𝓝 ((∫ t : ℝ in 0..2 * c, (f t - f c) / ((t : ℂ) - c)) +
        ∫ t : ℝ in Ioi (2 * c), f t / ((t : ℂ) - c))) := by
  have hp := pv_tendsto_rpow_div_sub (p := 1) (by norm_num) hc hf (by simpa using hd)
  simp only [Real.rpow_one, sub_self, Real.rpow_zero, one_mul, one_smul] at hp
  refine hp.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hc] with ε hε
  have hset : {t : ℝ | 0 < t ∧ ε < |t - c|} = Ioo 0 (c - ε) ∪ Ioi (c + ε) := by
    ext t
    simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi, lt_abs]
    constructor
    · rintro ⟨ht, h | h⟩
      · right; linarith
      · left; constructor <;> linarith
    · rintro (⟨ht0, ht⟩ | ht)
      · exact ⟨ht0, Or.inr (by linarith)⟩
      · exact ⟨by linarith [hε.1], Or.inl (by linarith)⟩
  have hi := integrableOn_Ioi_cut_div_sub (c := c) hf hε.1
  rw [hset] at hi ⊢
  have hdis : Disjoint (Ioo 0 (c - ε)) (Ioi (c + ε)) := by
    apply disjoint_left.mpr
    intro t ht ht'
    linarith [ht.2, show c + ε < t from ht', hε.1]
  rw [setIntegral_union hdis measurableSet_Ioi (hi.mono_set subset_union_left)
    (hi.mono_set subset_union_right), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [hε.2] : 0 ≤ c - ε)]


/-- Excising a shrinking interval from an integrable density preserves its integral. -/
lemma tendsto_setIntegral_Ioi_cut {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) (c : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in {t : ℝ | 0 < t ∧ ε < |t - c|}, f t)
      (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioi 0, f t)) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioi 0,
      ({t : ℝ | ε < |t - c|}.indicator f) t) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ in Ioi 0, f t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun t => ‖f t‖)
    · exact Eventually.of_forall fun ε => hf.aestronglyMeasurable.indicator (by measurability)
    · exact Eventually.of_forall fun ε =>
        Eventually.of_forall fun t => norm_indicator_le_norm_self _ _
    · exact hf.norm
    · have hae : ∀ᵐ t : ℝ, t ≠ c := by
        rw [ae_iff]
        simp
      filter_upwards [ae_restrict_of_ae hae] with t ht
      have hp : 0 < |t - c| := abs_pos.mpr (sub_ne_zero.mpr ht)
      have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < |t - c| :=
        (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hp)
      exact tendsto_const_nhds.congr' (hev.mono fun ε hε => (indicator_of_mem hε f).symm)
  refine hlim.congr fun ε => ?_
  rw [setIntegral_indicator (by measurability)]
  rfl

end MeasureTheory
