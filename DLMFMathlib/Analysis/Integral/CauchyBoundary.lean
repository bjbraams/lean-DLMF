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

/-!
# Boundary limits of Cauchy integrals

Subtracting the value at an interior point gives an integrable difference quotient.
Dominated convergence then gives the regular part of a boundary limit, while the
constant kernel contributes the imaginary jump. These formulas support indented
contour representations such as DLMF 8.6.9.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

namespace Complex

/-- Moving a real denominator off the real axis increases its norm. -/
theorem abs_le_norm_add_mul_I (t η : ℝ) : |t| ≤ ‖(t : ℂ) + η * I‖ := by
  simpa using abs_re_le_norm ((t : ℂ) + η * I)

/-- A real denominator shifted by a nonzero imaginary part never vanishes. -/
theorem ofReal_add_mul_I_ne_zero {η : ℝ} (hη : η ≠ 0) (t : ℝ) :
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
      (Complex.ofReal_add_mul_I_ne_zero (ne_of_gt hη))
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
      (Complex.ofReal_add_mul_I_ne_zero (mul_ne_zero hε0 (ne_of_gt hη)))
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
    simpa only [ofReal_sub] using Complex.ofReal_add_mul_I_ne_zero
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
