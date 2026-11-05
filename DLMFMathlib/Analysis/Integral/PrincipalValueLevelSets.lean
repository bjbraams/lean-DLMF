/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.PrincipalValueExcision
/-!
# Reciprocal level cutoffs and asymmetric principal-value excision

The condition `ε ≤ |1 - (a+c)/(t+c)|` on the positive ray removes an interval
about `a`, with distances `(a+c)ε/(1+ε)` and `(a+c)ε/(1-ε)`. The closed and open
versions of the removed interval give the same Lebesgue integral.

For an integrable kernel, level cutoffs tend to the original integral whenever the zero level
has measure zero. Trigonometric characteristics `1 - α sin²θ` satisfy this condition on the first
quarter-period, and cutting away a positive level makes reciprocal kernels integrable.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace Real
/-- A reciprocal level cutoff is the complement of an explicit open interval. -/
theorem le_abs_one_sub_div_iff {a c t ε : ℝ} (htc : 0 < t + c)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ε ≤ |1 - (a + c) / (t + c)| ↔
      t ≤ a - (a + c) * ε / (1 + ε) ∨ a + (a + c) * ε / (1 - ε) ≤ t := by
  have he : 1 - (a + c) / (t + c) = (t - a) / (t + c) := by field_simp; ring
  have hL : a - (a + c) * ε / (1 + ε) = (a - c * ε) / (1 + ε) := by
    field_simp
    ring
  have hR : a + (a + c) * ε / (1 - ε) = (a + c * ε) / (1 - ε) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos htc, le_div_iff₀ htc, abs_eq_max_neg, le_max_iff, hL, hR]
  constructor
  · rintro (h | h)
    · right
      rw [div_le_iff₀ (by linarith : 0 < 1 - ε)]
      nlinarith
    · left
      rw [le_div_iff₀ (by positivity : 0 < 1 + ε)]
      nlinarith
  · rintro (h | h)
    · right
      rw [le_div_iff₀ (by positivity : 0 < 1 + ε)] at h
      nlinarith
    · left
      rw [div_le_iff₀ (by linarith : 0 < 1 - ε)] at h
      nlinarith

/-- A trigonometric characteristic has at most one zero on the first quarter-period. -/
theorem ae_one_sub_mul_sin_sq_ne_zero_Ioc (α : ℝ) :
    ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (π / 2)), 1 - α * sin θ ^ 2 ≠ 0 := by
  rcases eq_or_ne α 0 with rfl | hα
  · simp
  let Z : Set ℝ := {θ | θ ∈ Icc 0 (π / 2) ∧ 1 - α * sin θ ^ 2 = 0}
  have hZ : Z.Subsingleton := by
    intro θ hθ ψ hψ
    have hsθ : 0 ≤ sin θ := sin_nonneg_of_mem_Icc ⟨hθ.1.1, by linarith [hθ.1.2, pi_pos]⟩
    have hsψ : 0 ≤ sin ψ := sin_nonneg_of_mem_Icc ⟨hψ.1.1, by linarith [hψ.1.2, pi_pos]⟩
    have hsq : sin θ ^ 2 = sin ψ ^ 2 := by
      apply mul_left_cancel₀ hα
      linear_combination -hθ.2 + hψ.2
    have he : sin θ = sin ψ := by nlinarith
    exact strictMonoOn_sin.injOn ⟨by linarith [hθ.1.1, pi_pos], hθ.1.2⟩
      ⟨by linarith [hψ.1.1, pi_pos], hψ.1.2⟩ he
  have hae : ∀ᵐ θ ∂volume, θ ∉ Z := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hZ.countable.measure_zero volume
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hae] with θ hθ hθZ
  intro H
  exact hθZ ⟨Ioc_subset_Icc_self hθ, H⟩

end Real
namespace MeasureTheory
/-- A reciprocal level cutoff integrates over an asymmetrically excised half-line. -/
theorem integral_indicator_one_sub_div_eq_diff_Icc (F : ℝ → ℂ) {a c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    (∫ t in Ioi (0 : ℝ), if ε ≤ |1 - (a + c) / (t + c)| then F t else 0) =
      ∫ t in Ioi (0 : ℝ) \ Icc (a - (a + c) * ε / (1 + ε))
        (a + (a + c) * ε / (1 - ε)), F t := by
  let S : Set ℝ := {t | ε ≤ |1 - (a + c) / (t + c)|}
  have hS : MeasurableSet S := by
    apply measurableSet_le measurable_const
    fun_prop
  change (∫ t in Ioi (0 : ℝ), S.indicator F t) = _
  rw [setIntegral_indicator hS]
  have hset : Ioi (0 : ℝ) ∩ S = Ioi (0 : ℝ) \
      Ioo (a - (a + c) * ε / (1 + ε)) (a + (a + c) * ε / (1 - ε)) := by
    ext t
    simp only [S, mem_inter_iff, mem_Ioi, mem_ofPred_eq, Set.mem_sdiff, mem_Ioo,
      not_and_or, not_lt]
    constructor
    · rintro ⟨ht, he⟩
      exact ⟨ht, (Real.le_abs_one_sub_div_iff (by linarith : 0 < t + c) hε hε1).mp he⟩
    · rintro ⟨ht, he⟩
      exact ⟨ht, (Real.le_abs_one_sub_div_iff (by linarith : 0 < t + c) hε hε1).mpr he⟩
  rw [hset]
  exact setIntegral_congr_set (ae_eq_set_sdiff Filter.EventuallyEq.rfl Ioo_ae_eq_Icc)

/-- Removing vanishing level sets preserves an integral when the zero level has measure zero. -/
theorem tendsto_integral_indicator_abs_ge {μ : Measure ℝ} {g : ℝ → ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (hg : Measurable g) (hne : ∀ᵐ t ∂μ, g t ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ t, if ε ≤ |g t| then f t else 0 ∂μ)
      (𝓝[>] 0) (𝓝 (∫ t, f t ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖) ?_ ?_ hf.norm ?_
  · filter_upwards [] with ε
    have hA : MeasurableSet {t | ε ≤ |g t|} :=
      measurableSet_le measurable_const (continuous_abs.measurable.comp hg)
    have H := hf.aestronglyMeasurable.indicator hA
    convert H using 1
    funext t
    simp only [Set.indicator_apply, mem_ofPred_eq]
  · filter_upwards [] with ε
    filter_upwards [] with t
    split_ifs <;> simp
  · filter_upwards [hne] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_lt_nhds (abs_pos.mpr ht)).filter_mono
      nhdsWithin_le_nhds] with ε hε
    simp only [ite_eq_left hε.le]


/-- Cutting away a positive level of a real denominator gives an integrable reciprocal kernel. -/
theorem integrable_indicator_abs_ge_inv_mul {μ : Measure ℝ} {g : ℝ → ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (hg : Measurable g) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t => if ε ≤ |g t| then ((g t : ℂ))⁻¹ * f t else 0) μ := by
  have hA : MeasurableSet {t | ε ≤ |g t|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hg)
  have hrec : AEStronglyMeasurable (fun t => (g t : ℂ)⁻¹) μ :=
    ((Complex.continuous_ofReal.measurable.comp hg).inv).aestronglyMeasurable
  have hM : AEStronglyMeasurable
      (fun t => if ε ≤ |g t| then (g t : ℂ)⁻¹ * f t else 0) μ := by
    convert (hrec.mul hf.aestronglyMeasurable).indicator hA using 1
    funext t
    simp only [Set.indicator_apply, mem_ofPred_eq, Pi.mul_apply]
  apply (hf.norm.const_mul ε⁻¹).mono' hM
  filter_upwards [] with t
  by_cases ht : ε ≤ |g t|
  · simp only [ite_eq_left ht, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε ht) (norm_nonneg _)
  · simp only [ite_eq_right ht, norm_zero]
    positivity

end MeasureTheory
