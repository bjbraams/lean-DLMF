/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Bilinear pairings of Fourier integrals

The forward and inverse Fourier pairings follow from Mathlib's vector-valued
Fubini theorem `VectorFourier.integral_bilin_fourierIntegral_eq_flip`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace Real

/-- The bilinear Fourier pairing can be interchanged for two integrable functions. -/
theorem integral_fourier_mul_eq_flip {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext
    rfl
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar (by fun_prop) hf hg
  rw [hflip] at h
  simpa [Real.fourier_eq, VectorFourier.fourierIntegral] using h

/-- The inverse Fourier pairing can be interchanged for two integrable functions. -/
theorem integral_fourierInv_mul_eq_flip {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) : (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  rw [integral_fourier_mul_eq_flip hf.comp_neg hg]
  have h := integral_neg_eq_self (fun x : ℝ => f x * 𝓕⁻ g x) volume
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using h

end Real
