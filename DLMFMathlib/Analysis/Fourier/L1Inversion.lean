/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Fourier.Pairing
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Almost-everywhere Fourier inversion and integral pairings on `L¹`

When a function and its Fourier transform are integrable, inversion holds almost
everywhere, without continuity of the original representative. Testing against smooth
compactly supported functions reduces this to Mathlib's inversion for Schwartz functions.
The resulting pairing requires integrability of only one of the Fourier transforms.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff

namespace Real

/-- Fourier inversion holds almost everywhere when both the function and its
Fourier transform are integrable. -/
theorem ae_fourierInv_fourier_eq {f : ℝ → ℂ} (hf : Integrable f)
    (hF : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) =ᵐ[volume] f := by
  have hc : Continuous (𝓕⁻ (𝓕 f)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF.comp_neg
  apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable hf.locallyIntegrable
  intro φ hφ hφc
  have hψc : HasCompactSupport (fun x => (φ x : ℂ)) :=
    hφc.comp_left (g := Complex.ofReal) rfl
  have hψd : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) := by
    change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ)
    exact Complex.ofRealCLM.contDiff.comp hφ
  let ψ : 𝓢(ℝ, ℂ) := hψc.toSchwartzMap hψd
  have hψ (x : ℝ) : ψ x = (φ x : ℂ) := rfl
  have h₁ := integral_fourierInv_mul_eq_flip hF ψ.integrable
  have h₂ := integral_fourier_mul_eq_flip hf (𝓕⁻ ψ).integrable
  have hinv : 𝓕 ((𝓕⁻ ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = (ψ : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  rw [← SchwartzMap.fourierInv_coe] at h₁
  rw [hinv] at h₂
  have h := h₁.trans h₂
  simpa only [hψ, Complex.real_smul, mul_comm] using h

/-- The bilinear Parseval identity for integrable functions, assuming the Fourier
transform of the second function is integrable. -/
theorem integral_mul_eq_integral_fourier_neg_mul {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hG : Integrable (𝓕 g)) :
    (∫ x, f x * g x) = ∫ t, 𝓕 f (-t) * 𝓕 g t := by
  calc
    (∫ x, f x * g x) = ∫ x, 𝓕⁻ (𝓕 g) x * f x := by
      apply integral_congr_ae
      filter_upwards [ae_fourierInv_fourier_eq hg hG] with x hx
      rw [hx, mul_comm]
    _ = ∫ t, 𝓕 g t * 𝓕⁻ f t := integral_fourierInv_mul_eq_flip hG hf
    _ = _ := by simp only [Real.fourierInv_eq_fourier_neg, mul_comm]

/-- The bilinear Parseval identity needs absolute integrability of either Fourier
transform, in addition to integrability of both original functions. -/
theorem integral_mul_eq_integral_fourier_neg_mul_of_or {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hF : Integrable (𝓕 g) ∨ Integrable (𝓕 f)) :
    (∫ x, f x * g x) = ∫ t, 𝓕 f (-t) * 𝓕 g t := by
  rcases hF with hG | hF
  · exact integral_mul_eq_integral_fourier_neg_mul hf hg hG
  · have h := integral_mul_eq_integral_fourier_neg_mul hg hf hF
    have hn := integral_neg_eq_self (fun t => 𝓕 f (-t) * 𝓕 g t) volume
    calc
      (∫ x, f x * g x) = ∫ t, 𝓕 f t * 𝓕 g (-t) := by
        simpa only [mul_comm] using h
      _ = _ := by simpa only [neg_neg] using hn

end Real
