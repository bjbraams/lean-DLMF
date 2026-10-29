/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import DLMFMathlib.Analysis.Fourier.Pairing
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Compatibility of the integral and Hilbert-space Fourier transforms

For functions in `L¹ ∩ L²`, the classical Fourier integral represents Mathlib's
unitary Fourier transform on `L²`. The identification follows by testing against
Schwartz functions and using `Lp.fourier_toTemperedDistribution_eq`, followed by
Mathlib's `ae_eq_of_integral_contDiff_smul_eq`. The pairing then specializes
`Lp.inner_fourier_eq`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ComplexConjugate ContDiff

namespace Real

/-- On `L¹ ∩ L²`, the Fourier integral agrees almost everywhere with the unitary
Fourier transform of the `L²` representative. -/
theorem ae_fourier_eq_fourier_toLp {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable
    ((MeasureTheory.Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))).locallyIntegrable
      (by norm_num))
  intro φ hφ hφc
  have hψc : HasCompactSupport (fun x => (φ x : ℂ)) :=
    hφc.comp_left (g := Complex.ofReal) rfl
  have hψd : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) := by
    change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ)
    exact Complex.ofRealCLM.contDiff.comp hφ
  let ψ : 𝓢(ℝ, ℂ) := hψc.toSchwartzMap hψd
  have hψ (x : ℝ) : ψ x = (φ x : ℂ) := rfl
  have ht := congrArg (fun T : 𝓢'(ℝ, ℂ) => T ψ)
    (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at ht
  have hp : (∫ x, (𝓕 ψ) x • (hf2.toLp f) x) =
      ∫ x, f x * 𝓕 (ψ : ℝ → ℂ) x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, mul_comm]
    rfl
  rw [hp] at ht
  have h := (integral_fourier_mul_eq_flip hf ψ.integrable).trans ht
  simp_rw [hψ] at h
  simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using h

/-- The Fourier integral of an integrable square-integrable function is square integrable. -/
theorem memLp_fourier {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (ae_fourier_eq_fourier_toLp hf hf2)).mpr
    (MeasureTheory.Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))

/-- Parseval's pairing for classical Fourier integrals on `L¹ ∩ L²`. -/
theorem integral_fourier_mul_conj_eq {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) :
    (∫ x, 𝓕 f x * conj (𝓕 g x)) = ∫ x, f x * conj (g x) := by
  have h := Lp.inner_fourier_eq (hg2.toLp g) (hf2.toLp f)
  rw [L2.inner_def, L2.inner_def] at h
  have hleft : (∫ x, inner ℂ ((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) x)
      ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x)) =
      ∫ x, 𝓕 f x * conj (𝓕 g x) := by
    apply integral_congr_ae
    filter_upwards [ae_fourier_eq_fourier_toLp hf hf2, ae_fourier_eq_fourier_toLp hg hg2]
      with x hx hy
    simp only [RCLike.inner_apply, ← hx, ← hy]
  have hright : (∫ x, inner ℂ ((hg2.toLp g) x) ((hf2.toLp f) x)) =
      ∫ x, f x * conj (g x) := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x hx hy
    simp only [RCLike.inner_apply, hx, hy]
  rwa [hleft, hright] at h

end Real
