/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.MellinConvolution
public import DLMFMathlib.Analysis.Fourier.L1Inversion

/-!
# Mellin Parseval identities with weighted `L¹` hypotheses

Logarithmic coordinates transport the bilinear Fourier pairing to the Mellin transform.
Only one Mellin transform needs to be integrable on its vertical line; no square-integrability
assumption on the original functions is required.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set
open scoped FourierTransform

/-- Positive dilation preserves absolute integrability of a Mellin transform on
a fixed vertical line. -/
theorem Complex.VerticalIntegrable.mellin_comp_mul_left {f : ℝ → ℂ} {σ y : ℝ}
    (hf : VerticalIntegrable (mellin f) σ) (hy : 0 < y) :
    VerticalIntegrable (mellin (fun x => f (y * x))) σ := by
  have hc : Continuous (fun t : ℝ => (y : ℂ) ^ (-(σ + t * I))) :=
    (by fun_prop : Continuous (fun t : ℝ => -(σ + t * I))).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hy.ne'))
  have h := hf.bdd_mul (c := y ^ (-σ)) hc.aestronglyMeasurable (by
    filter_upwards [] with t
    rw [norm_cpow_eq_rpow_re_of_pos hy]
    simp)
  simpa only [VerticalIntegrable, _root_.mellin_comp_mul_left _ _ hy, smul_eq_mul] using h

/-- Complex conjugation commutes with the Mellin transform after conjugating the
exponent, since the integration variable is positive real. -/
theorem mellin_conj (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun x => starRingEnd ℂ (f x)) (starRingEnd ℂ s) =
      starRingEnd ℂ (mellin f s) := by
  rw [mellin_eq_integral_exp_mul, mellin_eq_integral_exp_mul, ← integral_conj]
  apply integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, ← Complex.exp_conj, map_neg, conj_ofReal]

/-- The weighted function in logarithmic coordinates has Fourier transform equal
to the Mellin transform on a vertical line, with frequency scaled by `2π`. -/
theorem mellin_vertical_eq_fourier (f : ℝ → ℂ) (σ t : ℝ) :
    mellin f (σ + t * I) =
      𝓕 (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) (t / (2 * Real.pi)) := by
  simp [mellin_eq_fourier]

/-- Absolute Mellin convergence gives integrability of the real weighted function
in logarithmic coordinates. -/
theorem MellinConvergent.integrable_log_weight {f : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f σ) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  simpa only [Complex.real_smul, ofReal_exp, ofReal_mul, ofReal_neg] using
    (mellinConvergent_iff_integrable_exp_mul f σ).mp hf

/-- Mellin Parseval's bilinear identity with absolute convergence on complementary
vertical lines and an integrable transform on either line. -/
theorem integral_mul_eq_mellin_parseval {f g : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f (1 - σ)) (hg : MellinConvergent g σ)
    (hint : VerticalIntegrable (mellin g) σ ∨
      Integrable (fun t : ℝ => mellin f (1 - (σ + t * I)))) :
    (∫ x in Ioi (0 : ℝ), f x * g x) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, mellin f (1 - (σ + t * I)) * mellin g (σ + t * I) := by
  let F : ℝ → ℂ := fun u => Real.exp (-(1 - σ) * u) • f (Real.exp (-u))
  let G : ℝ → ℂ := fun u => Real.exp (-σ * u) • g (Real.exp (-u))
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfm (t : ℝ) : mellin f (1 - (σ + t * I)) = 𝓕 F (-t / (2 * Real.pi)) := by
    rw [show (1 : ℂ) - (σ + t * I) = ((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I by
      push_cast; ring, mellin_vertical_eq_fourier]
  have hgm (t : ℝ) : mellin g (σ + t * I) = 𝓕 G (t / (2 * Real.pi)) :=
    mellin_vertical_eq_fourier g σ t
  have hFG : Integrable (𝓕 G) ∨ Integrable (𝓕 F) := by
    rcases hint with hg' | hf'
    · left
      have h := hg'.comp_mul_right' hπ
      simpa only [VerticalIntegrable, hgm, mul_div_cancel_right₀ _ hπ] using h
    · right
      have h := hf'.comp_mul_right' hπ
      have he : (fun t : ℝ => mellin f (1 -
          (σ + ((t * (2 * Real.pi) : ℝ) : ℂ) * I))) =
          fun t => 𝓕 F (-t) := by
        ext t
        rw [hfm]
        field_simp
      rw [he] at h
      simpa only [neg_neg] using h.comp_neg
  have hfreal : MellinConvergent f ((1 - σ : ℝ) : ℂ) := by simpa using hf
  have hp := Real.integral_mul_eq_integral_fourier_neg_mul_of_or
    hfreal.integrable_log_weight hg.integrable_log_weight hFG
  have hleft : (∫ x in Ioi (0 : ℝ), f x * g x) = ∫ u, F u * G u := by
    have h := mellin_eq_integral_exp_mul (fun x => f x * g x) 1
    simp only [mellin, sub_self, cpow_zero, one_smul] at h
    rw [h]
    apply integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp [F, G]
    rw [ofReal_exp, ofReal_exp]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hleft, hp]
  have h := Measure.integral_comp_mul_right
    (fun t : ℝ => mellin f (1 - (σ + t * I)) * mellin g (σ + t * I)) (2 * Real.pi)
  simp only [hfm, hgm, mul_div_cancel_right₀ _ hπ] at h
  have he (t : ℝ) : -(t * (2 * Real.pi)) / (2 * Real.pi) = -t := by field_simp
  simp only [he, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)),
    Complex.real_smul, ofReal_inv, ofReal_mul, ofReal_ofNat] at h
  simpa only [hfm, hgm, one_div] using h
