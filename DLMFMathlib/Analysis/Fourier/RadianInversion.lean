/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Fourier inversion with radian frequencies

Mathlib normalizes the Fourier kernel by `2π`. This module derives inversion for
`exp(-i⟪x,ξ⟫)` and tracks a positive scalar difference between the chosen measure and
Euclidean volume. Values may lie in any complete complex normed space.

## Main results

* `Real.radianFourierIntegral_inversion`: inversion with Euclidean volume.
* `Real.radianFourierIntegral_inversion_of_volume_eq_smul`: inversion for a measure
  proportional to Euclidean volume.

The proofs adapt Mathlib's `MeasureTheory.Integrable.fourierInv_fourier_eq` using its
Haar-measure scaling formula, without reproving Fourier inversion.
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
public noncomputable section

namespace Real
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
/-- The Fourier integral with radian frequency, against an arbitrary measure. -/
@[expose] noncomputable def radianFourierIntegral (μ : Measure V) (f : V → E) (ξ : V) : E :=
  ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ)) • f x ∂μ
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The integral kernel for radian frequencies. -/
lemma radianFourierIntegral_def (μ : Measure V) (f : V → E) (ξ : V) :
    radianFourierIntegral μ f ξ =
      ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ)) • f x ∂μ := rfl
/-- Mathlib's Fourier transform is the radian transform at frequency `2πξ`. -/
lemma fourier_eq_radianFourierIntegral (f : V → E) (ξ : V) :
    𝓕 f ξ = radianFourierIntegral volume f ((2 * Real.pi) • ξ) := by
  rw [Real.fourier_eq']
  unfold radianFourierIntegral
  congr 1
  funext x
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 2
  push_cast
  ring
/-- Fourier inversion at continuity points, with radian frequencies and Euclidean volume. -/
lemma radianFourierIntegral_inversion [CompleteSpace E] {f : V → E} (hf : Integrable f)
    (hF : Integrable (radianFourierIntegral volume f)) {x : V} (hc : ContinuousAt f x) :
    f x = ((2 * Real.pi)^(Module.finrank ℝ V))⁻¹ •
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) • radianFourierIntegral volume f ξ := by
  have hpos : 0 < 2 * Real.pi := by positivity
  have hFi : Integrable (𝓕 f) := by
    rw [show 𝓕 f = (fun ξ => radianFourierIntegral volume f ((2 * Real.pi) • ξ))
      from funext (fourier_eq_radianFourierIntegral f)]
    exact hF.comp_smul hpos.ne'
  have hh := hf.fourierInv_fourier_eq hFi hc
  rw [Real.fourierInv_eq'] at hh
  simp_rw [fourier_eq_radianFourierIntegral] at hh
  have hs := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure V))
    (fun ξ => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) • radianFourierIntegral volume f ξ)
    (2 * Real.pi) (hR := hpos.le)
  rw [← hs, ← hh]
  congr 1
  funext ξ
  simp only [inner_smul_left, conj_trivial, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 2
  ring
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A positive real scaling of the measure scales its radian Fourier integral. -/
lemma radianFourierIntegral_smul_measure (μ : Measure V) (s : ℝ) (hs : 0 ≤ s)
    (f : V → E) (ξ : V) :
    radianFourierIntegral (ENNReal.ofReal s • μ) f ξ = s • radianFourierIntegral μ f ξ := by
  simp only [radianFourierIntegral, integral_smul_measure, ENNReal.toReal_ofReal hs]
/-- Fourier inversion when Euclidean volume is a positive scalar multiple of the measure. -/
lemma radianFourierIntegral_inversion_of_volume_eq_smul [CompleteSpace E]
    (μ : Measure V) {s : ℝ} (hs : 0 < s)
    (hvol : (volume : Measure V) = ENNReal.ofReal s • μ)
    {f : V → E} (hf : Integrable f μ) (hF : Integrable (radianFourierIntegral μ f) μ)
    {x : V} (hc : ContinuousAt f x) :
    f x = (s ^ 2 / (2 * Real.pi)^(Module.finrank ℝ V)) •
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) • radianFourierIntegral μ f ξ ∂μ := by
  have hfi : Integrable f volume := by
    rw [hvol]
    exact (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mpr hf
  have heq : radianFourierIntegral volume f = fun ξ => s • radianFourierIntegral μ f ξ := by
    funext ξ
    rw [hvol, radianFourierIntegral_smul_measure μ s hs.le]
  have hFi : Integrable (radianFourierIntegral volume f) volume := by
    rw [heq, hvol]
    exact (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mpr
      (hF.smul s)
  rw [radianFourierIntegral_inversion hfi hFi hc, heq, hvol, integral_smul_measure,
    ENNReal.toReal_ofReal hs.le]
  have hswap : (fun ξ => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) •
      (s • radianFourierIntegral μ f ξ)) =
      (fun ξ => s • (Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) •
        radianFourierIntegral μ f ξ)) := by
    funext ξ
    exact smul_comm _ _ _
  rw [hswap, integral_smul, smul_smul, smul_smul]
  congr 1
  ring
end Real
