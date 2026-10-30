/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Positivity.Finset

/-!
# Integral transforms in DLMF normalization (DLMF §1.14): definitions

DLMF §1.14 defines the Fourier, Fourier cosine and sine, Laplace, Mellin, Hilbert and Stieltjes
transforms. This file gives the definitions in DLMF's normalization, for complex-valued functions
of a real variable.

* `fourierTransform f x = (2π)^{-1/2} ∫ f(t) e^{ixt} dt` (1.14.1). Mathlib's Fourier transform
  `𝓕 f w = ∫ e^{-2πitw} f(t) dt` uses the opposite sign and the frequency `w = -x/(2π)`; the bridge
  `fourierTransform_eq_fourier` proves `fourierTransform f x = (2π)^{-1/2} 𝓕 f (-x/(2π))`.
* `fourierCosTransform`, `fourierSinTransform` (1.14.9, 1.14.10), integrals over `(0, ∞)`.
* `fourierConvolution f g t = (2π)^{-1/2} ∫ f(t - s) g(s) ds` (1.14.5), DLMF's normalized
  convolution; Mathlib's `MeasureTheory.convolution` has no factor `(2π)^{-1/2}`.
* `laplaceTransform f s = ∫₀^∞ e^{-st} f(t) dt` (1.14.17), `IsOfExponentialGrowth` (1.14.18)
  and the Laplace convolution `laplaceConvolution f g t = ∫₀^t f(u) g(t - u) du` (1.14.30).
* The Mellin transform (1.14.32) is Mathlib's `mellin`, the same normalization; only the Mellin
  convolution `mellinConvolution f g x = ∫₀^∞ f(y) g(x/y) dy/y` (1.14.39) is new.
* `hilbertTransform f x = (1/π) P.V.∫ f(t)/(t - x) dt` (1.14.41), as the limit as `ε → 0⁺` of
  the integrals over `|t - x| > ε` (`limUnder`, junk value when the limit does not exist).
  Note DLMF's sign: `t - x` in the denominator, so that the Fourier multiplier is `-i sign x` in
  DLMF's Fourier normalization (1.14.46).
* `stieltjesTransform f s = ∫₀^∞ f(t)/(s + t) dt` (1.14.47).

Lean totalization applies: an integral of a non-integrable function is `0`; all theorems carry
the integrability hypotheses that DLMF leaves implicit.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped FourierTransform

namespace DLMF.AlgebraicAnalytic

/-- DLMF 1.14.1: the Fourier transform `𝓕(f)(x) = (2π)^{-1/2} ∫_{-∞}^{∞} f(t) e^{ixt} dt` of a
complex-valued function on `ℝ`. Totalized: `0` when `t ↦ f(t) e^{ixt}` is not integrable. -/
@[dlmf 1.14.E1]
def fourierTransform (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ∫ t : ℝ, f t * cexp (I * x * t)

/-- DLMF 1.14.9: the Fourier cosine transform `√(2/π) ∫₀^∞ f(t) cos(xt) dt`. -/
@[dlmf 1.14.E9]
def fourierCosTransform (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt (2 / Real.pi) : ℂ) * ∫ t in Ioi (0 : ℝ), f t * (Real.cos (x * t) : ℂ)

/-- DLMF 1.14.10: the Fourier sine transform `√(2/π) ∫₀^∞ f(t) sin(xt) dt`. -/
@[dlmf 1.14.E10]
def fourierSinTransform (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt (2 / Real.pi) : ℂ) * ∫ t in Ioi (0 : ℝ), f t * (Real.sin (x * t) : ℂ)

/-- DLMF 1.14.5: the Fourier convolution `(f * g)(t) = (2π)^{-1/2} ∫ f(t - s) g(s) ds`, with
DLMF's factor `(2π)^{-1/2}` (absent from Mathlib's `MeasureTheory.convolution`). -/
@[dlmf 1.14.E5]
def fourierConvolution (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ∫ s : ℝ, f (t - s) * g s

/-- DLMF 1.14.17: the Laplace transform `𝓛(f)(s) = ∫₀^∞ e^{-st} f(t) dt`, for complex `s`. -/
@[dlmf 1.14.E17]
def laplaceTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-s * t) * f t

/-- DLMF 1.14.18: `f` is of exponential growth with exponent `α`: there is `M` with
`|f(t)| ≤ M e^{αt}` for `0 ≤ t < ∞`. -/
@[dlmf 1.14.E18]
def IsOfExponentialGrowth (f : ℝ → ℂ) (α : ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M * Real.exp (α * t)

/-- DLMF 1.14.30: the Laplace convolution `(f * g)(t) = ∫₀^t f(u) g(t - u) du`. -/
@[dlmf 1.14.E30]
def laplaceConvolution (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..t, f u * g (t - u)

/-- DLMF 1.14.39: the Mellin convolution `(f * g)(x) = ∫₀^∞ f(y) g(x/y) dy/y`. -/
@[dlmf 1.14.E39]
def mellinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), f y * g (x / y) / y

/-- The truncated Hilbert integral `(1/π) ∫_{|t - x| > ε} f(t)/(t - x) dt`, whose limit as
`ε → 0⁺` is the Hilbert transform 1.14.41. -/
def hilbertTruncated (f : ℝ → ℂ) (x ε : ℝ) : ℂ :=
  (Real.pi⁻¹ : ℂ) * ∫ t in {t : ℝ | ε < |t - x|}, f t / (t - x)

/-- DLMF 1.14.41: the Hilbert transform `ℋ(f)(x) = (1/π) P.V.∫ f(t)/(t - x) dt`, the limit as
`ε → 0⁺` of `hilbertTruncated f x ε` (junk value `limUnder` when the limit does not exist).
DLMF states it for real `f`; complex `f` is allowed here. -/
@[dlmf 1.14.E41]
def hilbertTransform (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (hilbertTruncated f x)

/-- DLMF 1.14.47: the Stieltjes transform `𝒮(f)(s) = ∫₀^∞ f(t)/(s + t) dt`, for complex `s`.
DLMF states it for real `f`; complex `f` is allowed here. -/
@[dlmf 1.14.E47]
def stieltjesTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f t / (s + t)

/-- **Bridge to Mathlib's Fourier transform.** DLMF's `𝓕(f)(x)` (1.14.1) is
`(2π)^{-1/2}` times Mathlib's `𝓕 f` at the frequency `-x/(2π)`. -/
theorem fourierTransform_eq_fourier (f : ℝ → ℂ) (x : ℝ) :
    fourierTransform f x = ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * 𝓕 f (-x / (2 * Real.pi)) := by
  rw [fourierTransform, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end DLMF.AlgebraicAnalytic
