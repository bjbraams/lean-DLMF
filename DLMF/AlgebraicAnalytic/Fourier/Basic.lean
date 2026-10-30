/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Fourier coefficients and Lebesgue constants: definitions (DLMF §1.8)

Definitions for DLMF §1.8 (namespace `DLMF.AlgebraicAnalytic`). The functions are complex
valued functions of a real variable, `f : ℝ → ℂ`; a real-valued function is covered through
the coercion `ℝ → ℂ`. Periodicity is a hypothesis of the theorems, not part of the definitions.

* `fourierCosCoeff f n`, `fourierSinCoeff f n` (1.8.2): `a_n = π⁻¹ ∫_{-π}^{π} f(x) cos(nx) dx`,
  `b_n = π⁻¹ ∫_{-π}^{π} f(x) sin(nx) dx`.
* `fourierExpCoeff f n` (1.8.4): `c_n = (2π)⁻¹ ∫_{-π}^{π} f(x) e^{-inx} dx`, `n ∈ ℤ`; it is
  Mathlib's `fourierCoeffOn` on `[-π, π]` (`fourierExpCoeff_eq_fourierCoeffOn` in
  `DLMF.AlgebraicAnalytic.Fourier.Series`).
* `lebesgueConstant n` (1.8.8): `L_n = π⁻¹ ∫_0^π |sin((n + ½)t)| / sin(t/2) dt`.

All integrals are interval integrals, which are `0` for non-integrable integrands (Lean's
totalization); the theorems carry integrability hypotheses where DLMF integrates.
-/

@[expose] public noncomputable section

open Real

namespace DLMF.AlgebraicAnalytic

/-- DLMF 1.8.2 (first formula): the cosine Fourier coefficient
`a_n = π⁻¹ ∫_{-π}^{π} f(x) cos(nx) dx` of `f : ℝ → ℂ`, `n = 0, 1, 2, …`. -/
@[dlmf 1.8.E2]
def fourierCosCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (1 / π : ℂ) * ∫ x in (-π)..π, f x * (Real.cos (n * x) : ℂ)

/-- DLMF 1.8.2 (second formula): the sine Fourier coefficient
`b_n = π⁻¹ ∫_{-π}^{π} f(x) sin(nx) dx` of `f : ℝ → ℂ`, `n = 1, 2, …` (the value at `n = 0`
is `0`). -/
@[dlmf 1.8.E2]
def fourierSinCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (1 / π : ℂ) * ∫ x in (-π)..π, f x * (Real.sin (n * x) : ℂ)

/-- DLMF 1.8.4: the exponential Fourier coefficient
`c_n = (2π)⁻¹ ∫_{-π}^{π} f(x) e^{-inx} dx`, `n ∈ ℤ`. -/
@[dlmf 1.8.E4]
def fourierExpCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ x in (-π)..π, f x * Complex.exp (-(Complex.I * n * x))

/-- DLMF 1.8.8: the Lebesgue constants
`L_n = π⁻¹ ∫_0^π |sin((n + ½)t)| / sin(½t) dt`, `n = 0, 1, …`. The integrand is bounded
(by `2n + 1`) on `(0, π]`, so the integral is a proper Lebesgue integral. -/
@[dlmf 1.8.E8]
def lebesgueConstant (n : ℕ) : ℝ :=
  (1 / π) * ∫ t in (0 : ℝ)..π, |Real.sin ((n + 1 / 2) * t)| / Real.sin (t / 2)

end DLMF.AlgebraicAnalytic
