/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.MarcumQ
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Cdf

/-!
# Probability and lower-integral forms of the Marcum functions

Temme, *Special Functions* (1996), Chapter 11, equations (11.61)–(11.63),
pages 298–299. The noncentral chi-squared bridge reuses TauCeti's existing Poisson
mixture and CDF formula; no competing probability measure is defined here.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set ProbabilityTheory
open scoped Real NNReal

namespace DLMF.Statistical

/-- The complementary Poisson mixture is nonnegative.
Temme (11.61)–(11.62), synopsis TEM-11-16. -/
theorem marcumQ_nonneg (μ : ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    0 ≤ marcumQ μ x y := by
  have h := marcumP_add_marcumQ μ hx y
  have hP := marcumP_le_one μ hx y
  linarith

/-- The complementary Poisson mixture is at most one.
Temme (11.61)–(11.62), synopsis TEM-11-16. -/
theorem marcumQ_le_one (μ : ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    marcumQ μ x y ≤ 1 := by
  have h := marcumP_add_marcumQ μ hx y
  have hP := marcumP_nonneg μ hx y
  linarith

/-- At zero noncentrality the upper tail is the central gamma tail.
Temme (11.61), synopsis TEM-11-16. -/
theorem marcumQ_zero_left (μ y : ℝ) :
    marcumQ μ 0 y = 1 - TauCeti.regularizedGamma μ y := by
  have h := marcumP_add_marcumQ μ (le_refl 0) y
  rw [marcumP_zero_left] at h
  linarith

/-- TauCeti's noncentral chi-squared CDF has the source's Marcum parametrization.
Temme (11.61)–(11.63), synopsis TEM-11-16. -/
theorem Real.cdf_noncentralChiSquaredMeasure_eq_marcumP {ν : ℝ} (hν : 0 < ν)
    (Λ : ℝ≥0) (z : ℝ) :
    cdf (TauCeti.Probability.noncentralChiSquaredMeasure ν Λ) z =
      marcumP (ν / 2) (Λ / 2) (z / 2) := by
  rw [TauCeti.Probability.cdf_noncentralChiSquaredMeasure_eq hν, marcumP]
  apply tsum_congr
  intro n
  rw [show (ν + 2 * (n : ℝ)) / 2 = ν / 2 + n by ring]
  simp only [poissonWeight, neg_div]

/-- The full Marcum Bessel density is absolutely integrable at both endpoints.
Temme (11.63), synopsis TEM-11-16. -/
theorem integrableOn_marcumBesselDensity {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (((t / x) ^ ((μ - 1) / 2) *
      _root_.Real.exp (-t - x) : ℝ) : ℂ) *
        DLMF.Bessel.besselI ((μ - 1 : ℝ) : ℂ) (2 * _root_.Real.sqrt (x * t))) (Ioi 0) := by
  sorry

/-- The same Bessel density integrated from zero gives the lower Marcum function.
Temme (11.63), synopsis TEM-11-16. -/
theorem marcumP_eq_integral {μ x y : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hy : 0 ≤ y) :
    (marcumP μ x y : ℂ) = ∫ t in (0 : ℝ)..y,
      (((t / x) ^ ((μ - 1) / 2) * _root_.Real.exp (-t - x) : ℝ) : ℂ) *
        DLMF.Bessel.besselI ((μ - 1 : ℝ) : ℂ) (2 * _root_.Real.sqrt (x * t)) := by
  sorry

end DLMF.Statistical
