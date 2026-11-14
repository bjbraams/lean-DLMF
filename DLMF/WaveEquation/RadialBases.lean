/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.SecondKind
public import DLMFMathlib.Analysis.ODE.Wronskian
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Spherical radial bases at positive and zero frequency

Temme, *Special Functions* (1996), §10.2.2, pp. 261–263,
synopsis TEM-10-03. The normalization here is `r^(-1/2) J_(l+1/2)(k r)`
and its Y counterpart. Wronskians retain the radius factor required for
applying the existing generic fundamental-pair theorem.
-/

@[expose] public noncomputable section
open Complex Set
namespace DLMF.WaveEquation

/-- The positive-frequency spherical radial Bessel pair is smooth, solves the
separated equation and has Wronskian `2/(π r²)`, Temme §10.2.2,
synopsis TEM-10-03. -/
theorem spherical_radial_bessel_pair (l : ℕ) {k : ℝ} (hk : 0 < k) :
    let f : ℝ → ℂ := fun r => (r : ℂ) ^ (-1 / 2 : ℂ) *
      Complex.besselJ (l + 1 / 2) (k * r)
    let g : ℝ → ℂ := fun r => (r : ℂ) ^ (-1 / 2 : ℂ) *
      DLMF.Bessel.besselY (l + 1 / 2) (k * r)
    ContDiffOn ℝ 2 f (Ioi 0) ∧ ContDiffOn ℝ 2 g (Ioi 0) ∧ ∀ r : ℝ, 0 < r →
      (r : ℂ) ^ 2 * iteratedDeriv 2 f r + 2 * r * deriv f r +
        ((k * r : ℝ) ^ 2 - (l : ℂ) * (l + 1)) * f r = 0 ∧
      (r : ℂ) ^ 2 * iteratedDeriv 2 g r + 2 * r * deriv g r +
        ((k * r : ℝ) ^ 2 - (l : ℂ) * (l + 1)) * g r = 0 ∧
      ODE.wronskian f g r = 2 / (Real.pi * (r : ℂ) ^ 2) := by
  sorry

/-- At zero frequency the spherical radial basis consists of two powers,
Temme §10.2.2, synopsis TEM-10-03. Its Wronskian is nonzero at every positive
radius, including degree zero. -/
theorem spherical_radial_power_pair (l : ℕ) :
    let f : ℝ → ℂ := fun r => (r : ℂ) ^ l
    let g : ℝ → ℂ := fun r => (r : ℂ) ^ (-(l : ℂ) - 1)
    ContDiffOn ℝ 2 f (Ioi 0) ∧ ContDiffOn ℝ 2 g (Ioi 0) ∧ ∀ r : ℝ, 0 < r →
      (r : ℂ) ^ 2 * iteratedDeriv 2 f r + 2 * r * deriv f r -
        (l : ℂ) * (l + 1) * f r = 0 ∧
      (r : ℂ) ^ 2 * iteratedDeriv 2 g r + 2 * r * deriv g r -
        (l : ℂ) * (l + 1) * g r = 0 ∧
      ODE.wronskian f g r = -((2 : ℂ) * l + 1) / (r : ℂ) ^ 2 := by
  sorry

end DLMF.WaveEquation
