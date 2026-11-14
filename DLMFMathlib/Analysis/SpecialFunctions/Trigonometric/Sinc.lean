/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
/-!
# Analyticity of the sinc function

Mathlib's identity `sinc = dslope sin 0` and analytic divided-difference API show that the
removable value of sinc at zero preserves real analyticity and smoothness.
-/

public noncomputable section
namespace Real
/-- The real sinc function is analytic, including at its removable value at zero. -/
lemma analyticAt_sinc (x : ℝ) : AnalyticAt ℝ sinc x := by
  simpa only [sinc_eq_dslope] using (Real.analyticAt_sin (x := x)).dslope 0
/-- The real sinc function is smooth to every order. -/
lemma contDiff_sinc {n : WithTop ℕ∞} : ContDiff ℝ n sinc :=
  contDiff_iff_contDiffAt.mpr fun x => (analyticAt_sinc x).contDiffAt
end Real
