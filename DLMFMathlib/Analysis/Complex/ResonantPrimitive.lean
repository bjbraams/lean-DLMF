/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The logarithmic coefficient of a resonant reduction-of-order primitive

Olver, *Asymptotics and Special Functions*, Chapter 5, §5, pp. 151–153,
synopsis O-5.09. If an analytic numerator is divided by `z^(N+1)`, its
primitive has one logarithm, whose coefficient is both the `N`th Taylor
coefficient of the numerator and the contour residue. Multiplying this
primitive by the first Frobenius solution gives the resonant second solution.
The residue convention is reused from pinned TauCeti.
-/

@[expose] public noncomputable section

open Set Complex
open scoped BigOperators

namespace Complex

/-- The analytic regular part of a meromorphic primitive and its exact logarithmic
coefficient. The finite principal part is displayed explicitly; `N=0` gives no such
part and leaves precisely the repeated-root logarithm.
Olver, Chapter 5, §5, pp. 151–153, synopsis O-5.09. -/
theorem exists_resonant_primitive {k : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hk : AnalyticOnNhd ℂ k (Metric.ball 0 R)) (N : ℕ) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (Metric.ball 0 R) ∧ H 0 = 0 ∧
      TauCeti.Contour.residue (fun z => k z / z ^ (N + 1)) 0 =
        iteratedDeriv N k 0 / (N.factorial : ℂ) ∧
      ∀ z ∈ Metric.ball 0 R, z ∈ slitPlane →
        HasDerivAt (fun t : ℂ =>
          (∑ j ∈ Finset.range N, iteratedDeriv j k 0 / (j.factorial : ℂ) /
            ((j : ℂ) - N) * t ^ ((j : ℤ) - (N : ℤ))) +
          iteratedDeriv N k 0 / (N.factorial : ℂ) * log t + H t)
          (k z / z ^ (N + 1)) z := by
  sorry

end Complex
