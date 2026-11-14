/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.BarnesContour
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Barnes summations on deformed separating contours

Andrews, Askey and Roy, *Special Functions*, Theorem 2.4.3 and Theorems 3.6.1,
3.6.3, pp. 85–94 and 150–154. Contours use actual finite paths with vertical
tails from the shared Barnes-contour API. The very-well-poised gamma quotient
is canceled to a linear factor before evaluation, including at its removable poles.
-/

@[expose] public section

open Complex

namespace DLMF.Gamma

/-- Barnes's second lemma on any separating deformation.
Andrews–Askey–Roy, *Special Functions*, Theorem 2.4.3, pp. 88–90
(synopsis AAR-2.4.1–2.4.6). The contour data exclude opposite pole coincidences. -/
theorem barnes_second_lemma_contour (a b c d e : ℂ)
    (C : BarnesContour ![a, b, c] ![d, e]) :
    let H := fun s : ℂ =>
      Gamma (a + s) * Gamma (b + s) * Gamma (c + s) * Gamma (d - s) * Gamma (e - s) /
        Gamma (a + b + c + d + e + s)
    C.IsIntegrable H ∧ C.integral H / (2 * Real.pi * I) =
      Gamma (a + d) * Gamma (b + d) * Gamma (c + d) *
        Gamma (a + e) * Gamma (b + e) * Gamma (c + e) /
        (Gamma (a + b + d + e) * Gamma (a + c + d + e) * Gamma (b + c + d + e)) := by
  sorry

/-- The seven-Gamma Barnes summation on any separating deformation.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.6.1, pp. 150–152
(synopsis AAR-3.6.1–3.8.2). The canceled factor is `a/2+s`, so negative
integer values of that argument cause no artificial gamma-quotient value. -/
theorem barnes_very_well_poised_seven_contour (a b c d : ℂ)
    (C : BarnesContour ![a, b, c, d] ![b - a, 0]) :
    let H := fun s : ℂ =>
      (a / 2 + s) * Gamma (a + s) * Gamma (b + s) * Gamma (c + s) * Gamma (d + s) *
        Gamma (b - a - s) * Gamma (-s) /
        (Gamma (1 + a - c + s) * Gamma (1 + a - d + s))
    C.IsIntegrable H ∧ C.integral H / (2 * Real.pi * I) =
      Gamma b * Gamma c * Gamma d * Gamma (b + c - a) * Gamma (b + d - a) /
        (2 * Gamma (1 + a - c - d) * Gamma (b + c + d - a)) := by
  sorry

/-- The balanced nine-Gamma Barnes summation on any separating deformation.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.6.3, pp. 152–154
(synopsis AAR-3.6.1–3.8.2). All removable very-well-poised gamma factors
are canceled before the integral is evaluated. -/
theorem barnes_balanced_nine_contour (a b c d e f : ℂ)
    (hbalance : 2 * a + 1 = b + c + d + e + f)
    (C : BarnesContour ![a, b, c, d, e, f] ![b - a, 0]) :
    let H := fun s : ℂ =>
      (a / 2 + s) * Gamma (a + s) * Gamma (b + s) * Gamma (c + s) * Gamma (d + s) *
        Gamma (e + s) * Gamma (f + s) * Gamma (b - a - s) * Gamma (-s) /
        (Gamma (1 + a - c + s) * Gamma (1 + a - d + s) *
          Gamma (1 + a - e + s) * Gamma (1 + a - f + s))
    C.IsIntegrable H ∧ C.integral H / (2 * Real.pi * I) =
      Gamma b * Gamma c * Gamma d * Gamma e * Gamma f *
        Gamma (b + c - a) * Gamma (b + d - a) * Gamma (b + e - a) * Gamma (b + f - a) /
        (2 * Gamma (1 + a - c - d) * Gamma (1 + a - c - e) * Gamma (1 + a - c - f) *
          Gamma (1 + a - d - e) * Gamma (1 + a - d - f) * Gamma (1 + a - e - f)) := by
  sorry

end DLMF.Gamma
