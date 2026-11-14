/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.BarnesContour
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Barnes Gamma integrals on contours with finite deformations

The binomial integral and Barnes's first lemma hold for any upward contour with
vertical tails separating the two Gamma pole families. Sources: Kristensson,
*Second Order Differential Equations*, Chapter 5, Corollary 5.3 and Lemma 5.6,
pp. 84–88; Andrews–Askey–Roy, *Special Functions*, Chapter 2, §2.4.
The geometry is `Complex.BarnesContour`; actual absolute integrability is asserted
separately from each evaluated integral.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Gamma

/-- The binomial Barnes integrand is absolutely integrable on every pole-separating
contour in the complete cut `abs(arg(-z))<pi`. Kristensson, Chapter 5,
Corollary 5.3, p. 84. -/
theorem isIntegrable_barnes_binomial {a z : ℂ}
    (C : BarnesContour ![a] ![(0 : ℂ)]) (hz : -z ∈ slitPlane) :
    C.IsIntegrable (fun s => Gamma (a + s) * Gamma (-s) * (-z) ^ s) := by
  sorry

/-- The binomial Barnes identity permits finite contour deformations even when no
single pole-separating straight vertical line exists. Kristensson, Chapter 5,
Corollary 5.3, p. 84; AAR Chapter 2, §2.4. -/
theorem Gamma_mul_one_sub_cpow_neg_barnesContour {a z : ℂ}
    (C : BarnesContour ![a] ![(0 : ℂ)]) (hz : -z ∈ slitPlane) :
    Gamma a * (1 - z) ^ (-a) =
      C.integral (fun s => Gamma (a + s) * Gamma (-s) * (-z) ^ s) /
        (2 * Real.pi * I) := by
  sorry

/-- The four-Gamma kernel of Barnes's first lemma is absolutely integrable on
every separating contour. Kristensson, Chapter 5, Lemma 5.6, pp. 86–88;
AAR Chapter 2, Barnes's first lemma. -/
theorem isIntegrable_barnes_first {a b c d : ℂ}
    (C : BarnesContour ![a, b] ![c, d]) :
    C.IsIntegrable (fun s =>
      Gamma (a + s) * Gamma (b + s) * Gamma (c - s) * Gamma (d - s)) := by
  sorry

/-- Barnes's first lemma with arbitrary finite pole-separating deformations and
vertical tails. Opposite pole coincidences are ruled out by the contour data;
no positivity condition on the parameter real parts is added. Kristensson,
Chapter 5, Lemma 5.6, pp. 86–88; AAR Chapter 2, §2.4. -/
theorem barnes_first_lemma_contour {a b c d : ℂ}
    (C : BarnesContour ![a, b] ![c, d]) :
    C.integral (fun s =>
      Gamma (a + s) * Gamma (b + s) * Gamma (c - s) * Gamma (d - s)) /
        (2 * Real.pi * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) /
        Gamma (a + b + c + d) := by
  sorry

end DLMF.Gamma
