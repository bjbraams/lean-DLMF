/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.OrthogonalCoordinates
public import TauCeti.Analysis.Calculus.CoordinateDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Prolate spheroidal coordinates

The focal-length normalization is `z=c*xi*eta`, with `xi>1` and `|eta|<1`.
The metric and Laplacian retain the regular-chart hypotheses. Source:
Kristensson, *Second Order Differential Equations*, Chapter 8, §8.6,
pp. 159–161, with `xi=cosh(u)` and `eta=cos(w)`.
-/

@[expose] public noncomputable section

open Set TauCeti Laplacian
open scoped Real

namespace EuclideanSpace

/-- Prolate spheroidal coordinates with focal half-distance `c`.
On the regular real chart `xi>1`, `|eta|<1`, both square roots are positive.
Kristensson, Chapter 8, §8.6, p. 160. -/
def prolateSpheroidalCoordinates (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![c * Real.sqrt (((q 0) ^ 2 - 1) * (1 - (q 1) ^ 2)) * Real.cos (q 2),
    c * Real.sqrt (((q 0) ^ 2 - 1) * (1 - (q 1) ^ 2)) * Real.sin (q 2), c * q 0 * q 1]

/-- The defining Cartesian coordinates of the prolate chart. -/
theorem prolateSpheroidalCoordinates_def (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    prolateSpheroidalCoordinates c q =
      WithLp.toLp 2 ![c * Real.sqrt (((q 0) ^ 2 - 1) * (1 - (q 1) ^ 2)) * Real.cos (q 2),
        c * Real.sqrt (((q 0) ^ 2 - 1) * (1 - (q 1) ^ 2)) * Real.sin (q 2), c * q 0 * q 1] := rfl

/-- The `xi=cosh(u)`, `eta=cos(w)` form is the hyperbolic/trigonometric
normalization used in the book. Kristensson, Chapter 8, §8.6, p. 160. -/
theorem prolateSpheroidalCoordinates_cosh_cos (c u w phi : ℝ)
    (hu : 0 < u) (hw : w ∈ Ioo (0 : ℝ) Real.pi) :
    prolateSpheroidalCoordinates c (WithLp.toLp 2 ![Real.cosh u, Real.cos w, phi]) =
      WithLp.toLp 2 ![c * Real.sinh u * Real.sin w * Real.cos phi,
        c * Real.sinh u * Real.sin w * Real.sin phi, c * Real.cosh u * Real.cos w] := by
  sorry

/-- The prolate metric is diagonal, with the three squared scale factors.
Kristensson, Chapter 8, §8.6, pp. 159–161. -/
theorem inner_fderiv_prolateSpheroidalCoordinates {c : ℝ} (hc : 0 < c)
    (q : EuclideanSpace ℝ (Fin 3)) (hxi : 1 < q 0) (heta : q 1 ∈ Ioo (-1 : ℝ) 1)
    (i j : Fin 3) :
    inner ℝ (fderiv ℝ (prolateSpheroidalCoordinates c) q (EuclideanSpace.single i 1))
      (fderiv ℝ (prolateSpheroidalCoordinates c) q (EuclideanSpace.single j 1)) =
        if i = j then if i = 0 then c ^ 2 * ((q 0) ^ 2 - (q 1) ^ 2) / ((q 0) ^ 2 - 1)
          else if i = 1 then c ^ 2 * ((q 0) ^ 2 - (q 1) ^ 2) / (1 - (q 1) ^ 2)
          else c ^ 2 * ((q 0) ^ 2 - 1) * (1 - (q 1) ^ 2)
        else 0 := by
  sorry

/-- The Cartesian Laplacian pulled back to the regular prolate chart.
Kristensson, Chapter 8, §8.6, pp. 159–161. -/
theorem laplacian_prolateSpheroidalCoordinates {c : ℝ} (hc : 0 < c)
    (u : EuclideanSpace ℝ (Fin 3) → ℂ) (q : EuclideanSpace ℝ (Fin 3))
    (hxi : 1 < q 0) (heta : q 1 ∈ Ioo (-1 : ℝ) 1)
    (hu : ContDiffAt ℝ 2 u (prolateSpheroidalCoordinates c q)) :
    let U := u ∘ prolateSpheroidalCoordinates c
    laplacian u (prolateSpheroidalCoordinates c q) =
      (((q 0) ^ 2 - 1 : ℝ) * coordinateDeriv [0, 0] U q +
        (2 * q 0 : ℝ) * coordinateDeriv [0] U q +
        (1 - (q 1) ^ 2 : ℝ) * coordinateDeriv [1, 1] U q -
        (2 * q 1 : ℝ) * coordinateDeriv [1] U q +
        (((q 0) ^ 2 - (q 1) ^ 2) / (((q 0) ^ 2 - 1) * (1 - (q 1) ^ 2)) : ℝ) *
          coordinateDeriv [2, 2] U q) / (c ^ 2 * ((q 0) ^ 2 - (q 1) ^ 2) : ℝ) := by
  sorry

end EuclideanSpace
