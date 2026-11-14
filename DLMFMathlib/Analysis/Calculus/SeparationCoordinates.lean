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
# Explicit cylindrical and spheroidal coordinate Laplacians

Temme, *Special Functions* (1996), §§10.1–10.2, pp. 258–268.
The coordinate derivatives use TauCeti's canonical Euclidean-coordinate API,
and the Cartesian Laplacian is Mathlib's `Laplacian.laplacian`.
-/

@[expose] public noncomputable section
open Set TauCeti Laplacian
open scoped Real
namespace EuclideanSpace

/-- Elliptic cylinder coordinates, with positive focal distance `c` on the regular chart,
Temme §10.2.3, synopsis TEM-10-04. -/
def ellipticCylinderCoordinates (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![c * Real.cosh (q 0) * Real.cos (q 1),
    c * Real.sinh (q 0) * Real.sin (q 1), q 2]

/-- The defining elliptic cylinder chart, Temme §10.2.3. -/
theorem ellipticCylinderCoordinates_def (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    ellipticCylinderCoordinates c q =
      WithLp.toLp 2 ![c * Real.cosh (q 0) * Real.cos (q 1),
        c * Real.sinh (q 0) * Real.sin (q 1), q 2] := rfl

/-- Parabolic cylinder coordinates, regular away from the focal axis,
Temme §10.2.4, synopsis TEM-10-04. -/
def parabolicCylinderCoordinates (q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![((q 0) ^ 2 - (q 1) ^ 2) / 2, q 0 * q 1, q 2]

/-- The defining parabolic cylinder chart, Temme §10.2.4. -/
theorem parabolicCylinderCoordinates_def (q : EuclideanSpace ℝ (Fin 3)) :
    parabolicCylinderCoordinates q =
      WithLp.toLp 2 ![((q 0) ^ 2 - (q 1) ^ 2) / 2, q 0 * q 1, q 2] := rfl

/-- Oblate spheroidal coordinates with focal radius `c`, regular for `ξ>0`, `|η|<1`,
Temme §10.2.5, synopsis TEM-10-05. -/
def oblateSpheroidalCoordinates (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![c * Real.sqrt ((1 + (q 0) ^ 2) * (1 - (q 1) ^ 2)) * Real.cos (q 2),
    c * Real.sqrt ((1 + (q 0) ^ 2) * (1 - (q 1) ^ 2)) * Real.sin (q 2), c * q 0 * q 1]

/-- The defining oblate spheroidal chart, Temme §10.2.5. -/
theorem oblateSpheroidalCoordinates_def (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    oblateSpheroidalCoordinates c q =
      WithLp.toLp 2 ![c * Real.sqrt ((1 + (q 0) ^ 2) * (1 - (q 1) ^ 2)) * Real.cos (q 2),
        c * Real.sqrt ((1 + (q 0) ^ 2) * (1 - (q 1) ^ 2)) * Real.sin (q 2), c * q 0 * q 1] := rfl

/-- The cylindrical-coordinate Laplacian off the axis, Temme §10.2.1,
synopsis TEM-10-02. -/
theorem laplacian_cylindricalCoordinates
    (u : EuclideanSpace ℝ (Fin 3) → ℂ) (q : EuclideanSpace ℝ (Fin 3))
    (hq : 0 < q 0)
    (hu : ContDiffAt ℝ 2 u
      (WithLp.toLp 2 ![q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2])) :
    let φ := fun p : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 ![p 0 * Real.cos (p 1), p 0 * Real.sin (p 1), p 2]
    let U := u ∘ φ
    laplacian u (φ q) = coordinateDeriv [0, 0] U q +
      coordinateDeriv [0] U q / q 0 + coordinateDeriv [1, 1] U q / (q 0 : ℂ) ^ 2 +
        coordinateDeriv [2, 2] U q := by
  sorry

/-- The spherical-coordinate Laplacian away from the polar axes,
Temme §10.2.2, synopsis TEM-10-03. -/
theorem laplacian_sphericalCoordinates
    (u : EuclideanSpace ℝ (Fin 3) → ℂ) (q : EuclideanSpace ℝ (Fin 3))
    (hr : 0 < q 0) (hθ : q 1 ∈ Ioo (0 : ℝ) Real.pi)
    (hu : ContDiffAt ℝ 2 u
      (WithLp.toLp 2 ![q 0 * Real.sin (q 1) * Real.cos (q 2),
        q 0 * Real.sin (q 1) * Real.sin (q 2), q 0 * Real.cos (q 1)])) :
    let φ := fun p : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 ![p 0 * Real.sin (p 1) * Real.cos (p 2),
        p 0 * Real.sin (p 1) * Real.sin (p 2), p 0 * Real.cos (p 1)]
    let U := u ∘ φ
    laplacian u (φ q) = coordinateDeriv [0, 0] U q +
      2 * coordinateDeriv [0] U q / q 0 +
        (coordinateDeriv [1, 1] U q +
          (Real.cos (q 1) / Real.sin (q 1) : ℝ) * coordinateDeriv [1] U q +
          coordinateDeriv [2, 2] U q / (Real.sin (q 1) : ℂ) ^ 2) / (q 0 : ℂ) ^ 2 := by
  sorry

/-- The elliptic-cylinder Laplacian, Temme §10.2.3, synopsis TEM-10-04. -/
theorem laplacian_ellipticCylinderCoordinates {c : ℝ} (hc : 0 < c)
    (u : EuclideanSpace ℝ (Fin 3) → ℂ) (q : EuclideanSpace ℝ (Fin 3))
    (hq : 0 < Real.sinh (q 0) ^ 2 + Real.sin (q 1) ^ 2)
    (hu : ContDiffAt ℝ 2 u (ellipticCylinderCoordinates c q)) :
    let U := u ∘ ellipticCylinderCoordinates c
    laplacian u (ellipticCylinderCoordinates c q) =
      (coordinateDeriv [0, 0] U q + coordinateDeriv [1, 1] U q) /
        (c ^ 2 * (Real.sinh (q 0) ^ 2 + Real.sin (q 1) ^ 2) : ℝ) +
          coordinateDeriv [2, 2] U q := by
  sorry

/-- The parabolic-cylinder Laplacian, Temme §10.2.4, synopsis TEM-10-04. -/
theorem laplacian_parabolicCylinderCoordinates
    (u : EuclideanSpace ℝ (Fin 3) → ℂ) (q : EuclideanSpace ℝ (Fin 3))
    (hq : 0 < (q 0) ^ 2 + (q 1) ^ 2)
    (hu : ContDiffAt ℝ 2 u (parabolicCylinderCoordinates q)) :
    let U := u ∘ parabolicCylinderCoordinates
    laplacian u (parabolicCylinderCoordinates q) =
      (coordinateDeriv [0, 0] U q + coordinateDeriv [1, 1] U q) /
        ((q 0) ^ 2 + (q 1) ^ 2 : ℝ) + coordinateDeriv [2, 2] U q := by
  sorry

/-- The oblate-spheroidal Laplacian on its regular chart,
Temme §10.2.5, synopsis TEM-10-05. -/
theorem laplacian_oblateSpheroidalCoordinates {c : ℝ} (hc : 0 < c)
    (u : EuclideanSpace ℝ (Fin 3) → ℂ) (q : EuclideanSpace ℝ (Fin 3))
    (hξ : 0 < q 0) (hη : q 1 ∈ Ioo (-1 : ℝ) 1)
    (hu : ContDiffAt ℝ 2 u (oblateSpheroidalCoordinates c q)) :
    let U := u ∘ oblateSpheroidalCoordinates c
    laplacian u (oblateSpheroidalCoordinates c q) =
      (((1 + (q 0) ^ 2 : ℝ) * coordinateDeriv [0, 0] U q +
          (2 * q 0 : ℝ) * coordinateDeriv [0] U q +
          (1 - (q 1) ^ 2 : ℝ) * coordinateDeriv [1, 1] U q -
          (2 * q 1 : ℝ) * coordinateDeriv [1] U q) +
        (((q 0) ^ 2 + (q 1) ^ 2) / ((1 + (q 0) ^ 2) * (1 - (q 1) ^ 2)) : ℝ) *
          coordinateDeriv [2, 2] U q) / (c ^ 2 * ((q 0) ^ 2 + (q 1) ^ 2) : ℝ) := by
  sorry

end EuclideanSpace
