/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.SeparationCoordinates
public import DLMF.Legendre.Basic
public import DLMF.Bessel.Basic

/-!
# Product modes in cylindrical and spheroidal coordinates

Temme, *Special Functions* (1996), §§10.2.1–10.2.5, pp. 259–268.
The equations are stated with their exact separation constants. The
orthogonal-coordinate Laplacian is linked to Cartesian space by the chart theorem.
-/

@[expose] public noncomputable section
open Complex EuclideanSpace Set
namespace DLMF.WaveEquation

/-- Cylindrical product separation with an arbitrary integral azimuthal mode,
Temme §10.2.1, synopsis TEM-10-02. -/
theorem helmholtz_cylindrical_product (R Z : ℝ → ℂ) (m : ℤ) (k kz : ℝ)
    (q : EuclideanSpace ℝ (Fin 3)) (hr : 0 < q 0)
    (hR : ContDiffAt ℝ 2 R (q 0)) (hZ : ContDiffAt ℝ 2 Z (q 2))
    (hrode : iteratedDeriv 2 R (q 0) + deriv R (q 0) / q 0 +
      (k ^ 2 - kz ^ 2 - (m : ℝ) ^ 2 / (q 0) ^ 2 : ℝ) * R (q 0) = 0)
    (hzode : iteratedDeriv 2 Z (q 2) + kz ^ 2 * Z (q 2) = 0) :
    let U := fun p : EuclideanSpace ℝ (Fin 3) => R (p 0) * exp (I * m * p 1) * Z (p 2)
    orthogonalLaplacian (fun j p => if j = 1 then p 0 else 1) U q + k ^ 2 * U q = 0 := by
  sorry

/-- Spherical product separation with a general associated Legendre angular mode,
Temme §10.2.2, synopsis TEM-10-03. -/
theorem helmholtz_spherical_product (R : ℝ → ℂ) (l : ℕ) (m : ℤ)
    (hm : m.natAbs ≤ l) (k : ℝ) (q : EuclideanSpace ℝ (Fin 3))
    (hr : 0 < q 0) (hθ : q 1 ∈ Ioo (0 : ℝ) Real.pi)
    (hR : ContDiffAt ℝ 2 R (q 0))
    (hrode : (q 0 : ℂ) ^ 2 * iteratedDeriv 2 R (q 0) +
      2 * q 0 * deriv R (q 0) + ((k * q 0) ^ 2 - l * (l + 1) : ℝ) * R (q 0) = 0) :
    let U := fun p : EuclideanSpace ℝ (Fin 3) =>
      R (p 0) * DLMF.Legendre.ferrersP l m (Real.cos (p 1)) * exp (I * m * p 2)
    orthogonalLaplacian
      (fun j p => if j = 0 then 1 else if j = 1 then p 0 else p 0 * Real.sin (p 1)) U q +
        k ^ 2 * U q = 0 := by
  sorry

/-- Elliptic-cylinder separation into the angular and modified Mathieu equations,
Temme §10.2.3, synopsis TEM-10-04. -/
theorem helmholtz_elliptic_product (X Θ Z : ℝ → ℂ) (a k kz c : ℝ)
    (hc : 0 < c) (q : EuclideanSpace ℝ (Fin 3))
    (hq : 0 < Real.sinh (q 0) ^ 2 + Real.sin (q 1) ^ 2)
    (hX : ContDiffAt ℝ 2 X (q 0)) (hΘ : ContDiffAt ℝ 2 Θ (q 1))
    (hZ : ContDiffAt ℝ 2 Z (q 2))
    (hXode : iteratedDeriv 2 X (q 0) -
      (a - c ^ 2 * (k ^ 2 - kz ^ 2) / 2 * Real.cosh (2 * q 0) : ℝ) * X (q 0) = 0)
    (hΘode : iteratedDeriv 2 Θ (q 1) +
      (a - c ^ 2 * (k ^ 2 - kz ^ 2) / 2 * Real.cos (2 * q 1) : ℝ) * Θ (q 1) = 0)
    (hZode : iteratedDeriv 2 Z (q 2) + kz ^ 2 * Z (q 2) = 0) :
    let U := fun p : EuclideanSpace ℝ (Fin 3) => X (p 0) * Θ (p 1) * Z (p 2)
    orthogonalLaplacian (fun j p => if j = 2 then 1 else
      c * Real.sqrt (Real.sinh (p 0) ^ 2 + Real.sin (p 1) ^ 2)) U q + k ^ 2 * U q = 0 := by
  sorry

/-- Parabolic-cylinder separation into Weber equations,
Temme §10.2.4, synopsis TEM-10-04. -/
theorem helmholtz_parabolic_product (U V Z : ℝ → ℂ) (a k kz : ℝ)
    (q : EuclideanSpace ℝ (Fin 3)) (hq : 0 < (q 0) ^ 2 + (q 1) ^ 2)
    (hU : ContDiffAt ℝ 2 U (q 0)) (hV : ContDiffAt ℝ 2 V (q 1))
    (hZ : ContDiffAt ℝ 2 Z (q 2))
    (hUode : iteratedDeriv 2 U (q 0) +
      ((k ^ 2 - kz ^ 2) * (q 0) ^ 2 - a : ℝ) * U (q 0) = 0)
    (hVode : iteratedDeriv 2 V (q 1) +
      ((k ^ 2 - kz ^ 2) * (q 1) ^ 2 + a : ℝ) * V (q 1) = 0)
    (hZode : iteratedDeriv 2 Z (q 2) + kz ^ 2 * Z (q 2) = 0) :
    let F := fun p : EuclideanSpace ℝ (Fin 3) => U (p 0) * V (p 1) * Z (p 2)
    orthogonalLaplacian (fun j p => if j = 2 then 1 else
      Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2)) F q + k ^ 2 * F q = 0 := by
  sorry

/-- Oblate separation with the radial and angular spheroidal equations,
Temme §10.2.5, synopsis TEM-10-05. -/
theorem helmholtz_oblate_product (R S : ℝ → ℂ) (m : ℤ) (separationConstant k c : ℝ)
    (hc : 0 < c) (q : EuclideanSpace ℝ (Fin 3))
    (hξ : 0 < q 0) (hη : q 1 ∈ Ioo (-1 : ℝ) 1)
    (hR : ContDiffAt ℝ 2 R (q 0)) (hS : ContDiffAt ℝ 2 S (q 1))
    (hRode : (1 + (q 0) ^ 2 : ℝ) * iteratedDeriv 2 R (q 0) +
      (2 * q 0 : ℝ) * deriv R (q 0) +
      (c ^ 2 * k ^ 2 * (q 0) ^ 2 - separationConstant +
        (m : ℝ) ^ 2 / (1 + (q 0) ^ 2) : ℝ) * R (q 0) = 0)
    (hSode : (1 - (q 1) ^ 2 : ℝ) * iteratedDeriv 2 S (q 1) -
      (2 * q 1 : ℝ) * deriv S (q 1) +
      (separationConstant + c ^ 2 * k ^ 2 * (q 1) ^ 2 -
        (m : ℝ) ^ 2 / (1 - (q 1) ^ 2) : ℝ) * S (q 1) = 0) :
    let U := fun p : EuclideanSpace ℝ (Fin 3) => R (p 0) * S (p 1) * exp (I * m * p 2)
    orthogonalLaplacian (fun j p => if j = 0 then
      c * Real.sqrt (((p 0) ^ 2 + (p 1) ^ 2) / (1 + (p 0) ^ 2)) else if j = 1 then
      c * Real.sqrt (((p 0) ^ 2 + (p 1) ^ 2) / (1 - (p 1) ^ 2)) else
      c * Real.sqrt ((1 + (p 0) ^ 2) * (1 - (p 1) ^ 2))) U q + k ^ 2 * U q = 0 := by
  sorry

end DLMF.WaveEquation
