/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Toroidal
public import DLMFMathlib.Analysis.Calculus.OrthogonalCoordinates
public import TauCeti.Analysis.Calculus.CoordinateDeriv

/-!
# Toroidal separation of Laplace's equation

The chart is a Euclidean-space bridge to the canonical DLMF toroidal coordinates.
Its metric, pulled-back Laplacian and separated product retain the regular-chart
conditions. Source: Kristensson, *Second Order Differential Equations*,
Chapter 6, Example 6.2, pp. 120–121; DLMF §14.19.
-/

@[expose] public noncomputable section

open Complex EuclideanSpace Laplacian Set
open scoped Real

namespace DLMF.Legendre

/-- The canonical triple-valued toroidal map viewed as a Euclidean chart.
No normalization is changed: the entries are those of `toroidalCoordinates`.
Kristensson, Chapter 6, Example 6.2, pp. 120–121. -/
def toroidalCoordinateChart (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  let p := toroidalCoordinates c (q 0) (q 1) (q 2)
  WithLp.toLp 2 ![p.1, p.2.1, p.2.2]

/-- The Euclidean chart uses exactly the existing canonical toroidal coordinates. -/
theorem toroidalCoordinateChart_def (c : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    toroidalCoordinateChart c q =
      let p := toroidalCoordinates c (q 0) (q 1) (q 2)
      WithLp.toLp 2 ![p.1, p.2.1, p.2.2] := rfl

/-- The toroidal metric is diagonal with scales `c/D,c/D,c*sinh(eta)/D`,
where `D=cosh(eta)-cos(theta)`. Kristensson, Example 6.2, pp. 120–121. -/
theorem inner_fderiv_toroidalCoordinateChart {c : ℝ} (hc : 0 < c)
    (q : EuclideanSpace ℝ (Fin 3)) (heta : 0 < q 0) (i j : Fin 3) :
    inner ℝ (fderiv ℝ (toroidalCoordinateChart c) q (EuclideanSpace.single i 1))
      (fderiv ℝ (toroidalCoordinateChart c) q (EuclideanSpace.single j 1)) =
      if i = j then
        (if i = 2 then c * Real.sinh (q 0) else c) ^ 2 /
          (Real.cosh (q 0) - Real.cos (q 1)) ^ 2
      else 0 := by
  sorry

/-- The Cartesian Laplacian equals the orthogonal metric-divergence expression
in toroidal coordinates. Kristensson, Example 6.2, pp. 120–121. -/
theorem laplacian_toroidalCoordinateChart {c : ℝ} (hc : 0 < c)
    (u : EuclideanSpace ℝ (Fin 3) → ℂ) (q : EuclideanSpace ℝ (Fin 3))
    (heta : 0 < q 0) (hu : ContDiffAt ℝ 2 u (toroidalCoordinateChart c q)) :
    laplacian u (toroidalCoordinateChart c q) =
      orthogonalLaplacian (fun j p =>
        (if j = 2 then c * Real.sinh (p 0) else c) /
          (Real.cosh (p 0) - Real.cos (p 1))) (u ∘ toroidalCoordinateChart c) q := by
  sorry

/-- The separated toroidal product is harmonic in the toroidal metric.
The square-root prefactor is essential to obtain degree `n-1/2`.
Kristensson, Example 6.2, pp. 120–121. -/
theorem laplace_toroidal_product (X Y Z : ℝ → ℂ) (m n : ℤ)
    {c : ℝ} (hc : 0 < c) (q : EuclideanSpace ℝ (Fin 3)) (heta : 0 < q 0)
    (hX : ContDiffAt ℝ 2 X (q 1)) (hY : ContDiffAt ℝ 2 Y (q 0))
    (hZ : ContDiffAt ℝ 2 Z (q 2))
    (hXode : iteratedDeriv 2 X (q 1) + (n : ℂ) ^ 2 * X (q 1) = 0)
    (hZode : iteratedDeriv 2 Z (q 2) + (m : ℂ) ^ 2 * Z (q 2) = 0)
    (hYode : iteratedDeriv 2 Y (q 0) +
      (Real.cosh (q 0) / Real.sinh (q 0) : ℝ) * deriv Y (q 0) -
      ((n : ℂ) ^ 2 - 1 / 4 + (m : ℂ) ^ 2 / (Real.sinh (q 0) : ℂ) ^ 2) * Y (q 0) = 0) :
    let U := fun p : EuclideanSpace ℝ (Fin 3) =>
      (Real.sqrt (Real.cosh (p 0) - Real.cos (p 1)) : ℂ) * X (p 1) * Y (p 0) * Z (p 2)
    orthogonalLaplacian (fun j p =>
      (if j = 2 then c * Real.sinh (p 0) else c) /
        (Real.cosh (p 0) - Real.cos (p 1))) U q = 0 := by
  sorry

/-- The associated Legendre radial function at `cosh(eta)` solves the toroidal
radial equation of degree `nu`. Kristensson, Example 6.2, pp. 120–121. -/
theorem associatedP_cosh_differential_equation (ν μ : ℂ) {eta : ℝ} (heta : 0 < eta) :
    let Y := fun t : ℝ => associatedP ν μ (Real.cosh t)
    iteratedDeriv 2 Y eta + (Real.cosh eta / Real.sinh eta : ℝ) * deriv Y eta -
      (ν * (ν + 1) + μ ^ 2 / (Real.sinh eta : ℂ) ^ 2) * Y eta = 0 := by
  sorry

/-- The regularized associated Legendre function of the second kind supplies the
second toroidal radial solution. Kristensson, Example 6.2, pp. 120–121. -/
theorem olverQ_cosh_differential_equation (ν μ : ℂ) {eta : ℝ} (heta : 0 < eta) :
    let Y := fun t : ℝ => olverQ ν μ (Real.cosh t)
    iteratedDeriv 2 Y eta + (Real.cosh eta / Real.sinh eta : ℝ) * deriv Y eta -
      (ν * (ν + 1) + μ ^ 2 / (Real.sinh eta : ℂ) ^ 2) * Y eta = 0 := by
  sorry

end DLMF.Legendre
