/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The Laplacian in orthogonal coordinates

The metric-scale expression for the scalar Laplacian and the product-separation
identity in Kristensson, *Second Order Differential Equations*, Chapter 1, pp. 1–2.
The coordinate transformation theorem uses Mathlib's Euclidean-space Laplacian.
-/

@[expose] public section

open Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace EuclideanSpace

/-- Kristensson, Chapter 1, p. 2: the orthogonal-coordinate Laplacian with
metric scales `h_j`, expressed by directional derivatives along the standard basis.
For a genuine nonsingular coordinate chart the scales are strictly positive. -/
def orthogonalLaplacian {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → F) (ξ : EuclideanSpace ℝ (Fin n)) : F :=
  (∏ j, h j ξ)⁻¹ • ∑ j, fderiv ℝ (fun η =>
    ((∏ k, h k η) / (h j η) ^ 2) • fderiv ℝ u η (EuclideanSpace.single j 1)) ξ
      (EuclideanSpace.single j 1)

/-- The metric-scale formula defining the orthogonal-coordinate Laplacian,
Kristensson, Chapter 1, p. 2. -/
theorem orthogonalLaplacian_def {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → F) (ξ : EuclideanSpace ℝ (Fin n)) :
    orthogonalLaplacian h u ξ =
      (∏ j, h j ξ)⁻¹ • ∑ j, fderiv ℝ (fun η =>
        ((∏ k, h k η) / (h j η) ^ 2) • fderiv ℝ u η (EuclideanSpace.single j 1)) ξ
          (EuclideanSpace.single j 1) := rfl

/-- Kristensson, Chapter 1, p. 2: an orthogonal coordinate chart transforms the
Cartesian Laplacian into the metric-scale divergence expression. The regularity
assumptions ensure all derivatives in that expression exist. -/
theorem laplacian_comp_eq_orthogonalLaplacian {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {h : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {u : EuclideanSpace ℝ (Fin n) → F}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 3 φ U)
    (hu : ContDiffOn ℝ 2 u (φ '' U))
    (hh : ∀ j, ContDiffOn ℝ 2 (h j) U)
    (hpos : ∀ ξ ∈ U, ∀ j, 0 < h j ξ)
    (hmetric : ∀ ξ ∈ U, ∀ i j,
      ⟪fderiv ℝ φ ξ (EuclideanSpace.single i 1),
        fderiv ℝ φ ξ (EuclideanSpace.single j 1)⟫ = if i = j then (h i ξ) ^ 2 else 0)
    {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ξ ∈ U) :
    Laplacian.laplacian u (φ ξ) = orthogonalLaplacian h (u ∘ φ) ξ := by
  sorry

/-- Kristensson, Chapter 1, pp. 1–2: the product-separation identity for a
constant orthogonal metric. Dividing by the product requires each factor nonzero
at the point under consideration. -/
theorem orthogonalLaplacian_prod_const_metric {n : ℕ} (h : Fin n → ℝ)
    (hh : ∀ j, h j ≠ 0) (f : Fin n → ℝ → ℂ)
    (hf : ∀ j, ContDiff ℝ 2 (f j)) (ξ : EuclideanSpace ℝ (Fin n))
    (hne : ∀ j, f j (ξ j) ≠ 0) :
    orthogonalLaplacian (fun j _ => h j) (fun η => ∏ j, f j (η j)) ξ /
      (∏ j, f j (ξ j)) =
        ∑ j, (h j : ℂ)⁻¹ ^ 2 * deriv (deriv (f j)) (ξ j) / f j (ξ j) := by
  sorry

/-- Kristensson, Chapter 1, p. 2: the complete product-separation identity for
variable metric scales. Its right side reduces to ordinary differential expressions
whenever the metric coefficients separate into the indicated individual coordinates. -/
theorem orthogonalLaplacian_prod {n : ℕ}
    (h : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (f : Fin n → ℝ → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n))
    (hh : ∀ j, ContDiffAt ℝ 2 (h j) ξ)
    (hf : ∀ j, ContDiffAt ℝ 2 (f j) (ξ j))
    (hhne : ∀ j, h j ξ ≠ 0) (hfne : ∀ j, f j (ξ j) ≠ 0) :
    orthogonalLaplacian h (fun η => ∏ j, f j (η j)) ξ / (∏ j, f j (ξ j)) =
      ∑ j, ((h j ξ : ℂ)⁻¹ ^ 2 * deriv (deriv (f j)) (ξ j) / f j (ξ j) +
        (((∏ k, h k ξ)⁻¹ * fderiv ℝ (fun η => (∏ k, h k η) / (h j η) ^ 2) ξ
          (EuclideanSpace.single j 1) : ℝ) : ℂ) * deriv (f j) (ξ j) / f j (ξ j)) := by
  sorry

end EuclideanSpace
