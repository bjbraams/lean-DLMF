/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Polar coordinates and orthogonal covariance of the Laplacian

Andrews, Askey and Roy, *Special Functions*, §§9.4–9.5, pp. 451–454
(synopsis AAR-9.1–9.5). The angular Laplacian at a unit vector is the
ordinary ambient Laplacian of the radially constant extension. This avoids
introducing a competing sphere differential-operator definition.
-/

@[expose] public noncomputable section

open Laplacian

namespace InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Polar decomposition of the Laplacian at a nonzero point for arbitrary vector-valued
`C²` functions. Andrews–Askey–Roy, *Special Functions*, §9.5, pp. 453–454
(synopsis AAR-9.1–9.5). The last term is the sphere Laplacian of the angular
function with radius fixed at `‖x‖`. -/
theorem laplacian_eq_polar {f : E → F} {x : E} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f x) :
    (Δ f) x =
      iteratedDeriv 2 (fun r : ℝ => f (r • (‖x‖⁻¹ • x))) ‖x‖ +
        (((Module.finrank ℝ E : ℝ) - 1) / ‖x‖) •
          deriv (fun r : ℝ => f (r • (‖x‖⁻¹ • x))) ‖x‖ +
        (‖x‖ ^ 2)⁻¹ •
          (Δ (fun y : E => f (‖x‖ • (‖y‖⁻¹ • y)))) (‖x‖⁻¹ • x) := by
  sorry

/-- Orthogonal changes of coordinates commute with the Laplacian.
Andrews–Askey–Roy, *Special Functions*, §9.4, pp. 451–453
(synopsis AAR-9.1–9.5). The codomain may be any real normed space. -/
theorem laplacian_comp_linearIsometryEquiv (U : E ≃ₗᵢ[ℝ] E)
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f (U x)) :
    (Δ (fun y => f (U y))) x = (Δ f) (U x) := by
  sorry

end InnerProductSpace
