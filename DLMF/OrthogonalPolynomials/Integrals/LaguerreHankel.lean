/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import DLMF.Bessel.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Laguerre–Bessel transforms and Hankel eigenfunctions

Temme, *Special Functions* (1996), Exercise 9.8, pp. 250–251.
The polynomial continuation retains complex parameters below the usual
orthogonality range whenever the integral still converges.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Set DLMF.Bessel
namespace DLMF.OrthogonalPolynomials

/-- The Laguerre–Bessel integral on its full complex-parameter convergence domain,
Temme Exercise 9.8, synopsis TEM-09-19. -/
theorem integral_laguerreExtended_besselJ {α : ℂ} (n : ℕ) {x : ℝ}
    (hx : 0 < x) (hα : -1 < (n : ℝ) + α.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (n + α / 2) *
      besselJ α (2 * Real.sqrt (x * t)) * exp (-t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (n + α / 2) *
        besselJ α (2 * Real.sqrt (x * t)) * exp (-t)) =
        (x : ℂ) ^ (α / 2) * exp (-x) * n.factorial * laguerreExtended α n x := by
  sorry

/-- Laguerre functions diagonalize the normalized Hankel transform,
Temme Exercise 9.8, synopsis TEM-09-19. -/
theorem integral_laguerreExtended_hankel {α : ℝ} (hα : -1 < α) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α / 2 : ℂ) *
      besselJ α (Real.sqrt (x * t)) * exp (-(t : ℂ) / 2) *
        laguerreExtended α n t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (α / 2 : ℂ) *
        besselJ α (Real.sqrt (x * t)) * exp (-(t : ℂ) / 2) *
          laguerreExtended α n t) =
        2 * (-1 : ℂ) ^ n * (x : ℂ) ^ (α / 2 : ℂ) * exp (-(x : ℂ) / 2) *
          laguerreExtended α n x := by
  sorry

end DLMF.OrthogonalPolynomials
