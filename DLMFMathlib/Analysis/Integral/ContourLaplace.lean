/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Contour Laplace solutions of equations with affine coefficients

Temme, *Special Functions* (1996), §4.6, pp. 98–103, synopsis TEM-04-07.
The contour transform includes its path derivative. Infinite paths are
handled by locally uniform limits and a vanishing endpoint defect.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Complex

/-- The Laplace transform along a continuously differentiable path on `[0,1]`,
Temme §4.6, synopsis TEM-04-07. -/
def contourLaplace (γ : ℝ → ℂ) (v : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, exp (z * γ t) * v (γ t) * deriv γ t

/-- The path-integral formula defining the contour Laplace transform,
Temme §4.6, synopsis TEM-04-07. -/
theorem contourLaplace_def (γ : ℝ → ℂ) (v : ℂ → ℂ) (z : ℂ) :
    contourLaplace γ v z = ∫ t : ℝ in (0 : ℝ)..1, exp (z * γ t) * v (γ t) * deriv γ t := rfl

/-- The explicit kernel determined by a primitive of `B/A`, Temme §4.6,
synopsis TEM-04-07. Its mathematical domain excludes zeros of `A`. -/
def affineEquationLaplaceKernel (A P : ℂ → ℂ) (t : ℂ) : ℂ := exp (P t) / A t

/-- The kernel formula for affine-coefficient contour solutions, Temme §4.6. -/
theorem affineEquationLaplaceKernel_def (A P : ℂ → ℂ) (t : ℂ) :
    affineEquationLaplaceKernel A P t = exp (P t) / A t := rfl

/-- A compact continuously differentiable contour gives an entire transform,
Temme §4.6, synopsis TEM-04-07. -/
theorem differentiable_contourLaplace (γ : ℝ → ℂ) (v : ℂ → ℂ)
    (hγ : ContDiff ℝ 1 γ) (hv : ContinuousOn v (γ '' Icc 0 1)) :
    Differentiable ℂ (contourLaplace γ v) := by
  sorry

/-- Integrating by parts gives the exact affine-equation endpoint defect,
Temme §4.6, synopsis TEM-04-07. -/
theorem contourLaplace_affine_residual (a₀ a₁ b₀ b₁ c₀ c₁ : ℂ)
    (γ : ℝ → ℂ) (v : ℂ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ v (γ t))
    (hkernel : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun w : ℂ => (a₁ * w ^ 2 + b₁ * w + c₁) * v w)
        ((a₀ * (γ t) ^ 2 + b₀ * γ t + c₀) * v (γ t)) (γ t)) (z : ℂ) :
    (a₀ + a₁ * z) * iteratedDeriv 2 (contourLaplace γ v) z +
      (b₀ + b₁ * z) * deriv (contourLaplace γ v) z + (c₀ + c₁ * z) * contourLaplace γ v z =
      exp (z * γ 1) * (a₁ * (γ 1) ^ 2 + b₁ * γ 1 + c₁) * v (γ 1) -
        exp (z * γ 0) * (a₁ * (γ 0) ^ 2 + b₁ * γ 0 + c₁) * v (γ 0) := by
  sorry

/-- An ordinary improper contour limit solves the affine equation when its endpoint
terms vanish and the transforms converge locally uniformly,
Temme §4.6, synopsis TEM-04-07. No absolute convergence of the limiting contour is required. -/
theorem affine_ode_of_tendstoLocallyUniformlyOn_contourLaplace
    (a₀ a₁ b₀ b₁ c₀ c₁ : ℂ) (γ : ℕ → ℝ → ℂ) (v y : ℂ → ℂ)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hγ : ∀ n, ContDiff ℝ 1 (γ n))
    (hv : ∀ n t, t ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ v (γ n t))
    (hkernel : ∀ n t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun w : ℂ => (a₁ * w ^ 2 + b₁ * w + c₁) * v w)
        ((a₀ * (γ n t) ^ 2 + b₀ * γ n t + c₀) * v (γ n t)) (γ n t))
    (hlim : TendstoLocallyUniformlyOn (fun n => contourLaplace (γ n) v) y atTop Ω)
    (hend : ∀ z ∈ Ω, Tendsto (fun n =>
      exp (z * γ n 1) * (a₁ * (γ n 1) ^ 2 + b₁ * γ n 1 + c₁) * v (γ n 1) -
        exp (z * γ n 0) * (a₁ * (γ n 0) ^ 2 + b₁ * γ n 0 + c₁) * v (γ n 0)) atTop (𝓝 0)) :
    AnalyticOnNhd ℂ y Ω ∧ ∀ z ∈ Ω,
      (a₀ + a₁ * z) * iteratedDeriv 2 y z + (b₀ + b₁ * z) * deriv y z +
        (c₀ + c₁ * z) * y z = 0 := by
  sorry

/-- A primitive of `B/A` produces the required first-order kernel equation,
Temme §4.6, synopsis TEM-04-07. -/
theorem hasDerivAt_mul_affineEquationLaplaceKernel (a₁ b₁ c₁ : ℂ)
    (P B : ℂ → ℂ) {t : ℂ} (hA : a₁ * t ^ 2 + b₁ * t + c₁ ≠ 0)
    (hP : HasDerivAt P (B t / (a₁ * t ^ 2 + b₁ * t + c₁)) t) :
    HasDerivAt (fun w : ℂ => (a₁ * w ^ 2 + b₁ * w + c₁) *
      affineEquationLaplaceKernel (fun s => a₁ * s ^ 2 + b₁ * s + c₁) P w)
      (B t * affineEquationLaplaceKernel (fun s => a₁ * s ^ 2 + b₁ * s + c₁) P t) t := by
  sorry

end Complex
