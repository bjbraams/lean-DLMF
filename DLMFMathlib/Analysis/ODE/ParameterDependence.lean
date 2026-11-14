/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Instances.Complex

/-!
# Dependence of linear initial-value problems on parameters

Olver, *Asymptotics and Special Functions*, Chapter 5, Theorems 2.1–2.2,
pp. 143–144. Coefficients need only be continuous in the real independent variable;
parameter derivatives are not replaced by unnecessary time derivatives. Solutions
and their first derivatives are supplied as functions, so the statements apply to
any construction of the initial-value problem.
-/

@[expose] public noncomputable section

open Set

namespace ODE

/-- Joint continuity of a second-order linear initial-value problem with a topological
parameter. Continuity of the coefficients and initial data suffices; no parameter
smoothness is assumed. Olver, Chapter 5, Theorem 2.1, pp. 143–144. -/
theorem continuousOn_parametric_linear_ode {A : Type*} [TopologicalSpace A]
    {U : Set A} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hab : a < b)
    {p q w v : A → ℝ → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (U ×ˢ Icc a b))
    (hq : ContinuousOn (Function.uncurry q) (U ×ˢ Icc a b))
    (h₀ : ContinuousOn (fun u => w u t₀) U)
    (h₁ : ContinuousOn (fun u => v u t₀) U)
    (hode : ∀ u ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (w u) (v u t) (Icc a b) t ∧
      HasDerivWithinAt (v u) (-p u t * v u t - q u t * w u t) (Icc a b) t) :
    ContinuousOn (Function.uncurry w) (U ×ˢ Icc a b) ∧
    ContinuousOn (Function.uncurry v) (U ×ˢ Icc a b) ∧
    ContinuousOn (fun ut => -p ut.1 ut.2 * v ut.1 ut.2 - q ut.1 ut.2 * w ut.1 ut.2)
      (U ×ˢ Icc a b) := by
  sorry

/-- Continuously differentiable real parameter dependence, including the differentiated
inhomogeneous equation and continuity of all three parameter derivatives. The coefficients
need only be continuous in time. Olver, Chapter 5, Theorem 2.1, pp. 143–144. -/
theorem differentiable_parametric_linear_ode {U : Set ℝ} (hU : IsOpen U)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hab : a < b)
    {p q pParam qParam w v : ℝ → ℝ → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (U ×ˢ Icc a b))
    (hq : ContinuousOn (Function.uncurry q) (U ×ˢ Icc a b))
    (hpp : ContinuousOn (Function.uncurry pParam) (U ×ˢ Icc a b))
    (hqp : ContinuousOn (Function.uncurry qParam) (U ×ˢ Icc a b))
    (hdp : ∀ u ∈ U, ∀ t ∈ Icc a b, HasDerivAt (fun u => p u t) (pParam u t) u)
    (hdq : ∀ u ∈ U, ∀ t ∈ Icc a b, HasDerivAt (fun u => q u t) (qParam u t) u)
    (h₀ : DifferentiableOn ℝ (fun u => w u t₀) U)
    (h₁ : DifferentiableOn ℝ (fun u => v u t₀) U)
    (h₀' : ContinuousOn (deriv (fun u => w u t₀)) U)
    (h₁' : ContinuousOn (deriv (fun u => v u t₀)) U)
    (hode : ∀ u ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (w u) (v u t) (Icc a b) t ∧
      HasDerivWithinAt (v u) (-p u t * v u t - q u t * w u t) (Icc a b) t) :
    (∀ t ∈ Icc a b, DifferentiableOn ℝ (fun u => w u t) U ∧
      DifferentiableOn ℝ (fun u => v u t) U ∧
      DifferentiableOn ℝ (fun u => -p u t * v u t - q u t * w u t) U) ∧
    ContinuousOn (fun ut => deriv (fun u => w u ut.2) ut.1) (U ×ˢ Icc a b) ∧
    ContinuousOn (fun ut => deriv (fun u => v u ut.2) ut.1) (U ×ˢ Icc a b) ∧
    ContinuousOn
      (fun ut => deriv (fun u => -p u ut.2 * v u ut.2 - q u ut.2 * w u ut.2) ut.1)
      (U ×ˢ Icc a b) ∧
    ∀ u ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun t => deriv (fun u => w u t) u)
        (deriv (fun u => v u t) u) (Icc a b) t ∧
      HasDerivWithinAt (fun t => deriv (fun u => v u t) u)
        (-p u t * deriv (fun u => v u t) u - q u t * deriv (fun u => w u t) u -
          pParam u t * v u t - qParam u t * w u t) (Icc a b) t := by
  sorry

/-- Holomorphic parameter dependence with a real independent variable and only
continuous time coefficients. Unlike an affine-parameter specialization, this allows
arbitrary jointly continuous holomorphic coefficient families and holomorphic initial
data. Olver, Chapter 5, Theorem 2.2, p. 144. -/
theorem differentiable_complex_parametric_linear_ode {U : Set ℂ} (hU : IsOpen U)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hab : a < b)
    {p q w v : ℂ → ℝ → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (U ×ˢ Icc a b))
    (hq : ContinuousOn (Function.uncurry q) (U ×ˢ Icc a b))
    (hpu : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun u => p u t) U)
    (hqu : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun u => q u t) U)
    (h₀ : DifferentiableOn ℂ (fun u => w u t₀) U)
    (h₁ : DifferentiableOn ℂ (fun u => v u t₀) U)
    (hode : ∀ u ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (w u) (v u t) (Icc a b) t ∧
      HasDerivWithinAt (v u) (-p u t * v u t - q u t * w u t) (Icc a b) t) :
    ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun u => w u t) U ∧
      DifferentiableOn ℂ (fun u => v u t) U ∧
      DifferentiableOn ℂ (fun u => -p u t * v u t - q u t * w u t) U := by
  sorry

end ODE
