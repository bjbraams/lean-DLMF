/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Real analytic regularity of linear differential equations

Duverney, *An Introduction to Hypergeometric Functions*, Appendix B, Theorem B.13
and Corollary B.14. Analytic matrix coefficients force a differentiable solution to be
analytic. The scalar higher-order equation is the companion-system corollary.
-/

@[expose] public noncomputable section

open Set Finset
open scoped Matrix

namespace ODE

/-- Solutions of real linear systems with analytic matrix coefficients are analytic.
Duverney Appendix B, Theorem B.13, equation (B.12), synopsis DU-B.07. -/
theorem analyticOnNhd_of_hasDerivAt_matrix_mulVec {U : Set ℝ} (hU : IsOpen U)
    {m : ℕ} {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) U)
    {y : ℝ → Fin m → ℝ} (hy : ∀ x ∈ U, HasDerivAt y (A x *ᵥ y x) x) :
    AnalyticOnNhd ℝ y U := by
  sorry

/-- A smooth solution of a monic scalar equation with analytic coefficients is analytic.
Duverney Appendix B, Corollary B.14, equation (B.16), synopsis DU-B.07. -/
theorem analyticOnNhd_of_iteratedDeriv_eq_sum {U : Set ℝ} (hU : IsOpen U)
    {n : ℕ} (hn : 1 ≤ n) {a : ℕ → ℝ → ℝ}
    (ha : ∀ k < n, AnalyticOnNhd ℝ (a k) U) {y : ℝ → ℝ}
    (hy : ContDiffOn ℝ n y U)
    (hode : ∀ x ∈ U, iteratedDeriv n y x +
      ∑ k ∈ range n, a k x * iteratedDeriv k y x = 0) :
    AnalyticOnNhd ℝ y U := by
  sorry

end ODE
