/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerM
public import DLMFMathlib.Analysis.Complex.BarnesContour
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Kummer Barnes integrals with finite pole-separating deformations

Kristensson, *Second Order Differential Equations*, Chapter 7, Theorem 7.2,
p. 127. The full admissible upper-parameter range is retained through a contour
with finite deformations; a straight separating line need not exist. The
regularized normalization permits every lower parameter, including reciprocal
Gamma zeros. Absolute convergence and locally uniform truncation are explicit.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Real Topology

namespace DLMF.Confluent

/-- The Kummer Barnes kernel. The contour avoids the two numerator pole families;
`(-z)^s` uses the principal logarithm on the left-half-plane argument domain.
Kristensson, Chapter 7, Theorem 7.2, p. 127. -/
def kummerBarnesIntegrand (a c z s : ℂ) : ℂ :=
  Gamma (a + s) * Gamma (-s) / Gamma (c + s) * (-z) ^ s

/-- The defining Gamma quotient for the Kummer Barnes kernel. -/
theorem kummerBarnesIntegrand_def (a c z s : ℂ) :
    kummerBarnesIntegrand a c z s =
      Gamma (a + s) * Gamma (-s) / Gamma (c + s) * (-z) ^ s := rfl

/-- The exact polynomial and exponential factors controlling the Kummer vertical
tails, uniformly on proper closed subsectors. Kristensson, Chapter 7,
Theorem 7.2, p. 127, using the Barnes convergence estimates of Chapter 5. -/
theorem exists_norm_kummerBarnesIntegrand_vertical_le (a c : ℂ) (σ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) :
    ∃ M Y : ℝ, 0 < M ∧ 1 ≤ Y ∧ ∀ z : ℂ, z.re < 0 →
      |arg (-z)| ≤ Real.pi / 2 - δ → ∀ y : ℝ, Y ≤ |y| →
        ‖kummerBarnesIntegrand a c z ((σ : ℂ) + I * y)‖ ≤
          M * ‖z‖ ^ σ * |y| ^ ((a - c).re - σ - 1 / 2) *
            Real.exp (-δ * |y|) := by
  sorry

/-- Absolute convergence of the complete deformed Kummer Barnes integral.
Kristensson, Chapter 7, Theorem 7.2, p. 127. -/
theorem isIntegrable_kummerBarnesIntegrand {a c z : ℂ}
    (C : BarnesContour ![a] ![(0 : ℂ)]) (hz : z.re < 0) :
    C.IsIntegrable (kummerBarnesIntegrand a c z) := by
  sorry

/-- Barnes's representation for the regularized Kummer function on its full
left-half-plane argument domain. Multiplying by `Gamma(c)` gives the ordinary
book normalization at admissible lower parameters. Kristensson, Chapter 7,
Theorem 7.2, p. 127. -/
theorem regularizedHGFun_eq_kummerBarnesContour {a c z : ℂ}
    (C : BarnesContour ![a] ![(0 : ℂ)]) (hz : z.re < 0) :
    regularizedHGFun {a} {c} z =
      C.integral (kummerBarnesIntegrand a c z) / (2 * Real.pi * I * Gamma a) := by
  sorry

/-- The deformed Kummer Barnes integrals converge locally uniformly in the
argument on the left half-plane. Kristensson, Chapter 7, Theorem 7.2, p. 127. -/
theorem tendstoLocallyUniformlyOn_kummerBarnesContour {a c : ℂ}
    (C : BarnesContour ![a] ![(0 : ℂ)]) :
    TendstoLocallyUniformlyOn
      (fun T : ℝ => fun z : ℂ => C.partialIntegral (kummerBarnesIntegrand a c z) T)
      (fun z : ℂ => C.integral (kummerBarnesIntegrand a c z)) atTop
      {z : ℂ | z.re < 0} := by
  sorry

end DLMF.Confluent
