/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.CutPlane
public import DLMFMathlib.Analysis.Complex.BarnesContour
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Gauss Barnes integrals with finite pole-separating deformations

Kristensson, *Second Order Differential Equations*, Chapter 5, Theorem 5.4 and
Lemmas 5.4–5.5, pp. 80–84; Olver, *Asymptotics and Special Functions*,
Chapter 8, §6, pp. 299–302. These statements retain the full cut, arbitrary
admissible parameter real parts, absolute tail estimates, local uniform convergence
and the separately specified residue series. The regularized normalization permits
all lower parameters, including zeros of reciprocal Gamma.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Real Topology

namespace DLMF.Hypergeometric

/-- The Gauss Barnes kernel with principal `(-z)^s`. Application theorems place
`-z` in the slit plane and keep numerator Gamma poles off the contour.
Kristensson, Chapter 5, (5.9), pp. 80–84; Olver, Chapter 8, §6, p. 299. -/
def barnesIntegrand (a b c z s : ℂ) : ℂ :=
  Gamma (a + s) * Gamma (b + s) * Gamma (-s) / Gamma (c + s) * (-z) ^ s

/-- The defining Gamma quotient of the Gauss Barnes kernel. -/
theorem barnesIntegrand_def (a b c z s : ℂ) :
    barnesIntegrand a b c z s =
      Gamma (a + s) * Gamma (b + s) * Gamma (-s) / Gamma (c + s) * (-z) ^ s := rfl

/-- The explicit vertical-tail bound is uniform on every proper closed argument
subsector. The factor `norm(z)^sigma` is retained, so the bound is valid for all
nonzero moduli. Kristensson, Lemmas 5.4–5.5, pp. 80–84. -/
theorem exists_norm_barnesIntegrand_vertical_le (a b c : ℂ) (σ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    ∃ M Y : ℝ, 0 < M ∧ 1 ≤ Y ∧ ∀ z : ℂ, -z ∈ slitPlane →
      |arg (-z)| ≤ Real.pi - δ → ∀ y : ℝ, Y ≤ |y| →
        ‖barnesIntegrand a b c z ((σ : ℂ) + I * y)‖ ≤
          M * ‖z‖ ^ σ * |y| ^ ((a + b - c).re - 1) * Real.exp (-δ * |y|) := by
  sorry

/-- Absolute convergence on every finite-deformation pole-separating Barnes contour.
Kristensson, Theorem 5.4 and Lemmas 5.4–5.5, pp. 80–84. -/
theorem isIntegrable_barnesIntegrand {a b c z : ℂ}
    (C : BarnesContour ![a, b] ![(0 : ℂ)]) (hz : -z ∈ slitPlane) :
    C.IsIntegrable (barnesIntegrand a b c z) := by
  sorry

/-- Barnes's complete representation for the principal regularized Gauss function,
with arbitrary finite contour deformations and vertical tails. Integer differences
of the upper parameters are allowed; opposite pole coincidences cannot satisfy
the contour-separation data. Kristensson, Theorem 5.4, pp. 80–84; Olver,
Chapter 8, §6, pp. 299–302. -/
theorem regularizedGaussHypergeometric_eq_barnesContour {a b c z : ℂ}
    (C : BarnesContour ![a, b] ![(0 : ℂ)]) (hz : -z ∈ slitPlane) :
    regularizedGaussHypergeometric a b c z =
      C.integral (barnesIntegrand a b c z) / (2 * Real.pi * I * Gamma a * Gamma b) := by
  sorry

/-- Truncated deformed Barnes integrals converge locally uniformly on the complete
cut, rather than only at one negative real argument. Kristensson, Theorem 5.4 and
Lemma 5.4, pp. 80–84. -/
theorem tendstoLocallyUniformlyOn_barnesContour {a b c : ℂ}
    (C : BarnesContour ![a, b] ![(0 : ℂ)]) :
    TendstoLocallyUniformlyOn
      (fun T : ℝ => fun z : ℂ => C.partialIntegral (barnesIntegrand a b c z) T)
      (fun z : ℂ => C.integral (barnesIntegrand a b c z)) atTop
      {z : ℂ | -z ∈ slitPlane} := by
  sorry

/-- Closing to the right produces the explicit Gamma residue series in the unit
disc. The orientation sign cancels the sign of `Res Gamma(-s)` and produces `z^n`.
This statement is separate from the vertical tail estimate. Kristensson,
Lemma 5.5, pp. 80–84; Olver, Chapter 8, §6, pp. 299–302. -/
theorem hasSum_barnesContour_right_residues {a b c z : ℂ}
    (C : BarnesContour ![a, b] ![(0 : ℂ)]) (hz : -z ∈ slitPlane) (hz₁ : ‖z‖ < 1) :
    HasSum (fun n : ℕ => Gamma (a + n) * Gamma (b + n) / Gamma (c + n) *
      z ^ n / n.factorial) (C.integral (barnesIntegrand a b c z) / (2 * Real.pi * I)) := by
  sorry

end DLMF.Hypergeometric
