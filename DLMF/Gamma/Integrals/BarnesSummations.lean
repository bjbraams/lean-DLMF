/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Barnes's second lemma and very-well-poised Barnes integrals

Andrews, Askey and Roy, *Special Functions*, Theorems 2.4.3, 3.6.1 and 3.6.3.
Vertical contours are oriented upward. Integration in the real height variable
absorbs the factor i in ds, leaving the normalization 1/(2π).
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace DLMF.Gamma

namespace BarnesProducts

/-- A ratio of Gamma blocks along a vertical line. Lists retain repeated parameters.
Andrews–Askey–Roy, *Special Functions*, §§2.4, 3.6
(synopsis AAR-2.4.1–2.4.6 and AAR-3.6.1–3.8.2). -/
def verticalKernel (A B C D : List ℂ) (σ t : ℝ) : ℂ :=
  ((A.map fun a => Complex.Gamma (a + σ + Complex.I * t)).prod *
    (B.map fun b => Complex.Gamma (b - σ - Complex.I * t)).prod) /
  ((C.map fun c => Complex.Gamma (c + σ + Complex.I * t)).prod *
    (D.map fun d => Complex.Gamma (d - σ - Complex.I * t)).prod)

/-- The Gamma-product kernel on the chosen vertical line. -/
theorem verticalKernel_def (A B C D : List ℂ) (σ t : ℝ) :
    verticalKernel A B C D σ t =
      ((A.map fun a => Complex.Gamma (a + σ + Complex.I * t)).prod *
        (B.map fun b => Complex.Gamma (b - σ - Complex.I * t)).prod) /
      ((C.map fun c => Complex.Gamma (c + σ + Complex.I * t)).prod *
        (D.map fun d => Complex.Gamma (d - σ - Complex.I * t)).prod) := rfl

end BarnesProducts

/-- Barnes's second lemma on an explicitly separating vertical line.
Andrews–Askey–Roy, *Special Functions*, Theorem 2.4.3
(synopsis AAR-2.4.1–2.4.6). -/
theorem barnes_second_lemma (a b c d e : ℂ) (σ : ℝ)
    (hplus : ∀ u ∈ [a, b, c], 0 < (u + σ).re)
    (hminus : ∀ u ∈ [d, e], 0 < (u - σ).re) :
    Integrable (BarnesProducts.verticalKernel [a, b, c] [d, e]
      [a + b + c + d + e] [] σ) ∧
    (∫ t : ℝ, BarnesProducts.verticalKernel [a, b, c] [d, e]
      [a + b + c + d + e] [] σ t) / (2 * Real.pi) =
      Complex.Gamma (a + d) * Complex.Gamma (b + d) * Complex.Gamma (c + d) *
        Complex.Gamma (a + e) * Complex.Gamma (b + e) * Complex.Gamma (c + e) /
        (Complex.Gamma (a + b + d + e) * Complex.Gamma (a + c + d + e) *
          Complex.Gamma (b + c + d + e)) := by
  sorry

/-- The very-well-poised seven-Gamma Barnes evaluation.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.6.1
(synopsis AAR-3.6.1–3.8.2). -/
theorem barnes_very_well_poised_seven (a b c d : ℂ) (σ : ℝ)
    (hplus : ∀ u ∈ [a, 1 + a / 2, b, c, d], 0 < (u + σ).re)
    (hminus : ∀ u ∈ [b - a, 0], 0 < (u - σ).re) :
    Integrable (BarnesProducts.verticalKernel [a, 1 + a / 2, b, c, d] [b - a, 0]
      [a / 2, 1 + a - c, 1 + a - d] [] σ) ∧
    (∫ t : ℝ, BarnesProducts.verticalKernel [a, 1 + a / 2, b, c, d] [b - a, 0]
      [a / 2, 1 + a - c, 1 + a - d] [] σ t) / (2 * Real.pi) =
      Complex.Gamma b * Complex.Gamma c * Complex.Gamma d *
        Complex.Gamma (b + c - a) * Complex.Gamma (b + d - a) /
        (2 * Complex.Gamma (1 + a - c - d) * Complex.Gamma (b + c + d - a)) := by
  sorry

/-- The balanced nine-Gamma Barnes evaluation.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.6.3
(synopsis AAR-3.6.1–3.8.2). -/
theorem barnes_balanced_nine (a b c d e f : ℂ) (σ : ℝ)
    (hbalance : 2 * a + 1 = b + c + d + e + f)
    (hplus : ∀ u ∈ [a, 1 + a / 2, b, c, d, e, f], 0 < (u + σ).re)
    (hminus : ∀ u ∈ [b - a, 0], 0 < (u - σ).re) :
    Integrable (BarnesProducts.verticalKernel [a, 1 + a / 2, b, c, d, e, f]
      [b - a, 0] [a / 2, 1 + a - c, 1 + a - d, 1 + a - e, 1 + a - f] [] σ) ∧
    (∫ t : ℝ, BarnesProducts.verticalKernel [a, 1 + a / 2, b, c, d, e, f]
      [b - a, 0] [a / 2, 1 + a - c, 1 + a - d, 1 + a - e, 1 + a - f] [] σ t) /
        (2 * Real.pi) =
      Complex.Gamma b * Complex.Gamma c * Complex.Gamma d * Complex.Gamma e *
        Complex.Gamma f * Complex.Gamma (b + c - a) * Complex.Gamma (b + d - a) *
        Complex.Gamma (b + e - a) * Complex.Gamma (b + f - a) /
        (2 * Complex.Gamma (1 + a - c - d) * Complex.Gamma (1 + a - c - e) *
          Complex.Gamma (1 + a - c - f) * Complex.Gamma (1 + a - d - e) *
          Complex.Gamma (1 + a - d - f) * Complex.Gamma (1 + a - e - f)) := by
  sorry

end DLMF.Gamma
