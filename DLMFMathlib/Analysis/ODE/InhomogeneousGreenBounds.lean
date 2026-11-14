/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.InhomogeneousExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Uniform bounds for two-ended inhomogeneous errors

The complementary solutions enter through explicit product majorants and their
Wronskian. An `L1` residual gives the general extra inverse-parameter power;
retaining exponential decay gives the sharper additional power for a bounded
residual. These hypotheses are directly checkable from the progressive-path LG
bounds. Source: Olver, *Asymptotics and Special Functions*, Chapter 10,
§10, (10.04)–(10.09), pp. 386–388.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Real

namespace Complex

/-- The two endpoint variation-of-parameters error, integrating each path
outward from the evaluation point. The residual coefficient is `G_N`.
Olver, Chapter 10, (10.04), p. 387. -/
def inhomogeneousTwoTailError (W₁ W₂ G : ℂ → ℂ)
    (path₁ path₂ : ℝ → ℂ) (u wr z : ℂ) (N : ℕ) : ℂ :=
  (W₂ z * (∫ t in Ioi (0 : ℝ), W₁ (path₁ t) * G (path₁ t) * deriv path₁ t) -
    W₁ z * (∫ t in Ioi (0 : ℝ), W₂ (path₂ t) * G (path₂ t) * deriv path₂ t)) /
      (u ^ (2 * N) * wr)

/-- The defining two-ended integral error. The path tangents are the actual derivatives
of the supplied parametrizations. -/
theorem inhomogeneousTwoTailError_def (W₁ W₂ G : ℂ → ℂ)
    (path₁ path₂ : ℝ → ℂ) (u wr z : ℂ) (N : ℕ) :
    inhomogeneousTwoTailError W₁ W₂ G path₁ path₂ u wr z N =
      (W₂ z * (∫ t in Ioi (0 : ℝ), W₁ (path₁ t) * G (path₁ t) * deriv path₁ t) -
        W₁ z * (∫ t in Ioi (0 : ℝ), W₂ (path₂ t) * G (path₂ t) * deriv path₂ t)) /
          (u ^ (2 * N) * wr) := rfl

/-- Integrable residuals give the general `abs(u)^(-2*N-1)` bound uniformly in
the evaluation point whenever the displayed constants are uniform.
Olver, Chapter 10, §10, pp. 386–388. -/
theorem norm_inhomogeneousTwoTailError_le_of_integrable
    {W₁ W₂ G : ℂ → ℂ} {path₁ path₂ : ℝ → ℂ} {u wr z : ℂ}
    {C M c : ℝ} (N : ℕ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hc : 0 < c) (hu : u ≠ 0)
    (hwr : c * ‖u‖ ≤ ‖wr‖)
    (hI₁ : IntegrableOn (fun t => W₁ (path₁ t) * G (path₁ t) * deriv path₁ t) (Ioi 0))
    (hI₂ : IntegrableOn (fun t => W₂ (path₂ t) * G (path₂ t) * deriv path₂ t) (Ioi 0))
    (hG₁ : IntegrableOn (fun t => ‖G (path₁ t)‖ * ‖deriv path₁ t‖) (Ioi 0))
    (hG₂ : IntegrableOn (fun t => ‖G (path₂ t)‖ * ‖deriv path₂ t‖) (Ioi 0))
    (hM₁ : (∫ t in Ioi (0 : ℝ), ‖G (path₁ t)‖ * ‖deriv path₁ t‖) ≤ M)
    (hM₂ : (∫ t in Ioi (0 : ℝ), ‖G (path₂ t)‖ * ‖deriv path₂ t‖) ≤ M)
    (hW₁ : ∀ t : ℝ, 0 < t → ‖W₂ z * W₁ (path₁ t)‖ ≤ C)
    (hW₂ : ∀ t : ℝ, 0 < t → ‖W₁ z * W₂ (path₂ t)‖ ≤ C) :
    ‖inhomogeneousTwoTailError W₁ W₂ G path₁ path₂ u wr z N‖ ≤
      2 * C * M / (c * ‖u‖ ^ (2 * N + 1)) := by
  sorry

/-- Exponential complementary-product estimates give the sharper
`abs(u)^(-2*N-2)` bound for bounded residuals. The decay rate is retained
explicitly, so no assertion of uniformity over degenerating paths is implicit.
Olver, Chapter 10, (10.08)–(10.09), pp. 387–388. -/
theorem norm_inhomogeneousTwoTailError_le_of_exponential
    {W₁ W₂ G : ℂ → ℂ} {path₁ path₂ : ℝ → ℂ} {u wr z : ℂ}
    {C M c a : ℝ} (N : ℕ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hc : 0 < c) (ha : 0 < a) (hu : u ≠ 0) (hwr : c * ‖u‖ ≤ ‖wr‖)
    (hI₁ : IntegrableOn (fun t => W₁ (path₁ t) * G (path₁ t) * deriv path₁ t) (Ioi 0))
    (hI₂ : IntegrableOn (fun t => W₂ (path₂ t) * G (path₂ t) * deriv path₂ t) (Ioi 0))
    (hG₁ : ∀ t : ℝ, 0 < t → ‖G (path₁ t)‖ * ‖deriv path₁ t‖ ≤ M)
    (hG₂ : ∀ t : ℝ, 0 < t → ‖G (path₂ t)‖ * ‖deriv path₂ t‖ ≤ M)
    (hW₁ : ∀ t : ℝ, 0 < t →
      ‖W₂ z * W₁ (path₁ t)‖ ≤ C * Real.exp (-a * ‖u‖ * t))
    (hW₂ : ∀ t : ℝ, 0 < t →
      ‖W₁ z * W₂ (path₂ t)‖ ≤ C * Real.exp (-a * ‖u‖ * t)) :
    ‖inhomogeneousTwoTailError W₁ W₂ G path₁ path₂ u wr z N‖ ≤
      2 * C * M / (c * a * ‖u‖ ^ (2 * N + 2)) := by
  sorry

end Complex
