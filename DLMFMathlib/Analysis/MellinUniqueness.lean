/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform

/-!
# Almost-everywhere uniqueness from one Mellin line

Andrews, Askey and Roy, *Special Functions*, Lemma 10.12.4. Only the positive
half-line is determined by a Mellin transform.
-/

@[expose] public section

namespace MeasureTheory

/-- An absolutely Mellin-integrable function with zero transform on one whole vertical
line vanishes almost everywhere on the positive ray. Andrews–Askey–Roy,
*Special Functions*, Lemma 10.12.4 (synopsis AAR-10.12.1–10.12.8). -/
theorem ae_eq_zero_of_mellin_vertical_eq_zero {f : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f (σ : ℂ))
    (hzero : ∀ t : ℝ, mellin f ((σ : ℂ) + t * Complex.I) = 0) :
    ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)), f x = 0 := by
  sorry

end MeasureTheory
