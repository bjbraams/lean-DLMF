/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Uniform logarithmic zeta bounds near the line Re s = 1

Andrews, Askey and Roy, *Special Functions*, Theorem D.3.1. The left edge is
allowed to move by a fixed multiple of 1/log|t|. The constant and threshold
are uniform throughout that region.
-/

@[expose] public section

namespace DLMF.Zeta

/-- Zeta and its first derivative have logarithmic and squared-logarithmic bounds
uniformly in a shrinking left neighborhood of Re s=1. Andrews–Askey–Roy,
*Special Functions*, Theorem D.3.1 (synopsis AAR-D.2.1–D.3.2). -/
theorem exists_riemannZeta_log_bounds_near_one {A : ℝ} (hA : 0 < A) :
    ∃ C T : ℝ, 0 < C ∧ 1 < T ∧ ∀ t : ℝ, T ≤ |t| →
      ∀ σ : ℝ, 1 - A / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ C * Real.log |t| ∧
        ‖deriv riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ C * Real.log |t| ^ 2 := by
  sorry

end DLMF.Zeta
