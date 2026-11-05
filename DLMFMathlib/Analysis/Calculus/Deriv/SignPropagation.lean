/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.Instances.Sign

/-!
# Propagating the sign of a differentiable function

A positive derivative at a zero fixes the positive sign throughout a right interval on which
a continuous real function has no further zero.
-/

public section

open Filter Set
open scoped Topology

/-- A positive derivative at zero forces positivity throughout a right interval with no zeros. -/
theorem pos_of_deriv_pos_of_continuousOn_of_ne_zero {f : ℝ → ℝ} {R : ℝ}
    (hc : ContinuousOn f (Ioo 0 R)) (hne : ∀ x ∈ Ioo 0 R, f x ≠ 0)
    (hf0 : f 0 = 0) (hd : deriv f 0 > 0) {x : ℝ} (hx : x ∈ Ioo 0 R) : 0 < f x := by
  have hsgn := eventually_nhdsWithin_sign_eq_of_deriv_pos hd hf0
  obtain ⟨δ, hδ, hsgn⟩ := Metric.eventually_nhds_iff.mp hsgn
  have hx0 := hx.1
  let y : ℝ := min δ x / 2
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hyx : y < x := by dsimp [y]; linarith [min_le_right δ x]
  have hyδ : y < δ := by dsimp [y]; linarith [min_le_left δ x]
  have hy : y ∈ Ioo 0 R := ⟨hy0, hyx.trans hx.2⟩
  have hs := hsgn (show dist y 0 < δ by simpa [Real.dist_eq, abs_of_pos hy0] using hyδ)
  have he := isPreconnected_Ioo.sign_eq_of_continuousOn hc hne hx hy
  rw [hs] at he
  exact sign_eq_one_iff.mp (by simpa [sign_pos hy0] using he)
