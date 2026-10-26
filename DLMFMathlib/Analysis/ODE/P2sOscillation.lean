/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import DLMFMathlib.Analysis.ODE.SturmComparison

/-!
# Oscillation of solutions with a coefficient tending to `+∞`

If `v'' + P(x) v = 0` on `ℝ` with `P(x) → +∞` as `x → +∞`, then `v` has infinitely many
positive zeros (`ODE.p2s_infinite_zeros_of_tendsto_atTop`). Beyond the point where `P > 1`,
the Sturm comparison theorem against `sin (x - c)` gives a zero of `v` in every interval
`(c, c + π)`.
-/

@[expose] public section

open Set Filter Topology Real

namespace ODE

/-- **Oscillation.** Let `v'' = -P v` on `ℝ` with `P(x) → +∞` as `x → +∞`. Then `v` has
infinitely many positive zeros. -/
theorem p2s_infinite_zeros_of_tendsto_atTop {P v v' : ℝ → ℝ} (hP : Tendsto P atTop atTop)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (-(P x * v x)) x) :
    {x : ℝ | 0 < x ∧ v x = 0}.Infinite := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hP.eventually_gt_atTop 1)
  set Y := max Y₀ 0
  have hzero : ∀ j : ℕ, ∃ x ∈ Ioo (Y + j * π) (Y + (j + 1) * π), v x = 0 := by
    intro j
    set c := Y + j * π
    have hc : Y + (j + 1) * π = c + π := by simp only [c]; ring
    rw [hc]
    refine sturm_comparison_strict (p := fun _ => 1) (q₁ := fun _ => 1) (q₂ := P)
      (u := fun x => sin (x - c)) (u' := fun x => cos (x - c)) (by linarith [pi_pos])
      (fun x _ => ?_) (fun x _ => ?_) (fun x _ => hv x) (fun x _ => ?_) zero_le_one zero_le_one
      (fun x hx => ?_) (by simp) (by simp) (fun x hx => ?_)
    · simpa using ((hasDerivAt_id x).sub_const c).sin
    · simpa using ((hasDerivAt_id x).sub_const c).cos
    · simpa using hv' x
    · refine hY₀ x ?_
      have : (0 : ℝ) ≤ j * π := by positivity
      linarith [hx.1, le_max_left Y₀ 0]
    · exact (sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne'
  choose z hz hz0 using hzero
  have hmono : StrictMono z := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    have h1 := (hz j).2
    have h2 := (hz (j + 1)).1
    push_cast at h2
    linarith
  refine Set.infinite_of_injective_forall_mem hmono.injective fun j => ⟨?_, hz0 j⟩
  have : (0 : ℝ) ≤ j * π := by positivity
  linarith [(hz j).1, le_max_right Y₀ 0]

end ODE
