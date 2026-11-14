/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lipschitz transfer of asymptotic errors

A quantitative scaled error transfers through a Lipschitz inverse without losing
its constants or uniformity in an external index. This is the elementary
inverse-coordinate step in Olver, *Asymptotics and Special Functions*,
Chapter 11, §6, pp. 405–408, after the perturbed Airy zero displacement estimate.
-/

@[expose] public section

open Filter Set Asymptotics NNReal

namespace LipschitzOnWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- A Lipschitz map preserves a big-O difference whenever both arguments
are eventually in its domain. This is the inverse-coordinate step used in
Olver, Chapter 11, §6, pp. 405–408. -/
theorem isBigO_sub_comp {ι : Type*} {l : Filter ι} {s : Set E} {C : ℝ≥0}
    {X : E → F} (hX : LipschitzOnWith C X s) {f g : ι → E} {r : ι → ℝ}
    (hf : ∀ᶠ i in l, f i ∈ s) (hg : ∀ᶠ i in l, g i ∈ s)
    (h : (fun i => f i - g i) =O[l] r) :
    (fun i => X (f i) - X (g i)) =O[l] r := by
  have hcomp : (fun i => X (f i) - X (g i)) =O[l] (fun i => f i - g i) :=
    IsBigO.of_bound C <| by
      filter_upwards [hf, hg] with i hfi hgi
      simpa only [dist_eq_norm] using hX.dist_le_mul (f i) hfi (g i) hgi
  exact hcomp.trans h

/-- An error in `r*x-y` transfers through a Lipschitz map with the explicit
factor `1/r`. Applying `r=u^(2/3)` to an `O(1/u)` Airy zero displacement
therefore gives `O(u^(-5/3))`, uniformly in any index for which the hypotheses
hold with the same constants. -/
theorem norm_sub_le_of_mul_sub_le {s : Set ℝ} {C : ℝ≥0} {X : ℝ → F}
    (hX : LipschitzOnWith C X s) {x y r δ : ℝ} (hr : 0 < r)
    (hx : x ∈ s) (hy : y / r ∈ s) (herror : ‖r * x - y‖ ≤ δ) :
    ‖X x - X (y / r)‖ ≤ C * δ / r := by
  have heq : r * (x - y / r) = r * x - y := by field_simp
  have hn : ‖r * x - y‖ = r * ‖x - y / r‖ := by
    rw [← heq, norm_mul, Real.norm_of_nonneg hr.le]
  have hscaled : ‖x - y / r‖ ≤ δ / r := by
    apply (le_div_iff₀ hr).2
    nlinarith [herror]
  have hdist := hX.dist_le_mul x hx (y / r) hy
  rw [dist_eq_norm, dist_eq_norm] at hdist
  calc
    ‖X x - X (y / r)‖ ≤ C * ‖x - y / r‖ := hdist
    _ ≤ C * (δ / r) := mul_le_mul_of_nonneg_left hscaled C.coe_nonneg
    _ = C * δ / r := by ring

end LipschitzOnWith
