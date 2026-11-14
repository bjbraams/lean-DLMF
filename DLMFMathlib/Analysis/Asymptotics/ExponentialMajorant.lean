/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.Real

/-!
# Uniform inverse-parameter and vanishing exponential majorants

Olver, *Asymptotics and Special Functions*, Chapter 6, §5, pp. 203–206,
synopsis O-6.07. These elementary transfers apply simultaneously to the
relative error and its normalized derivative, on bounded or unbounded index sets.
The control variation may itself depend on the large parameter.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Real

/-- A computable inverse-parameter bound for a nonnegative exponential control.
Olver, Chapter 6, §5, synopsis O-6.07. -/
theorem exp_div_sub_one_le_two_div {V u : ℝ} (hV : 0 ≤ V) (hu : max 1 V ≤ u) :
    exp (V / u) - 1 ≤ 2 * V / u := by
  have hu' : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hu)
  have hVu : 0 ≤ V / u := div_nonneg hV hu'.le
  have hVu' : V / u ≤ 1 := (div_le_one hu').mpr (le_trans (le_max_right _ _) hu)
  have h := abs_exp_sub_one_le (x := V / u) (by rwa [abs_of_nonneg hVu])
  calc
    exp (V / u) - 1 ≤ |exp (V / u) - 1| := le_abs_self _
    _ ≤ 2 * |V / u| := h
    _ = 2 * V / u := by rw [abs_of_nonneg hVu]; ring

/-- A bounded error-control variation gives a bound uniform in an arbitrary index set.
Olver, Chapter 6, §5, synopsis O-6.07. -/
theorem norm_le_inv_parameter_of_exp_control {X E : Type*} [SeminormedAddCommGroup E]
    {ε : ℝ → X → E} {V : ℝ → ℝ} {C u₀ : ℝ}
    (hV : ∀ u ≥ u₀, 0 ≤ V u ∧ V u ≤ C)
    (hε : ∀ u ≥ u₀, ∀ x, ‖ε u x‖ ≤ exp (V u / u) - 1) :
    ∀ u ≥ max u₀ (max 1 C), ∀ x, ‖ε u x‖ ≤ 2 * C / u := by
  intro u hu x
  have hu₀ : u₀ ≤ u := le_trans (le_max_left _ _) hu
  have huC : max 1 C ≤ u := le_trans (le_max_right _ _) hu
  have hpos : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) huC)
  calc
    ‖ε u x‖ ≤ exp (V u / u) - 1 := hε u hu₀ x
    _ ≤ 2 * V u / u := exp_div_sub_one_le_two_div (hV u hu₀).1
      ((max_le_max le_rfl (hV u hu₀).2).trans huC)
    _ ≤ 2 * C / u := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hV u hu₀).2 (by norm_num)) hpos.le

/-- Sublinear parameter-dependent variation gives uniformly vanishing errors on an
arbitrary index set. The quotient condition is precisely `V(u)=o(u)` as `u→∞`.
Olver, Chapter 6, §5, synopsis O-6.07. -/
theorem eventually_norm_lt_of_exp_control {X E : Type*} [SeminormedAddCommGroup E]
    {ε : ℝ → X → E} {V : ℝ → ℝ} {S : Set X}
    (hV : Tendsto (fun u => V u / u) atTop (𝓝 0))
    (hε : ∀ u > 0, ∀ x ∈ S, ‖ε u x‖ ≤ exp (V u / u) - 1) :
    ∀ η > 0, ∀ᶠ u : ℝ in atTop, ∀ x ∈ S, ‖ε u x‖ < η := by
  have hlim : Tendsto (fun u => exp (V u / u) - 1) atTop (𝓝 0) := by
    simpa using ((continuous_exp.continuousAt.tendsto.comp hV).sub_const 1)
  intro η hη
  filter_upwards [hlim.eventually_lt_const hη, eventually_gt_atTop (0 : ℝ)] with u hu hupos
  intro x hx
  exact lt_of_le_of_lt (hε u hupos x hx) hu

end Real
