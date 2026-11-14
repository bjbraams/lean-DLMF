/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic

/-!
# Relative errors in a quotient

The normed-field estimate underlying the nonvanishing error denominator in
Olver, *Asymptotics and Special Functions*, Chapter 13, §4,
pp. 483–486, synopsis O-13.02. Both numerator and denominator errors
are retained in the resulting bound.
-/

@[expose] public section

/-- A quotient of two relative errors has controlled error whenever the
perturbed denominator stays in the open unit ball about one.
Olver, Chapter 13, §4, pp. 483–486. -/
theorem norm_div_relativeError_sub_one_le {K : Type*} [NormedField K]
    {ε η : K} (hη : ‖η‖ < 1) :
    ‖(1 + ε) / (1 + η) - 1‖ ≤ (‖ε‖ + ‖η‖) / (1 - ‖η‖) := by
  have hden : 1 - ‖η‖ ≤ ‖1 + η‖ := by
    simpa only [norm_one, norm_neg, sub_neg_eq_add] using
      norm_sub_norm_le (1 : K) (-η)
  have hpositive : 0 < ‖1 + η‖ := lt_of_lt_of_le (sub_pos.mpr hη) hden
  have hne : (1 : K) + η ≠ 0 := norm_pos_iff.mp hpositive
  have hid : (1 + ε) / (1 + η) - 1 = (ε - η) / (1 + η) := by
    field_simp [hne]
    ring
  rw [hid, norm_div]
  exact div_le_div₀ (add_nonneg (norm_nonneg ε) (norm_nonneg η))
    (norm_sub_le ε η) (sub_pos.mpr hη) hden
