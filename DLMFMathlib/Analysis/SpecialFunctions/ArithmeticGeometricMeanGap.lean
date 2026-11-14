/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import Mathlib.Tactic

/-!
# The exact quadratic arithmetic-geometric mean gap

Temme, *Special Functions* (1996), Chapter 12, equations (12.5)–(12.8), p. 318.
The one-step identity applies at every index of the canonical AGM sequences.
-/

@[expose] public noncomputable section

namespace Real

/-- The difference of the arithmetic and geometric means is exactly quadratic in the
input gap. Temme (12.5)–(12.8), synopsis TEM-12-03. -/
theorem add_div_two_sub_sqrt_mul_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) / 2 - sqrt (a * b) =
      (a - b) ^ 2 / (2 * (sqrt a + sqrt b) ^ 2) := by
  have hsa := sq_sqrt ha.le
  have hsb := sq_sqrt hb.le
  have hs : sqrt a + sqrt b ≠ 0 := ne_of_gt (by positivity)
  have hfactor : a - b = (sqrt a - sqrt b) * (sqrt a + sqrt b) := by
    nlinarith
  calc
    _ = (sqrt a - sqrt b) ^ 2 / 2 := by rw [sqrt_mul ha.le]; nlinarith
    _ = _ := by rw [hfactor, mul_pow]; field_simp

/-- A positive lower bound on the smaller input gives an explicit quadratic gap bound.
Temme (12.5)–(12.8), synopsis TEM-12-03. -/
theorem add_div_two_sub_sqrt_mul_le {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    (a + b) / 2 - sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  rw [add_div_two_sub_sqrt_mul_eq (hb.trans_le hab) hb]
  have hs : sqrt b ≤ sqrt a := sqrt_le_sqrt hab
  have hsb := sq_sqrt hb.le
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith [sqrt_nonneg a, sqrt_nonneg b]

end Real
