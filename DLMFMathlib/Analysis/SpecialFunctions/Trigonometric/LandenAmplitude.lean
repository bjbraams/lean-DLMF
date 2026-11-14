/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Trigonometric formulas for the Landen amplitude

When `cos φ > 0`, the sine and cosine of `φ + arctan(r tan φ)` are rational expressions
with denominator `sqrt(cos²φ + r²sin²φ)`. Its derivative and the transformed elliptic
square-root factor follow by elementary algebra. The first formulas allow arbitrary real
`r`; the transformed factor assumes `r > 0`.

The proofs use Mathlib's sine, cosine, tangent and arctangent derivative APIs.

* `Real.sin_add_arctan_mul_tan`, `Real.cos_add_arctan_mul_tan`: the transformed sine and cosine.
* `Real.hasDerivAt_add_arctan_mul_tan`: the transformed derivative.
* `Real.sqrt_one_add_mul_tan_sq`, `Real.sqrt_one_sub_landen_mul_sin_sq`: square-root factors.
-/

public noncomputable section
namespace Real
/-- The positive cosine factor converts the tangent square root to a quadratic form. -/
lemma sqrt_one_add_mul_tan_sq {r φ : ℝ} (hc : 0 < Real.cos φ) :
    Real.sqrt (1 + (r * Real.tan φ) ^ 2) =
      Real.sqrt (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) / Real.cos φ := by
  have he : 1 + (r * Real.tan φ) ^ 2 =
      (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) / Real.cos φ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hc.le]
/-- Sine of the Landen amplitude, for any real scale and positive cosine. -/
lemma sin_add_arctan_mul_tan {r φ : ℝ} (hc : 0 < Real.cos φ) :
    Real.sin (φ + Real.arctan (r * Real.tan φ)) =
      (1 + r) * Real.sin φ * Real.cos φ /
        Real.sqrt (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) := by
  have hD : Real.sqrt (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) ≠ 0 := by positivity
  rw [Real.sin_add, Real.sin_arctan, Real.cos_arctan, sqrt_one_add_mul_tan_sq hc,
    Real.tan_eq_sin_div_cos]
  field_simp [hc.ne', hD]
/-- Cosine of the Landen amplitude, for any real scale and positive cosine. -/
lemma cos_add_arctan_mul_tan {r φ : ℝ} (hc : 0 < Real.cos φ) :
    Real.cos (φ + Real.arctan (r * Real.tan φ)) =
      (Real.cos φ ^ 2 - r * Real.sin φ ^ 2) /
        Real.sqrt (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) := by
  have hD : Real.sqrt (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) ≠ 0 := by positivity
  rw [Real.cos_add, Real.sin_arctan, Real.cos_arctan, sqrt_one_add_mul_tan_sq hc,
    Real.tan_eq_sin_div_cos]
  field_simp [hc.ne', hD]
/-- The derivative of the Landen amplitude away from the tangent poles. -/
lemma hasDerivAt_add_arctan_mul_tan {r φ : ℝ} (hc : Real.cos φ ≠ 0) :
    HasDerivAt (fun t : ℝ => t + Real.arctan (r * Real.tan t))
      (1 + r / (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2)) φ := by
  have hD : Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2 ≠ 0 := by positivity
  have hA : 1 + (r * Real.tan φ) ^ 2 ≠ 0 := by positivity
  convert (hasDerivAt_id φ).add (((Real.hasDerivAt_tan hc).const_mul r).arctan) using 1
  · rfl
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hc, hD, hA]
/-- The transformed positive square root under the Landen amplitude substitution. -/
lemma sqrt_one_sub_landen_mul_sin_sq {r φ : ℝ} (hr : 0 < r) (hc : 0 < Real.cos φ) :
    Real.sqrt (1 - ((1 - r) / (1 + r)) ^ 2 *
      Real.sin (φ + Real.arctan (r * Real.tan φ)) ^ 2) =
      (Real.cos φ ^ 2 + r * Real.sin φ ^ 2) /
        Real.sqrt (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) := by
  have hp : 0 < 1 + r := by linarith
  have hα : ((1 - r) / (1 + r)) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    nlinarith [hr]
  have hb : 0 ≤ 1 - ((1 - r) / (1 + r)) ^ 2 *
      Real.sin (φ + Real.arctan (r * Real.tan φ)) ^ 2 := by
    nlinarith [Real.sin_sq_le_one (φ + Real.arctan (r * Real.tan φ)),
      sq_nonneg (Real.sin (φ + Real.arctan (r * Real.tan φ)))]
  have hD : Real.sqrt (Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) ≠ 0 := by positivity
  rw [Real.sqrt_eq_iff_eq_sq hb (by positivity), sin_add_arctan_mul_tan hc]
  field_simp [hp.ne', hD]
  rw [Real.sq_sqrt (by positivity)]
  linear_combination -(Real.cos φ ^ 2 + r ^ 2 * Real.sin φ ^ 2) * Real.sin_sq_add_cos_sq φ
end Real
