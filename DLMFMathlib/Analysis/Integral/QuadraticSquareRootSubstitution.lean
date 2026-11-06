/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Topology.Order.IntermediateValue

/-!
# A quadratic substitution for a pair of square roots

For nonnegative `y,z`, the map `t ↦ t+√((t+y)(t+z))+p` sends the positive half-line
onto the half-line starting at `√(yz)+p`. Its Jacobian transforms a quadratic reciprocal
kernel into `1/(2√((t+y)(t+z))(t+p))`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Real

namespace MeasureTheory.QuadraticSquareRoot

/-- The increasing substitution determined by two nonnegative square-root shifts. -/
def substitution (y z p t : ℝ) : ℝ := t + √((t + y) * (t + z)) + p

/-- The Jacobian of the pair-root substitution in the positive half-line. -/
def jacobian (y z t : ℝ) : ℝ := 1 + (2 * t + y + z) / (2 * √((t + y) * (t + z)))

/-- The pair-root substitution is continuous. -/
theorem continuous_substitution (y z p : ℝ) : Continuous (substitution y z p) := by
  unfold substitution
  fun_prop

/-- The derivative of the pair-root substitution in the positive half-line. -/
theorem hasDerivAt_substitution {y z p t : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
    HasDerivAt (substitution y z p) (jacobian y z t) t := by
  have hprod : 0 < (t + y) * (t + z) := by positivity
  have H := ((hasDerivAt_id t).add
    ((((hasDerivAt_id t).add_const y).mul ((hasDerivAt_id t).add_const z)).sqrt
      hprod.ne')).add_const p
  convert H using 1
  · funext u
    simp only [substitution, Pi.add_apply, Pi.mul_apply, id_eq]
  · dsimp only [jacobian]
    simp only [Pi.mul_apply, id_eq, mul_one, one_mul]
    ring

/-- The pair-root substitution is monotone on the positive half-line. -/
theorem monotoneOn_substitution {y z p : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    MonotoneOn (substitution y z p) (Ioi 0) := by
  intro t ht u hu htu
  have ht0 : 0 < t := ht
  have hu0 : 0 < u := hu
  have hty : t + y ≤ u + y := by linarith
  have htz : t + z ≤ u + z := by linarith
  have H : (t + y) * (t + z) ≤ (u + y) * (u + z) :=
    mul_le_mul hty htz (by linarith) (by linarith)
  change t + √((t + y) * (t + z)) + p ≤ u + √((u + y) * (u + z)) + p
  linarith [Real.sqrt_le_sqrt H]

/-- The image of the positive half-line under the pair-root substitution. -/
theorem image_substitution_Ioi {y z p : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    substitution y z p '' Ioi 0 = Ioi (√(y * z) + p) := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht0 : 0 < t := ht
    have hroot : √(y * z) ≤ √((t + y) * (t + z)) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    change √(y * z) + p < t + √((t + y) * (t + z)) + p
    linarith
  · intro hu
    have hu0 : √(y * z) + p < u := hu
    have hT : 0 ≤ u - p := by linarith [Real.sqrt_nonneg (y * z)]
    have hleft : substitution y z p 0 ≤ u := by
      simp only [substitution, zero_add]
      exact hu0.le
    have hright : u ≤ substitution y z p (u - p) := by
      unfold substitution
      linarith [Real.sqrt_nonneg ((u - p + y) * (u - p + z))]
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hT
      (continuous_substitution y z p).continuousOn ⟨hleft, hright⟩
    have htpos : 0 < t := by
      have ht0 : 0 ≤ t := ht.1
      by_contra hn
      have htzero : t = 0 := by linarith
      subst t
      simp only [substitution, zero_add] at he
      linarith
    exact ⟨t, htpos, he⟩

/-- The quadratic denominator factorizes after the pair-root substitution. -/
theorem substitution_sq_add {y z p t : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
    substitution y z p t ^ 2 + 2 * ((y + z) / 2 + √(y * z)) * p - (√(y * z) + p) ^ 2 =
      2 * (t + √((t + y) * (t + z)) + (y + z) / 2) * (t + p) := by
  have hprod : 0 ≤ (t + y) * (t + z) := by positivity
  dsimp only [substitution]
  nlinarith [Real.sq_sqrt hprod, Real.sq_sqrt (mul_nonneg hy hz)]

/-- The Jacobian cancels the nonconstant factor of the transformed quadratic kernel. -/
theorem jacobian_div_quadratic {y z p t : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ht : 0 < t) (htp : t + p ≠ 0) :
    jacobian y z t /
      (substitution y z p t ^ 2 + 2 * ((y + z) / 2 + √(y * z)) * p - (√(y * z) + p) ^ 2) =
      1 / (2 * √((t + y) * (t + z)) * (t + p)) := by
  have hprod : 0 < (t + y) * (t + z) := by positivity
  have hroot : 0 < √((t + y) * (t + z)) := Real.sqrt_pos.mpr hprod
  have hsum : 0 < t + √((t + y) * (t + z)) + (y + z) / 2 := by positivity
  rw [substitution_sq_add hy hz ht]
  dsimp only [jacobian]
  field_simp [hroot.ne', hsum.ne', htp]
  ring

end MeasureTheory.QuadraticSquareRoot
