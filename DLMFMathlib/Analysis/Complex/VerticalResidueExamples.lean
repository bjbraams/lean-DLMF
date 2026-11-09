/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.VerticalResidues
public import DLMFMathlib.Analysis.Complex.LaplaceInversion

/-!
# A rational vertical contour example

The function `1/(z(1-z))` has residue one at zero. Its vertical integral is `2π` on
the line with real part one half and zero on the line with real part minus one half.
These values check the orientation and normalization of vertical contour shifts.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped Topology

namespace Complex

/-- The rational two-pole example has residue one at zero. -/
theorem residue_one_div_mul_one_sub_zero :
    TauCeti.Contour.residue (fun z : ℂ => 1 / (z * (1 - z))) 0 = 1 := by
  have ha : AnalyticAt ℂ (fun z : ℂ => (1 - z)⁻¹) 0 :=
    (analyticAt_const.sub analyticAt_id).inv (by norm_num)
  have he : (fun z : ℂ => 1 / (z * (1 - z))) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => (1 - z)⁻¹ / (z - 0)) :=
    Filter.Eventually.of_forall fun z => by simp [div_eq_mul_inv, mul_comm]
  simpa using residue_eq_of_eventuallyEq_div_sub ha he

/-- On the line `Re z = 1/2`, the rational example integrates to `2π`. -/
theorem integral_vertical_one_div_mul_one_sub_half :
    (∫ y : ℝ, 1 / (((1 / 2 : ℂ) + y * I) * (1 - ((1 / 2 : ℂ) + y * I)))) =
      2 * (Real.pi : ℂ) := by
  have he (y : ℝ) : ((1 / 2 : ℂ) + y * I) * (1 - ((1 / 2 : ℂ) + y * I)) =
      (((1 / 2 : ℝ) ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [I_sq]
  have hf : (fun y : ℝ => 1 / (((1 / 2 : ℂ) + y * I) *
      (1 - ((1 / 2 : ℂ) + y * I)))) =
      (fun y : ℝ => ((((1 / 2 : ℝ) ^ 2 + y ^ 2)⁻¹ : ℝ) : ℂ)) := by
    funext y
    rw [he]
    simp
  rw [hf, integral_complex_ofReal, integral_inv_sq_add_sq (by norm_num : (0 : ℝ) < 1 / 2)]
  push_cast
  ring

/-- On the half-plane to the left of `-1/2`, the denominator factor `1-z` has norm at
least that of `z`, so the rational example has a quadratic bound. -/
theorem norm_one_div_mul_one_sub_le {z : ℂ} (hz : z.re ≤ -(1 / 2 : ℝ)) :
    ‖1 / (z * (1 - z))‖ ≤ 1 / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; subst z; norm_num at hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnorm : ‖z‖ ≤ ‖1 - z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp only [normSq_apply, sub_re, one_re, sub_im, one_im, zero_sub, neg_mul_neg]
    nlinarith
  rw [norm_div, norm_one, norm_mul]
  calc 1 / (‖z‖ * ‖1 - z‖) ≤ 1 / (‖z‖ * ‖z‖) :=
      one_div_le_one_div_of_le (mul_pos hn hn) (mul_le_mul_of_nonneg_left hnorm hn.le)
    _ = _ := by rw [pow_two]

/-- On the line `Re z = -1/2`, the rational example integrates to zero by shifting the
line to the left without crossing a pole. -/
theorem integral_vertical_one_div_mul_one_sub_neg_half :
    (∫ y : ℝ, 1 / (((-(1 / 2) : ℂ) + y * I) *
      (1 - ((-(1 / 2) : ℂ) + y * I)))) = 0 := by
  have he : (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by norm_num
  rw [he]
  apply integral_vertical_eq_zero_of_norm_le'
    (k := fun z : ℂ => 1 / (z * (1 - z))) (d := -(1 / 2))
    (p := 0) (K := 1) (by norm_num)
  · intro z hz
    have hz0 : z ≠ 0 := by intro h; subst z; norm_num at hz
    have h1z : 1 - z ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp at he
      linarith [show z.re ≤ -(1 / 2 : ℝ) from hz]
    have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) z := differentiableAt_const 1
    exact (hconst.div (hid.mul (hconst.sub hid))
      (mul_ne_zero hz0 h1z)).differentiableWithinAt
  · intro z hz
    simpa using norm_one_div_mul_one_sub_le hz

end Complex
