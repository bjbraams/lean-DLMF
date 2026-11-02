/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Cauchy integral formula on an annulus and the inner Laurent expansion

For `f` continuous on the closed annulus `r ≤ ‖w - c‖ ≤ R` and holomorphic inside it, and `z`
strictly inside the annulus,
`2πi f(z) = ∮_{|w - c| = R} f(w)/(w - z) dw - ∮_{|w - c| = r} f(w)/(w - z) dw`.
The outer integral expands in powers of `z - c` (Mathlib's
`hasSum_two_pi_I_cauchyPowerSeries_integral`); here the inner integral is expanded in negative
powers of `z - c`. Together these give Laurent's theorem.

## Main results

* `Complex.circleIntegral_sub_inv_mul_annulus`: the Cauchy integral formula on an annulus.
* `Complex.hasSum_circleIntegral_inner`: the expansion of the inner Cauchy integral in negative
  powers.
-/

@[expose] public section

open Set Metric Filter
open scoped Real Topology

namespace Complex

/-- **Cauchy integral formula on an annulus.** If `f` is continuous on the closed annulus
`r ≤ ‖w - c‖ ≤ R` (`0 < r`) and differentiable at every point of the open annulus, then for `z` in
the open annulus `∮_{C(c,R)} (w - z)⁻¹ f(w) dw - ∮_{C(c,r)} (w - z)⁻¹ f(w) dw = 2πi f(z)`. -/
theorem circleIntegral_sub_inv_mul_annulus {f : ℂ → ℂ} {c z : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrz : r < ‖z - c‖) (hzR : ‖z - c‖ < R)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ w ∈ ball c R \ closedBall c r, DifferentiableAt ℂ f w) :
    (∮ w in C(c, R), (w - z)⁻¹ * f w) - (∮ w in C(c, r), (w - z)⁻¹ * f w) =
      2 * π * I * f z := by
  have hrR : r ≤ R := (hrz.trans hzR).le
  have hzA : z ∈ ball c R \ closedBall c r := ⟨by rwa [mem_ball, dist_eq_norm],
    by rw [mem_closedBall, dist_eq_norm, not_le]; exact hrz⟩
  have hfz : DifferentiableAt ℂ f z := hd z hzA
  -- the difference quotient is holomorphic on the annulus
  have hg : (∮ w in C(c, R), dslope f z w) = ∮ w in C(c, r), dslope f z w := by
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
      (countable_singleton z) ?_ ?_
    · intro w hw
      by_cases hwz : w = z
      · subst hwz; exact (continuousAt_dslope_same.mpr hfz).continuousWithinAt
      · have hcw : ContinuousWithinAt (slope f z) (closedBall c R \ ball c r) w := by
          have : ContinuousWithinAt (fun y => (y - z)⁻¹ • (f y - f z))
              (closedBall c R \ ball c r) w :=
            ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.mpr hwz)).smul
              ((hc w hw).sub continuousWithinAt_const)
          refine this.congr (fun y _ => ?_) ?_ <;> simp [slope_def_module]
        refine hcw.congr_of_eventuallyEq ?_ (dslope_of_ne f hwz)
        filter_upwards [self_mem_nhdsWithin, (isOpen_ne.mem_nhds hwz : {y | y ≠ z} ∈ 𝓝 w)
          |> nhdsWithin_le_nhds] with y _ hy using dslope_of_ne f hy
    · intro w hw
      exact (differentiableAt_dslope_of_ne hw.2).mpr (hd w hw.1)
  have hsph : ∀ ρ, ρ ≠ ‖z - c‖ → ∀ w ∈ sphere c ρ, w ≠ z := by
    intro ρ hρ w hw hwz
    rw [mem_sphere, dist_eq_norm, hwz] at hw
    exact hρ hw.symm
  have hexp : ∀ ρ, 0 ≤ ρ → ρ ≠ ‖z - c‖ → ContinuousOn f (sphere c ρ) →
      (∮ w in C(c, ρ), dslope f z w) =
        (∮ w in C(c, ρ), (w - z)⁻¹ * f w) - f z * ∮ w in C(c, ρ), (w - z)⁻¹ := by
    intro ρ hρ0 hρ hfρ
    have hcont : ContinuousOn (fun w => (w - z)⁻¹) (sphere c ρ) := fun w hw =>
      ((continuousAt_id.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr (hsph ρ hρ w hw))).continuousWithinAt
    rw [circleIntegral.integral_congr hρ0 (g := fun w => (w - z)⁻¹ * f w - f z * (w - z)⁻¹)]
    · have hi1 : CircleIntegrable (fun w => (w - z)⁻¹ * f w) c ρ :=
        (hcont.mul hfρ).circleIntegrable hρ0
      have hi2 : CircleIntegrable (fun w => f z * (w - z)⁻¹) c ρ :=
        (continuousOn_const.mul hcont).circleIntegrable hρ0
      rw [circleIntegral.integral_sub hi1 hi2, circleIntegral.integral_const_mul]
    · intro w hw
      rw [dslope_of_ne f (hsph ρ hρ w hw), slope_def_module, smul_eq_mul]
      ring
  have hsR : sphere c R ⊆ closedBall c R \ ball c r := fun w hw =>
    ⟨sphere_subset_closedBall hw, by
      rw [mem_ball, not_lt, (mem_sphere.mp hw)]; exact hrR⟩
  have hsr : sphere c r ⊆ closedBall c R \ ball c r := fun w hw =>
    ⟨closedBall_subset_closedBall hrR (sphere_subset_closedBall hw), by
      rw [mem_ball, not_lt, (mem_sphere.mp hw)]⟩
  have h1 : (∮ w in C(c, R), (w - z)⁻¹) = 2 * π * I :=
    circleIntegral.integral_sub_inv_of_mem_ball hzA.1
  have hzr : z ∉ closedBall c r := hzA.2
  have h2 : (∮ w in C(c, r), (w - z)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      (fun w hw => ?_) (fun w hw => ?_)
    · have hwz : w ≠ z := fun h => hzr (h ▸ hw)
      exact ((continuousAt_id.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr hwz)).continuousWithinAt
    · have hwz : w ≠ z := fun h => hzr (h ▸ ball_subset_closedBall hw.1)
      exact (differentiableAt_id.sub_const z).inv (sub_ne_zero.mpr hwz)
  rw [hexp R (hr.le.trans hrR) hzR.ne' (hc.mono hsR), hexp r hr.le hrz.ne (hc.mono hsr),
    h1, h2] at hg
  linear_combination hg

/-- **Inner Laurent expansion.** If `f` is circle integrable on `C(c, R)`, `R > 0`, and
`R < ‖w‖`, then
`-∮_{C(c,R)} (z - (c + w))⁻¹ f(z) dz = ∑_{n ≥ 0} ∮_{C(c,R)} ((z - c)/w)ⁿ w⁻¹ f(z) dz`. -/
theorem hasSum_circleIntegral_inner {f : ℂ → ℂ} {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : CircleIntegrable f c R) (hw : R < ‖w‖) :
    HasSum (fun n : ℕ => ∮ z in C(c, R), ((z - c) / w) ^ n * w⁻¹ * f z)
      (∮ z in C(c, R), -((z - (c + w))⁻¹ * f z)) := by
  have hw0 : 0 < ‖w‖ := hR.trans hw
  have hq : R / ‖w‖ ∈ Ico (0 : ℝ) 1 := ⟨by positivity, (div_lt_one hw0).2 hw⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (R / ‖w‖) ^ n * (R / ‖w‖)) (fun n => ?_)
      (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [MeasureTheory.AEStronglyMeasurable.smul, MeasureTheory.AEStronglyMeasurable.mul,
      hf.def'.1] <;>
      apply Measurable.aestronglyMeasurable <;> fun_prop
  · refine Eventually.of_forall fun θ _ => ?_
    rw [deriv_circleMap, norm_smul, norm_mul, norm_mul, norm_mul, norm_pow, norm_div,
      norm_circleMap_zero, circleMap_sub_center, norm_circleMap_zero, norm_I, norm_inv,
      abs_of_pos hR]
    apply le_of_eq
    field_simp
  · exact Eventually.of_forall fun _ _ =>
      ((summable_geometric_of_lt_one hq.1 hq.2).mul_left _).mul_right _
  · simp_rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hq.1 hq.2]
    exact (hf.norm.mul_continuousOn continuousOn_const).mul_continuousOn continuousOn_const
  · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
    have hzc : circleMap c R θ - c ≠ w := fun h => by
      have := congrArg norm h
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR] at this
      exact hw.ne this
    have hn : ‖(circleMap c R θ - c) / w‖ < 1 := by
      rw [norm_div, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
      exact hq.2
    have hwne : w ≠ 0 := norm_pos_iff.mp hw0
    convert ((hasSum_geometric_of_norm_lt_one hn).mul_right (w⁻¹ * f (circleMap c R θ)))
      using 1
    · funext n; ring
    · have h1 : (1 : ℂ) - (circleMap c R θ - c) / w ≠ 0 := by
        rw [sub_ne_zero, ne_comm]
        exact div_ne_one_of_ne hzc
      have h2 : circleMap c R θ - (c + w) ≠ 0 := by
        intro h; apply hzc; linear_combination h
      field_simp
      ring

end Complex
