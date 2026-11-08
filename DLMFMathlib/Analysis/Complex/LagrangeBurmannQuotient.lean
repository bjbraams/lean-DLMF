/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.LagrangeBurmann
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Local Lagrange–Bürmann quotient expansions

For an analytic coordinate `h` with a simple zero at the origin, put
`Ψ(t) = t/h(t)`, with its analytic value at zero. The quotient
`F(t)/(1-h(t)Ψ'(t))` has an expansion in powers of `h(t)` whose coefficients are
`[tⁿ](F(t)Ψ(t)ⁿ)`. The formula applies directly to weighted inverse-coordinate densities.

The local factorization and bounds follow the proof of
`Complex.hasSum_lagrangeInversion`; the quotient form keeps the numerator arbitrary.
-/

@[expose] public noncomputable section

open Complex Metric Set Filter MeasureTheory
open scoped Real Topology Nat NNReal ENNReal

namespace Complex

/-- The local Lagrange–Bürmann quotient formula, in powers of an analytic coordinate. -/
theorem hasSum_lagrangeBurmann_quotient {h F : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (h0 : h 0 = 0) (hd : deriv h 0 ≠ 0) (hF : AnalyticAt ℂ F 0) :
    ∃ ε > 0, ∀ w : ℂ, ‖w‖ < ε →
      HasSum (fun n : ℕ => h w ^ n *
        (iteratedDeriv n (fun t => F t * (dslope h 0 t)⁻¹ ^ n) 0 / n !))
        (F w / (1 - h w * deriv (fun t => (dslope h 0 t)⁻¹) w)) := by
  obtain ⟨R₁, hR₁, hh₁⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨R₂, hR₂, hF₂⟩ := hF.exists_ball_analyticOnNhd
  have hDc : ContinuousAt (dslope h 0) 0 := continuousAt_dslope_same.2 hh.differentiableAt
  have hD0 : dslope h 0 0 ≠ 0 := by rwa [dslope_same]
  obtain ⟨R₃, hR₃, hD₃⟩ := Metric.eventually_nhds_iff.1 (hDc.eventually_ne hD0)
  set R := min R₁ (min R₂ R₃) with hRdef
  have hR : 0 < R := lt_min hR₁ (lt_min hR₂ hR₃)
  set U := ball (0 : ℂ) R with hUdef
  have hUo : IsOpen U := isOpen_ball
  have hhU : DifferentiableOn ℂ h U :=
    (hh₁.mono (ball_subset_ball (min_le_left _ _))).differentiableOn
  have hFU : DifferentiableOn ℂ F U :=
    (hF₂.mono (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)))).differentiableOn
  have hDU : DifferentiableOn ℂ (dslope h 0) U :=
    (differentiableOn_dslope (ball_mem_nhds 0 hR)).2 hhU
  have hDne : ∀ t ∈ U, dslope h 0 t ≠ 0 := fun t ht => hD₃ (lt_of_lt_of_le (mem_ball.1 ht)
    ((min_le_right _ _).trans (min_le_right _ _)))
  set Ψ : ℂ → ℂ := fun t => (dslope h 0 t)⁻¹ with hΨdef
  have hΨU : DifferentiableOn ℂ Ψ U := hDU.inv hDne
  have hΨ'U : DifferentiableOn ℂ (deriv Ψ) U := hΨU.deriv hUo
  set r := R / 2 with hrdef
  have hr : 0 < r := by positivity
  have hsub : closedBall (0 : ℂ) r ⊆ U := closedBall_subset_ball (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hΨU.continuousOn.mono hsub)
  obtain ⟨M', hM'⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hΨ'U.continuousOn.mono hsub)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hDU.continuousOn.mono hsub)
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) r := mem_closedBall_self hr.le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0mem)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0 h0mem)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 h0mem)
  set ε := min (r / 2) (min (r / (2 * (K + 1) * (M + 1))) (1 / (2 * (K + 1) * (M' + 1))))
    with hεdef
  refine ⟨ε, by positivity, fun w hw => ?_⟩
  have hw1 : ‖w‖ < r / 2 := hw.trans_le (min_le_left _ _)
  have hw2 : ‖w‖ < r / (2 * (K + 1) * (M + 1)) :=
    hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hw3 : ‖w‖ < 1 / (2 * (K + 1) * (M' + 1)) :=
    hw.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hwB : w ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hwU : w ∈ U := hsub hwB
  set ζ := h w with hζdef
  have hζ : ζ = w * dslope h 0 w := by
    have := sub_smul_dslope h 0 w
    rw [h0, sub_zero, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hζn : ‖ζ‖ ≤ ‖w‖ * (K + 1) := by
    rw [hζ, norm_mul]
    exact mul_le_mul_of_nonneg_left ((hK w hwB).trans (by linarith)) (norm_nonneg _)
  have hζM : ‖ζ‖ * (M + 1) < r / 2 := by
    have h1 : ‖w‖ * (K + 1) * (M + 1) < r / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hw2
      nlinarith
    calc ‖ζ‖ * (M + 1) ≤ ‖w‖ * (K + 1) * (M + 1) :=
          mul_le_mul_of_nonneg_right hζn (by linarith)
      _ < r / 2 := h1
  have hζM' : ‖ζ‖ * (M' + 1) < 1 := by
    have h1 : ‖w‖ * (K + 1) * (M' + 1) < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hw3
      nlinarith
    calc ‖ζ‖ * (M' + 1) ≤ ‖w‖ * (K + 1) * (M' + 1) :=
          mul_le_mul_of_nonneg_right hζn (by linarith)
      _ < 1 := by linarith
  set f : ℂ → ℂ := fun t => t - ζ * Ψ t with hfdef
  have hfU : DifferentiableOn ℂ f U := differentiableOn_id.sub (hΨU.const_mul ζ)
  set g := dslope f w with hgdef
  have hgU : DifferentiableOn ℂ g U := (differentiableOn_dslope (hUo.mem_nhds hwU)).2 hfU
  have hfw : f w = 0 := by
    simp only [hfdef, hΨdef, hζ]
    field_simp [hDne w hwU]
    ring
  have hfac : ∀ t, t - ζ * Ψ t = (t - w) * g t := by
    intro t
    have := sub_smul_dslope f w t
    rw [hfw, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hgw : g w = 1 - ζ * deriv Ψ w := by
    rw [hgdef, dslope_same]
    exact ((hasDerivAt_id w).sub ((hΨU.differentiableAt (hUo.mem_nhds hwU)).hasDerivAt.const_mul
      ζ)).deriv
  have hg0 : ∀ t ∈ closedBall (0 : ℂ) r, g t ≠ 0 := by
    intro t ht hgt
    by_cases htw : t = w
    · subst htw
      rw [hgw, sub_eq_zero] at hgt
      have : ‖ζ * deriv Ψ t‖ < 1 := by
        rw [norm_mul]
        calc ‖ζ‖ * ‖deriv Ψ t‖ ≤ ‖ζ‖ * (M' + 1) :=
              mul_le_mul_of_nonneg_left ((hM' t ht).trans (by linarith)) (norm_nonneg _)
          _ < 1 := hζM'
      rw [← hgt, norm_one] at this
      exact lt_irrefl _ this
    · have hft : t - ζ * Ψ t = 0 := by rw [hfac t, hgt, mul_zero]
      have hlip : ‖Ψ t - Ψ w‖ ≤ M' * ‖t - w‖ :=
        (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
          (fun x hx => hΨU.differentiableAt (hUo.mem_nhds (hsub hx))) hM' hwB ht
      have heq : t - w = ζ * (Ψ t - Ψ w) := by
        have : w - ζ * Ψ w = 0 := hfw
        linear_combination hft - this
      have hpos : 0 < ‖t - w‖ := norm_pos_iff.2 (sub_ne_zero.2 htw)
      have : ‖t - w‖ ≤ ‖ζ‖ * M' * ‖t - w‖ := by
        calc ‖t - w‖ = ‖ζ‖ * ‖Ψ t - Ψ w‖ := by rw [heq, norm_mul]
          _ ≤ ‖ζ‖ * (M' * ‖t - w‖) := mul_le_mul_of_nonneg_left hlip (norm_nonneg _)
          _ = ‖ζ‖ * M' * ‖t - w‖ := by ring
      nlinarith [norm_nonneg ζ]
  have key := lagB_hasSum_iteratedDeriv (F := F) (Φ := Ψ) (g := g) (ρ := ‖ζ‖ * (M + 1))
    (z := ζ) (w := w) hr (hFU.mono hsub) (hΨU.mono hsub) (hgU.mono hsub) hg0 (by linarith)
    (fun t ht => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hM t (sphere_subset_closedBall ht)).trans
        (by linarith)) (norm_nonneg _))
    (by linarith) (fun t _ => hfac t)
  simpa only [hgw, hζdef, hΨdef] using key

/-- The quotient formula for the coordinate `t/Φ(t)`, with `Φ(0) ≠ 0`. -/
theorem hasSum_lagrangeBurmann_div_coordinate {Φ F : ℂ → ℂ}
    (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0 ≠ 0) (hF : AnalyticAt ℂ F 0) :
    ∃ ε > 0, ∀ w : ℂ, ‖w‖ < ε →
      HasSum (fun n : ℕ => (w / Φ w) ^ n *
        (iteratedDeriv n (fun t => F t * Φ t ^ n) 0 / n !))
        (F w / (1 - (w / Φ w) * deriv Φ w)) := by
  let h : ℂ → ℂ := fun t => t / Φ t
  have hh : AnalyticAt ℂ h 0 := analyticAt_id.div hΦ hΦ0
  have h0 : h 0 = 0 := by simp only [h, zero_div]
  have hd : deriv h 0 = (Φ 0)⁻¹ := by
    have H := (hasDerivAt_id (0 : ℂ)).div hΦ.differentiableAt.hasDerivAt hΦ0
    have H' : HasDerivAt h ((Φ 0)⁻¹) 0 := by
      convert H using 1
      · funext t; rfl
      · simp only [id_eq, one_mul, zero_mul, sub_zero]
        field_simp
    exact H'.deriv
  have hΨ : (fun t => (dslope h 0 t)⁻¹) = Φ := by
    funext t
    by_cases ht : t = 0
    · subst t
      rw [dslope_same, hd, inv_inv]
    · rw [dslope_of_ne _ ht, slope_def_field, h0, sub_zero, sub_zero]
      dsimp only [h]
      field_simp
  obtain ⟨ε, hε, H⟩ := hasSum_lagrangeBurmann_quotient hh h0 (by rw [hd]; exact inv_ne_zero hΦ0) hF
  refine ⟨ε, hε, fun w hw => ?_⟩
  have he (n : ℕ) : (fun t => F t * (dslope h 0 t)⁻¹ ^ n) =
      (fun t => F t * Φ t ^ n) := by
    funext t
    rw [show (dslope h 0 t)⁻¹ = Φ t from congrFun hΨ t]
  simpa only [he, hΨ, h] using H w hw

end Complex
