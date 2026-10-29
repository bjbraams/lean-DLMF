/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Analytic series in a geometric Newton basis

The polynomials `∏ j < n, (w - q^j)` admit a uniform geometric bound on compact discs
when `‖q‖ < 1`. Consequently a series in this basis with geometrically bounded
coefficients is analytic on its expected open disc. The estimate uses Mathlib's
geometric series and `1 + x ≤ exp x`; normal convergence uses the existing locally
dominated holomorphic-series theorem.
-/

@[expose] public noncomputable section

open Complex Finset Filter Set
open scoped Topology

namespace Complex

/-- A geometric Newton polynomial is bounded on a closed disc by its radius to the
polynomial degree, times a constant independent of the degree. -/
theorem norm_prod_sub_pow_le {q w : ℂ} {ρ : ℝ} (hq : ‖q‖ < 1) (hρ : 0 < ρ)
    (hw : ‖w‖ ≤ ρ) (n : ℕ) :
    ‖∏ j ∈ range n, (w - q ^ j)‖ ≤
      ρ ^ n * Real.exp ((1 / (1 - ‖q‖)) / ρ) := by
  have hsum : ∑ j ∈ range n, ‖q‖ ^ j ≤ 1 / (1 - ‖q‖) := by
    have h := (summable_geometric_of_lt_one (norm_nonneg q) hq).sum_le_tsum (range n)
      (fun j _ => pow_nonneg (norm_nonneg q) j)
    rw [tsum_geometric_of_norm_lt_one (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)] using hq)] at h
    simpa only [one_div] using! h
  rw [norm_prod]
  calc
    _ ≤ ∏ j ∈ range n, (ρ * Real.exp (‖q‖ ^ j / ρ)) := by
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j _
      calc ‖w - q ^ j‖ ≤ ρ + ‖q‖ ^ j := by
            exact (norm_sub_le _ _).trans (by rw [norm_pow]; gcongr)
        _ = ρ * (1 + ‖q‖ ^ j / ρ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by simpa only [add_comm] using Real.add_one_le_exp (‖q‖ ^ j / ρ)) hρ.le
    _ = ρ ^ n * Real.exp ((∑ j ∈ range n, ‖q‖ ^ j) / ρ) := by
      rw [prod_mul_distrib]
      simp only [prod_const, card_range, ← Real.exp_sum, Finset.sum_div]
    _ ≤ _ := by gcongr

/-- Geometrically bounded Newton-series coefficients give a summable series at
every point strictly inside the reciprocal growth radius. -/
theorem summable_geometricNewton {q w : ℂ} {c : ℕ → ℂ} {C R : ℝ}
    (hq : ‖q‖ < 1) (hC : 0 ≤ C) (hR : 0 < R)
    (hc : ∀ n, ‖c n‖ ≤ C * R ^ n) (hw : ‖w‖ < R⁻¹) :
    Summable (fun n => c n * ∏ j ∈ range n, (w - q ^ j)) := by
  obtain ⟨ρ, hwρ, hρR⟩ := exists_between hw
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg w) hwρ
  have hr : R * ρ < 1 := by
    have h := mul_lt_mul_of_pos_left hρR hR
    rwa [mul_inv_cancel₀ hR.ne'] at h
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ R * ρ) hr).mul_left
      (C * Real.exp ((1 / (1 - ‖q‖)) / ρ)))
  intro n
  rw [norm_mul]
  calc ‖c n‖ * ‖∏ j ∈ range n, (w - q ^ j)‖ ≤
      (C * R ^ n) * (ρ ^ n * Real.exp ((1 / (1 - ‖q‖)) / ρ)) :=
        mul_le_mul (hc n) (norm_prod_sub_pow_le hq hρ hwρ.le n) (norm_nonneg _)
          (mul_nonneg hC (pow_nonneg hR.le _))
    _ = _ := by rw [mul_pow]; ring

/-- A geometrically bounded series in a geometric Newton basis is analytic on the
open disc given by the reciprocal coefficient growth rate. -/
theorem analyticOnNhd_tsum_geometricNewton {q : ℂ} {c : ℕ → ℂ} {C R : ℝ}
    (hq : ‖q‖ < 1) (hC : 0 ≤ C) (hR : 0 < R) (hc : ∀ n, ‖c n‖ ≤ C * R ^ n) :
    AnalyticOnNhd ℂ (fun w => ∑' n, c n * ∏ j ∈ range n, (w - q ^ j))
      (Metric.ball 0 R⁻¹) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  apply differentiableOn_tsum_of_locally_dominated Metric.isOpen_ball
  · intro n w _
    fun_prop
  · intro w hw
    have hw' : ‖w‖ < R⁻¹ := by simpa using hw
    obtain ⟨ρ, hwρ, hρR⟩ := exists_between hw'
    have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg w) hwρ
    have hr : R * ρ < 1 := by
      have h := mul_lt_mul_of_pos_left hρR hR
      rwa [mul_inv_cancel₀ hR.ne'] at h
    refine ⟨Metric.ball 0 ρ, Metric.isOpen_ball.mem_nhds (by simpa using hwρ),
      fun n => C * Real.exp ((1 / (1 - ‖q‖)) / ρ) * (R * ρ) ^ n,
      (summable_geometric_of_lt_one (by positivity : 0 ≤ R * ρ) hr).mul_left _, ?_⟩
    intro n z hz
    rw [norm_mul]
    have hz' : ‖z‖ ≤ ρ := (show ‖z‖ < ρ by simpa using hz).le
    calc ‖c n‖ * ‖∏ j ∈ range n, (z - q ^ j)‖ ≤
        (C * R ^ n) * (ρ ^ n * Real.exp ((1 / (1 - ‖q‖)) / ρ)) :=
          mul_le_mul (hc n) (norm_prod_sub_pow_le hq hρ hz' n) (norm_nonneg _)
            (mul_nonneg hC (pow_nonneg hR.le _))
      _ = _ := by dsimp only; rw [mul_pow]; ring

end Complex
