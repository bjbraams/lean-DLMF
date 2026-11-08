/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.AlgebraicAnalytic.Complex.Functions
public import DLMFMathlib.Analysis.Complex.CircleLaurent

/-!
# Laurent coefficient differentiation for Darboux's method

The coefficients of an iterated derivative are falling-factorial multiples of shifted
Laurent coefficients. This transfers integrable-singularity Darboux bounds to the
higher-order theorem without differentiating a singular boundary trace.
-/

@[expose] public noncomputable section

open Complex Set Filter Metric
open scoped Real Topology Nat

namespace DLMF.AsymptoticApproximations.DarbouxDerivatives

/-- Holomorphic functions on a punctured disk are analytic on that open set. -/
theorem analyticOnNhd_puncturedDisc {f : ℂ → ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) : AnalyticOnNhd ℂ f (puncturedDisc r) :=
  hf.analyticOnNhd ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const))

/-- Laurent coefficients commute with subtraction of two holomorphic functions. -/
theorem laurentCoeff_sub {f g : ℂ → ℂ} {r ρ : ℝ}
    (hf : DifferentiableOn ℂ f (puncturedDisc r))
    (hg : DifferentiableOn ℂ g (puncturedDisc r)) (hρ : 0 < ρ) (hρr : ρ < r) (n : ℤ) :
    AlgebraicAnalytic.laurentCoeff (f - g) 0 ρ n =
      AlgebraicAnalytic.laurentCoeff f 0 ρ n - AlgebraicAnalytic.laurentCoeff g 0 ρ n := by
  have hsph : sphere (0 : ℂ) ρ ⊆ puncturedDisc r := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    exact ⟨hz ▸ hρ, hz ▸ hρr⟩
  have hci (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (puncturedDisc r)) :
      CircleIntegrable (fun z => F z * z ^ (-n - 1)) 0 ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    intro z hz
    have hz0 : z ≠ 0 := by
      intro he
      have H := (hsph hz).1
      simp [he] at H
    exact ((hF.continuousOn.mono hsph) z hz).mul
      ((continuousAt_id.zpow₀ _ (Or.inl hz0)).continuousWithinAt)
  simp only [AlgebraicAnalytic.laurentCoeff, sub_zero, ← mul_sub]
  rw [← circleIntegral.integral_sub (hci f hf) (hci g hg)]
  congr 1
  apply circleIntegral.integral_congr hρ.le
  intro z _
  simp only [Pi.sub_apply]
  ring

/-- Differentiating multiplies the Laurent coefficient of index `n` by `n`. -/
theorem laurentCoeff_deriv {f : ℂ → ℂ} {r ρ : ℝ}
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) (hρ : 0 < ρ) (hρr : ρ < r) (n : ℤ) :
    AlgebraicAnalytic.laurentCoeff (deriv f) 0 ρ (n - 1) =
      (n : ℂ) * AlgebraicAnalytic.laurentCoeff f 0 ρ n := by
  have hsph : sphere (0 : ℂ) ρ ⊆ puncturedDisc r := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    exact ⟨hz ▸ hρ, hz ▸ hρr⟩
  have hA := analyticOnNhd_puncturedDisc hf
  have H := circleIntegral.integral_deriv_mul_zpow hρ
    (fun z hz => (hA z (hsph hz)).differentiableAt)
    (hA.deriv.continuousOn.mono hsph) n
  simp only [AlgebraicAnalytic.laurentCoeff, sub_zero,
    show -(n - 1) - 1 = -n by omega, show -n - 1 = -(n + 1) by omega, H]
  ring

/-- Every iterated derivative multiplies Laurent coefficients by the falling factorial. -/
theorem laurentCoeff_iteratedDeriv {f : ℂ → ℂ} {r ρ : ℝ}
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) (hρ : 0 < ρ) (hρr : ρ < r)
    (m : ℕ) (n : ℤ) :
    AlgebraicAnalytic.laurentCoeff (iteratedDeriv m f) 0 ρ (n - m) =
      (∏ j ∈ Finset.range m, ((n : ℂ) - (j : ℂ))) *
        AlgebraicAnalytic.laurentCoeff f 0 ρ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hA := (analyticOnNhd_puncturedDisc hf).iterated_deriv m
    have hD : DifferentiableOn ℂ (iteratedDeriv m f) (puncturedDisc r) := by
      rw [iteratedDeriv_eq_iterate]
      exact hA.differentiableOn
    rw [iteratedDeriv_succ,
      show n - ((m + 1 : ℕ) : ℤ) = (n - m) - 1 by omega,
      laurentCoeff_deriv hD hρ hρr (n - m), ih, Finset.prod_range_succ]
    push_cast
    ring

end DLMF.AsymptoticApproximations.DarbouxDerivatives
