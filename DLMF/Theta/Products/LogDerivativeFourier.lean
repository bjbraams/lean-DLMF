/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Theta
import DLMF.Theta.Products.LogDerivativesAndDoubleProducts
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Differentiating the theta logarithmic derivative Fourier series

The Fourier series for `θ₄′/θ₄` can be differentiated throughout the strip
`|Im z| < π Im τ / 2`. Uniform bounds on compact subsets justify the differentiation.
-/

public section

set_option maxHeartbeats 0
open Complex Filter DLMF.Elliptic
open scoped Real Topology
namespace DLMF.Theta

/-- The derivative of `θ₄′/θ₄` is given by its differentiated cosine Fourier series. -/
lemma jacobiThetaFourTau_logDeriv_deriv_hasSum {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : |z.im| < π * τ.im / 2) :
    HasSum (fun n : ℕ => 8 * (n + 1) * (cexp (π * I * τ) ^ (n + 1) /
        (1 - cexp (π * I * τ) ^ (2 * (n + 1)))) * cos (2 * (n + 1) * z))
      (deriv (fun w => deriv (fun u => jacobiThetaFourTau u τ) w /
        jacobiThetaFourTau w τ) z) := by
  let U : Set ℂ := {w | |w.im| < π * τ.im / 2}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  obtain ⟨u, hu, hb⟩ := (jacobiTheta_logDeriv_series_uniform hτ (Metric.closedBall z r)
    (isCompact_closedBall z r)).2 (fun w hw => hsub hw)
  let F : ℕ → ℂ → ℂ := fun n w => 4 * (cexp (π * I * τ) ^ (n + 1) /
    (1 - cexp (π * I * τ) ^ (2 * (n + 1)))) * sin (2 * (n + 1) * w)
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball z r) : ‖F n w‖ ≤ 4 * u n := by
    have hh := (hb n w (Metric.ball_subset_closedBall hw)).1
    calc
      ‖F n w‖ = 4 * ‖cexp (π * I * τ) ^ (n + 1) /
          (1 - cexp (π * I * τ) ^ (2 * (n + 1))) * sin (2 * (n + 1) * w)‖ := by
        dsimp only [F]
        rw [mul_assoc, norm_mul]
        norm_num
      _ ≤ 4 * u n := mul_le_mul_of_nonneg_left hh (by norm_num)
  have hsum := hasSum_deriv_of_summable_norm (hu.mul_left 4)
    (F := F) (U := Metric.ball z r) (fun n => by dsimp only [F]; fun_prop)
    Metric.isOpen_ball hbound (Metric.mem_ball_self hr)
  have hderiv (n : ℕ) : deriv (F n) z = 8 * (n + 1) *
      (cexp (π * I * τ) ^ (n + 1) / (1 - cexp (π * I * τ) ^ (2 * (n + 1)))) *
        cos (2 * (n + 1) * z) := by
    have h := (((hasDerivAt_id z).const_mul (2 * (n + 1 : ℂ))).csin).const_mul
      (4 * (cexp (π * I * τ) ^ (n + 1) / (1 - cexp (π * I * τ) ^ (2 * (n + 1)))))
    have hf := h.congr_of_eventuallyEq (f₁ := F n)
      (Eventually.of_forall fun w => by simp only [F, id_eq])
    rw [hf.deriv]
    simp only [id_eq]
    ring_nf
  have heq : (fun w => ∑' n, F n w) =ᶠ[𝓝 z]
      (fun w => deriv (fun u => jacobiThetaFourTau u τ) w / jacobiThetaFourTau w τ) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (jacobiThetaFourTau_logDeriv hτ hw).2.tsum_eq
  rw [heq.deriv_eq] at hsum
  simpa only [hderiv] using hsum

end DLMF.Theta
