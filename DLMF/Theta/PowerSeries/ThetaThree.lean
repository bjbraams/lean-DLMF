/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.PowerSeries
public import DLMF.Theta.Basic.Definitions
public import DLMF.Elliptic.Basic.Theta
import DLMF.Theta.PowerSeries.ShiftedLattice
import DLMF.Theta.PowerSeries.ThetaTwo
import DLMF.Theta.Identities
import DLMF.Theta.ZeroValues
import DLMF.JacobiElliptic.QuarterPeriods
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The logarithmic power series of the third Jacobi theta function

The real-shifted Landen product determines the local logarithmic expansion, and analytic
continuation gives the full shifted lattice disk in DLMF 20.6.4.
-/

public section

set_option maxHeartbeats 0
open Complex Filter DLMF.Elliptic DLMF.JacobiElliptic
open scoped Real Topology
namespace DLMF.Theta.LogarithmicTheta

/-- The third theta logarithmic series follows from the shifted even-row relation. -/
lemma thetaThree_powerSeries_of_lattice_relation {τ z : ℂ} (hτ : 0 < τ.im)
    (hβ : ∀ j : ℕ, thetaBeta (2 * (j + 1)) τ =
      thetaAlpha (2 * (j + 1)) (τ / 2) - thetaAlpha (2 * (j + 1)) τ)
    (hα : ∀ σ : ℂ, 0 < σ.im → ∀ j : ℕ, thetaAlpha (2 * (j + 1)) σ =
      2 ^ (2 * (j + 1)) * thetaDelta (2 * (j + 1)) (2 * σ) - thetaDelta (2 * (j + 1)) σ)
    (hz : ‖π * z‖ < thetaShiftedLatticeMinNorm (1 / 2) (1 / 2) τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaBeta (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaThreeTau (π * z) τ = jacobiThetaThreeNullTau τ * cexp (-S) := by
  let c : ℕ → ℂ := fun j => thetaBeta (2 * (j + 1)) τ
  let f : ℕ → ℂ → ℂ := fun j w => c j * w ^ (2 * (j + 1)) / (2 * (j + 1))
  let S : ℂ → ℂ := fun w => ∑' j, f j w
  let U : Set ℂ := {w | ‖π * w‖ < thetaShiftedLatticeMinNorm (1 / 2) (1 / 2) τ}
  have hc (j : ℕ) : (∑' n : ℤ, ∑' m : ℤ,
      (((m : ℂ) - (1 / 2 : ℝ) + ((n : ℂ) - (1 / 2 : ℝ)) * τ) ^ (2 * (j + 1)))⁻¹) = c j := by
    dsimp only [c, thetaBeta]
    simp only [ofReal_div, ofReal_one, ofReal_ofNat,
      zpow_neg, zpow_natCast]
  have hs (w : ℂ) (hw : w ∈ U) : Summable (fun j => ‖f j w‖) := by
    simpa only [hc] using summable_norm_shiftedLatticeLogSeries hτ (1 / 2) (1 / 2) hw
  have haS : AnalyticOnNhd ℂ S U := by
    simpa only [hc] using analyticOnNhd_shiftedLatticeLogSeries hτ (1 / 2) (1 / 2)
  have hρ : 0 < thetaShiftedLatticeMinNorm (1 / 2) (1 / 2) τ :=
    thetaShiftedLatticeMinNorm_half_pos (1 / 2) hτ
  have hU0 : (0 : ℂ) ∈ U := by simpa only [U, Set.mem_ofPred_eq, mul_zero, norm_zero] using hρ
  have hπ : 0 < ‖(π : ℂ)‖ := norm_pos_iff.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hUball : U = Metric.ball 0 (thetaShiftedLatticeMinNorm (1 / 2) (1 / 2) τ / ‖(π : ℂ)‖) := by
    ext w
    simp only [U, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [lt_div_iff₀ hπ, norm_mul, mul_comm]
  have hconn : IsPreconnected U := by rw [hUball]; exact (convex_ball _ _).isPreconnected
  have hτh : 0 < (τ / 2).im := by simpa using div_pos hτ two_pos
  have hθ3 : Differentiable ℂ (fun w => jacobiThetaThreeTau w τ) := by
    simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 3 hτ
  have hprod (x : ℂ) : 2 * (jacobiThetaTwoTau x τ * jacobiThetaThreeTau x τ) =
      jacobiThetaTwoTau x (τ / 2) * jacobiThetaTwoNullTau (τ / 2) := by
    simpa only [show 2 * (τ / 2) = τ by ring_nf] using
      two_mul_jacobiThetaTwoTau_mul_jacobiThetaThreeTau_two_mul x (τ / 2) hτh
  have hconst : jacobiThetaTwoNullTau (τ / 2) * jacobiThetaTwoNullTau (τ / 2) =
      2 * jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ := by
    have h := (hprod 0).symm
    simpa only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, mul_assoc] using h
  have hsmall1 : ∀ᶠ w : ℂ in 𝓝 0, ‖π * w‖ < thetaShiftedLatticeMinNorm (1 / 2) 0 τ :=
    (isOpen_lt (continuous_norm.comp (continuous_const.mul continuous_id))
      continuous_const).mem_nhds (by simpa using thetaShiftedLatticeMinNorm_half_zero_pos hτ)
  have hsmall2 : ∀ᶠ w : ℂ in 𝓝 0, ‖π * w‖ < thetaShiftedLatticeMinNorm (1 / 2) 0 (τ / 2) :=
    (isOpen_lt (continuous_norm.comp (continuous_const.mul continuous_id))
      continuous_const).mem_nhds (by simpa using thetaShiftedLatticeMinNorm_half_zero_pos hτh)
  have hlocal : (fun w => jacobiThetaThreeTau (π * w) τ) =ᶠ[𝓝 0]
      fun w => jacobiThetaThreeNullTau τ * cexp (-S w) := by
    filter_upwards [hsmall1, hsmall2] with w hw1 hw2
    obtain ⟨S1, hS1, he1⟩ := thetaTwo_powerSeries_of_lattice_relation hτ (hα τ hτ) hw1
    obtain ⟨S2, hS2, he2⟩ := thetaTwo_powerSeries_of_lattice_relation hτh (hα _ hτh) hw2
    have hdiff : HasSum (fun j => f j w) (S2 - S1) := by
      convert hS2.sub hS1 using 1
      funext j
      dsimp only [f, c]
      rw [hβ j]
      ring_nf
    have hS : S w = S2 - S1 := hdiff.tsum_eq
    have hp := hprod (π * w)
    rw [he1, he2] at hp
    have hexp : cexp (-S1) * cexp (-(S2 - S1)) = cexp (-S2) := by
      rw [← exp_add]
      congr 1
      ring_nf
    have hr : jacobiThetaTwoNullTau (τ / 2) * cexp (-S2) *
        jacobiThetaTwoNullTau (τ / 2) =
        2 * ((jacobiThetaTwoNullTau τ * cexp (-S1)) *
          (jacobiThetaThreeNullTau τ * cexp (-(S2 - S1)))) := by
      calc
        _ = (jacobiThetaTwoNullTau (τ / 2) *
            jacobiThetaTwoNullTau (τ / 2)) * cexp (-S2) := by ring_nf
        _ = _ := by rw [hconst, ← hexp]; ring_nf
    rw [hr] at hp
    have hh := mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) hp
    rw [hS]
    exact mul_left_cancel₀ (mul_ne_zero (jacobiThetaTwoTau_zero_ne_zero hτ)
      (exp_ne_zero _)) hh
  have hleft : AnalyticOnNhd ℂ (fun w => jacobiThetaThreeTau (π * w) τ) U := by
    intro w _
    exact ((hθ3.comp (differentiable_const _ |>.mul differentiable_id)).analyticAt w)
  have hright : AnalyticOnNhd ℂ (fun w => jacobiThetaThreeNullTau τ * cexp (-S w)) U := by
    intro w hw
    exact analyticAt_const.mul ((haS w hw).neg.cexp)
  refine ⟨S z, (summable_norm_iff.mp (hs z hz)).hasSum, ?_⟩
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconn hU0 hlocal hz

end DLMF.Theta.LogarithmicTheta
