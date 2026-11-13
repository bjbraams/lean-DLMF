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
import DLMF.Theta.PowerSeries.ThetaOne
import DLMF.Theta.Identities
import DLMF.Theta.ZeroValues
import DLMF.JacobiElliptic.QuarterPeriods
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The logarithmic power series of the second Jacobi theta function

The Landen product determines the local logarithmic series. Analytic continuation on
the shifted lattice disk gives the full convergence region in DLMF 20.6.3.
-/

public section

set_option maxHeartbeats 0
open Complex Filter DLMF.Elliptic DLMF.JacobiElliptic
open scoped Real Topology
namespace DLMF.Theta.LogarithmicTheta

/-- The second theta logarithmic series follows from the even-row lattice relation. -/
lemma thetaTwo_powerSeries_of_lattice_relation {τ z : ℂ} (hτ : 0 < τ.im)
    (hα : ∀ j : ℕ, thetaAlpha (2 * (j + 1)) τ =
      2 ^ (2 * (j + 1)) * thetaDelta (2 * (j + 1)) (2 * τ) - thetaDelta (2 * (j + 1)) τ)
    (hz : ‖π * z‖ < thetaShiftedLatticeMinNorm (1 / 2) 0 τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaAlpha (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaTwoTau (π * z) τ = jacobiThetaTwoNullTau τ * cexp (-S) := by
  let c : ℕ → ℂ := fun j => thetaAlpha (2 * (j + 1)) τ
  let f : ℕ → ℂ → ℂ := fun j w => c j * w ^ (2 * (j + 1)) / (2 * (j + 1))
  let S : ℂ → ℂ := fun w => ∑' j, f j w
  let U : Set ℂ := {w | ‖π * w‖ < thetaShiftedLatticeMinNorm (1 / 2) 0 τ}
  have hc (j : ℕ) : (∑' n : ℤ, ∑' m : ℤ,
      (((m : ℂ) - (1 / 2 : ℝ) + ((n : ℂ) - (0 : ℝ)) * τ) ^ (2 * (j + 1)))⁻¹) = c j := by
    dsimp only [c, thetaAlpha]
    simp only [ofReal_div, ofReal_one, ofReal_ofNat, ofReal_zero, sub_zero,
      zpow_neg, zpow_natCast]
  have hs (w : ℂ) (hw : w ∈ U) : Summable (fun j => ‖f j w‖) := by
    simpa only [hc] using summable_norm_shiftedLatticeLogSeries hτ (1 / 2) 0 hw
  have haS : AnalyticOnNhd ℂ S U := by
    simpa only [hc] using analyticOnNhd_shiftedLatticeLogSeries hτ (1 / 2) 0
  have hρ : 0 < thetaShiftedLatticeMinNorm (1 / 2) 0 τ :=
    thetaShiftedLatticeMinNorm_half_zero_pos hτ
  have hU0 : (0 : ℂ) ∈ U := by simpa only [U, Set.mem_ofPred_eq, mul_zero, norm_zero] using hρ
  have hπ : 0 < ‖(π : ℂ)‖ := norm_pos_iff.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hUball : U = Metric.ball 0 (thetaShiftedLatticeMinNorm (1 / 2) 0 τ / ‖(π : ℂ)‖) := by
    ext w
    simp only [U, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [lt_div_iff₀ hπ, norm_mul, mul_comm]
  have hconn : IsPreconnected U := by rw [hUball]; exact (convex_ball _ _).isPreconnected
  have hτ2 : 0 < (2 * τ).im := by simpa using mul_pos two_pos hτ
  have hD (σ : ℂ) (hσ : 0 < σ.im) : jacobiThetaOneDerivNullTau σ ≠ 0 := by
    rw [jacobiThetaOneDerivNullTau_eq_mul hσ]
    exact mul_ne_zero (mul_ne_zero (jacobiThetaTwoTau_zero_ne_zero hσ)
      (jacobiThetaThreeTau_zero_ne_zero hσ)) (jacobiThetaFourTau_zero_ne_zero hσ)
  have hθ1 : Differentiable ℂ (fun w => jacobiThetaOneTau w τ) := by
    simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 1 hτ
  have hθ2 : Differentiable ℂ (fun w => jacobiThetaTwoTau w τ) := by
    simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 2 hτ
  have hθ12 : Differentiable ℂ (fun w => jacobiThetaOneTau w (2 * τ)) := by
    simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 1 hτ2
  have hconst : jacobiThetaOneDerivNullTau τ * jacobiThetaTwoNullTau τ =
      2 * jacobiThetaOneDerivNullTau (2 * τ) * jacobiThetaFourNullTau (2 * τ) := by
    have hd1 := (hθ1 0).hasDerivAt.mul (hθ2 0).hasDerivAt
    have hd2 := ((hθ12 0).hasDerivAt.comp_of_eq 0
      ((hasDerivAt_id (0 : ℂ)).const_mul 2) (by simp)).mul_const
        (jacobiThetaFourNullTau (2 * τ))
    have hd2' := hd2.congr_of_eventuallyEq (f₁ := fun w => jacobiThetaOneTau w τ *
      jacobiThetaTwoTau w τ) (Eventually.of_forall fun w =>
        jacobiThetaOneTau_mul_jacobiThetaTwoTau w τ hτ)
    have h := hd1.unique hd2'
    simpa only [jacobiThetaOneTau_zero, zero_mul, add_zero, jacobiThetaOneDerivNullTau,
      jacobiThetaTwoNullTau, mul_one, one_mul, id_eq, mul_assoc, mul_left_comm, mul_comm] using h
  have hsmall1 : ∀ᶠ w : ℂ in 𝓝 0, ‖π * w‖ < thetaLatticeMinNorm τ :=
    (isOpen_lt (continuous_norm.comp (continuous_const.mul continuous_id))
      continuous_const).mem_nhds (by simpa using thetaLatticeMinNorm_pos hτ)
  have hsmall2 : ∀ᶠ w : ℂ in 𝓝 0, ‖π * (2 * w)‖ < thetaLatticeMinNorm (2 * τ) :=
    (isOpen_lt (continuous_norm.comp (continuous_const.mul (continuous_const.mul
      continuous_id))) continuous_const).mem_nhds (by simpa using thetaLatticeMinNorm_pos hτ2)
  have hzero : S 0 = 0 := by
    dsimp only [S, f]
    have hpow (j : ℕ) : (0 : ℂ) ^ (2 * (j + 1)) = 0 := zero_pow (by omega)
    simp only [hpow, mul_zero, zero_div, tsum_zero]
  have hlocal : (fun w => jacobiThetaTwoTau (π * w) τ) =ᶠ[𝓝 0]
      fun w => jacobiThetaTwoNullTau τ * cexp (-S w) := by
    filter_upwards [hsmall1, hsmall2] with w hw1 hw2
    by_cases hw0 : w = 0
    · subst w
      rw [mul_zero, hzero]
      simp only [neg_zero, exp_zero, mul_one, jacobiThetaTwoNullTau]
    · obtain ⟨S1, hS1, he1⟩ := jacobiThetaOneTau_powerSeries hτ hw1
      obtain ⟨S2, hS2, he2⟩ := jacobiThetaOneTau_powerSeries hτ2 hw2
      have hdiff : HasSum (fun j => f j w) (S2 - S1) := by
        convert hS2.sub hS1 using 1
        funext j
        dsimp only [f, c]
        rw [hα j, mul_pow]
        ring_nf
      have hS : S w = S2 - S1 := hdiff.tsum_eq
      have hp := jacobiThetaOneTau_mul_jacobiThetaTwoTau (π * w) τ hτ
      rw [show 2 * (π * w) = π * (2 * w) by ring_nf, he1, he2] at hp
      have hexp : cexp (-S1) * cexp (-(S2 - S1)) = cexp (-S2) := by
        rw [← exp_add]
        congr 1
        ring_nf
      have hr : π * (2 * w) * jacobiThetaOneDerivNullTau (2 * τ) * cexp (-S2) *
          jacobiThetaFourNullTau (2 * τ) =
          (π * w * jacobiThetaOneDerivNullTau τ * cexp (-S1)) *
            (jacobiThetaTwoNullTau τ * cexp (-(S2 - S1))) := by
        calc
          _ = π * w * (2 * jacobiThetaOneDerivNullTau (2 * τ) *
              jacobiThetaFourNullTau (2 * τ)) * cexp (-S2) := by ring_nf
          _ = _ := by rw [← hconst, ← hexp]; ring_nf
      rw [hr] at hp
      rw [hS]
      exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (ofReal_ne_zero.mpr Real.pi_ne_zero) hw0) (hD τ hτ)) (exp_ne_zero _)) hp
  have hleft : AnalyticOnNhd ℂ (fun w => jacobiThetaTwoTau (π * w) τ) U := by
    intro w _
    exact ((hθ2.comp (differentiable_const _ |>.mul differentiable_id)).analyticAt w)
  have hright : AnalyticOnNhd ℂ (fun w => jacobiThetaTwoNullTau τ * cexp (-S w)) U := by
    intro w hw
    exact analyticAt_const.mul ((haS w hw).neg.cexp)
  refine ⟨S z, (summable_norm_iff.mp (hs z hz)).hasSum, ?_⟩
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconn hU0 hlocal hz

end DLMF.Theta.LogarithmicTheta
