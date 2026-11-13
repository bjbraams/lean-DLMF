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
# The logarithmic power series of the fourth Jacobi theta function

The imaginary-period Landen product determines the local logarithmic expansion, and
analytic continuation gives its entire shifted lattice disk in DLMF 20.6.5.
-/

public section

set_option maxHeartbeats 0
open Complex Filter DLMF.Elliptic DLMF.JacobiElliptic
open scoped Real Topology
namespace DLMF.Theta.LogarithmicTheta

/-- The fourth theta logarithmic series follows from the even/odd period relation. -/
lemma thetaFour_powerSeries_of_lattice_relation {τ z : ℂ} (hτ : 0 < τ.im)
    (hγ : ∀ j : ℕ, thetaGamma (2 * (j + 1)) τ =
      thetaDelta (2 * (j + 1)) (τ / 2) - thetaDelta (2 * (j + 1)) τ)
    (hz : ‖π * z‖ < thetaShiftedLatticeMinNorm 0 (1 / 2) τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaGamma (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaFourTau (π * z) τ = jacobiThetaFourNullTau τ * cexp (-S) := by
  let c : ℕ → ℂ := fun j => thetaGamma (2 * (j + 1)) τ
  let f : ℕ → ℂ → ℂ := fun j w => c j * w ^ (2 * (j + 1)) / (2 * (j + 1))
  let S : ℂ → ℂ := fun w => ∑' j, f j w
  let U : Set ℂ := {w | ‖π * w‖ < thetaShiftedLatticeMinNorm 0 (1 / 2) τ}
  have hc (j : ℕ) : (∑' n : ℤ, ∑' m : ℤ,
      (((m : ℂ) - (0 : ℝ) + ((n : ℂ) - (1 / 2 : ℝ)) * τ) ^ (2 * (j + 1)))⁻¹) = c j := by
    dsimp only [c, thetaGamma]
    simp only [ofReal_div, ofReal_one, ofReal_ofNat, ofReal_zero, sub_zero,
      zpow_neg, zpow_natCast]
  have hs (w : ℂ) (hw : w ∈ U) : Summable (fun j => ‖f j w‖) := by
    simpa only [hc] using summable_norm_shiftedLatticeLogSeries hτ 0 (1 / 2) hw
  have haS : AnalyticOnNhd ℂ S U := by
    simpa only [hc] using analyticOnNhd_shiftedLatticeLogSeries hτ 0 (1 / 2)
  have hρ : 0 < thetaShiftedLatticeMinNorm 0 (1 / 2) τ :=
    thetaShiftedLatticeMinNorm_half_pos 0 hτ
  have hU0 : (0 : ℂ) ∈ U := by simpa only [U, Set.mem_ofPred_eq, mul_zero, norm_zero] using hρ
  have hπ : 0 < ‖(π : ℂ)‖ := norm_pos_iff.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hUball : U = Metric.ball 0 (thetaShiftedLatticeMinNorm 0 (1 / 2) τ / ‖(π : ℂ)‖) := by
    ext w
    simp only [U, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [lt_div_iff₀ hπ, norm_mul, mul_comm]
  have hconn : IsPreconnected U := by rw [hUball]; exact (convex_ball _ _).isPreconnected
  have hτh : 0 < (τ / 2).im := by simpa using div_pos hτ two_pos
  have hD (σ : ℂ) (hσ : 0 < σ.im) : jacobiThetaOneDerivNullTau σ ≠ 0 := by
    rw [jacobiThetaOneDerivNullTau_eq_mul hσ]
    exact mul_ne_zero (mul_ne_zero (jacobiThetaTwoTau_zero_ne_zero hσ)
      (jacobiThetaThreeTau_zero_ne_zero hσ)) (jacobiThetaFourTau_zero_ne_zero hσ)
  have hθ1 : Differentiable ℂ (fun w => jacobiThetaOneTau w τ) := by
    simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 1 hτ
  have hθ4 : Differentiable ℂ (fun w => jacobiThetaFourTau w τ) := by
    simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 4 hτ
  have hθ1h : Differentiable ℂ (fun w => jacobiThetaOneTau w (τ / 2)) := by
    simpa only [jacobiThetaTau] using differentiable_jacobiThetaTau 1 hτh
  have hprod (x : ℂ) : 2 * (jacobiThetaOneTau x τ * jacobiThetaFourTau x τ) =
      jacobiThetaOneTau x (τ / 2) * jacobiThetaTwoNullTau (τ / 2) := by
    simpa only [show 2 * (τ / 2) = τ by ring_nf] using
      two_mul_jacobiThetaOneTau_mul_jacobiThetaFourTau_two_mul x (τ / 2) hτh
  have hconst : jacobiThetaOneDerivNullTau (τ / 2) * jacobiThetaTwoNullTau (τ / 2) =
      2 * jacobiThetaOneDerivNullTau τ * jacobiThetaFourNullTau τ := by
    have hd1 := ((hθ1 0).hasDerivAt.mul (hθ4 0).hasDerivAt).const_mul 2
    have hd2 := (hθ1h 0).hasDerivAt.mul_const (jacobiThetaTwoNullTau (τ / 2))
    have hd2' := hd2.congr_of_eventuallyEq (f₁ := fun w => 2 * (jacobiThetaOneTau w τ *
      jacobiThetaFourTau w τ)) (Eventually.of_forall hprod)
    have h := hd2'.unique hd1
    simpa only [jacobiThetaOneTau_zero, zero_mul, add_zero, jacobiThetaOneDerivNullTau,
      jacobiThetaFourNullTau, mul_one, one_mul, id_eq, mul_assoc, mul_left_comm, mul_comm] using h
  have hsmall1 : ∀ᶠ w : ℂ in 𝓝 0, ‖π * w‖ < thetaLatticeMinNorm τ :=
    (isOpen_lt (continuous_norm.comp (continuous_const.mul continuous_id))
      continuous_const).mem_nhds (by simpa using thetaLatticeMinNorm_pos hτ)
  have hsmall2 : ∀ᶠ w : ℂ in 𝓝 0, ‖π * w‖ < thetaLatticeMinNorm (τ / 2) :=
    (isOpen_lt (continuous_norm.comp (continuous_const.mul continuous_id))
      continuous_const).mem_nhds (by simpa using thetaLatticeMinNorm_pos hτh)
  have hzero : S 0 = 0 := by
    dsimp only [S, f]
    have hpow (j : ℕ) : (0 : ℂ) ^ (2 * (j + 1)) = 0 := zero_pow (by omega)
    simp only [hpow, mul_zero, zero_div, tsum_zero]
  have hlocal : (fun w => jacobiThetaFourTau (π * w) τ) =ᶠ[𝓝 0]
      fun w => jacobiThetaFourNullTau τ * cexp (-S w) := by
    filter_upwards [hsmall1, hsmall2] with w hw1 hw2
    by_cases hw0 : w = 0
    · subst w
      rw [mul_zero, hzero]
      simp only [neg_zero, exp_zero, mul_one, jacobiThetaFourNullTau]
    · obtain ⟨S1, hS1, he1⟩ := jacobiThetaOneTau_powerSeries hτ hw1
      obtain ⟨S2, hS2, he2⟩ := jacobiThetaOneTau_powerSeries hτh hw2
      have hdiff : HasSum (fun j => f j w) (S2 - S1) := by
        convert hS2.sub hS1 using 1
        funext j
        dsimp only [f, c]
        rw [hγ j]
        ring_nf
      have hS : S w = S2 - S1 := hdiff.tsum_eq
      have hp := hprod (π * w)
      rw [he1, he2] at hp
      have hexp : cexp (-S1) * cexp (-(S2 - S1)) = cexp (-S2) := by
        rw [← exp_add]
        congr 1
        ring_nf
      have hr : π * w * jacobiThetaOneDerivNullTau (τ / 2) * cexp (-S2) *
          jacobiThetaTwoNullTau (τ / 2) =
          2 * ((π * w * jacobiThetaOneDerivNullTau τ * cexp (-S1)) *
            (jacobiThetaFourNullTau τ * cexp (-(S2 - S1)))) := by
        calc
          _ = π * w * (jacobiThetaOneDerivNullTau (τ / 2) *
              jacobiThetaTwoNullTau (τ / 2)) * cexp (-S2) := by ring_nf
          _ = _ := by rw [hconst, ← hexp]; ring_nf
      rw [hr] at hp
      have hh := mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) hp
      rw [hS]
      exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (ofReal_ne_zero.mpr Real.pi_ne_zero) hw0) (hD τ hτ)) (exp_ne_zero _)) hh
  have hleft : AnalyticOnNhd ℂ (fun w => jacobiThetaFourTau (π * w) τ) U := by
    intro w _
    exact ((hθ4.comp (differentiable_const _ |>.mul differentiable_id)).analyticAt w)
  have hright : AnalyticOnNhd ℂ (fun w => jacobiThetaFourNullTau τ * cexp (-S w)) U := by
    intro w hw
    exact analyticAt_const.mul ((haS w hw).neg.cexp)
  refine ⟨S z, (summable_norm_iff.mp (hs z hz)).hasSum, ?_⟩
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconn hU0 hlocal hz

end DLMF.Theta.LogarithmicTheta
