/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.Theta.Basic.Analytic
import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!
# Second theta derivatives and their Fourier series

The second amplitude derivative of `θ₄` at zero is a Gaussian Fourier series and depends
holomorphically on the lattice parameter in the upper half-plane (DLMF §20.2(i)–(ii)).

## Main results

* `jacobiThetaFourTau_second_deriv_eq_tsum`: the integer Fourier series.
* `jacobiThetaFourTau_second_deriv_zero_hasSum`: the series over positive integers.
* `differentiableOn_jacobiThetaFourTau_second_deriv_zero`: holomorphy in the lattice parameter.

## Implementation notes

The proof uses Mathlib's Gaussian estimates for `jacobiTheta₂_term` and termwise differentiation
from `Complex.iteratedDeriv_tsum_of_locally_dominated`.
-/

open Complex Set Filter Topology
open scoped Real
namespace DLMF.Theta
open DLMF.Elliptic

/-- The theta-four summand separates its amplitude and lattice parameter. -/
private lemma thetaFour_term_factor (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n ((z + π / 2) / π) τ =
      ((-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ)) * cexp ((2 * I * n) * z) := by
  rw [jacobiTheta₂_term, neg_one_zpow_eq_exp]
  simp only [← exp_add]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

/-- The second derivative of the fourth theta function as an integer Fourier series. -/
public theorem jacobiThetaFourTau_second_deriv_eq_tsum {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (deriv (fun z => jacobiThetaFourTau z τ)) 0 =
      -4 * ∑' n : ℤ, (n : ℂ) ^ 2 * (-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ) := by
  let f : ℤ → ℂ → ℂ := fun n z => jacobiTheta₂_term n ((z + π / 2) / π) τ
  let g : ℤ → ℝ := fun n => Real.exp (-π * (τ.im * n ^ 2 - 2 * (1 / π) * |n|))
  have hg : Summable g := by
    simpa only [pow_zero, one_mul] using summable_pow_mul_jacobiTheta₂_term_bound (1 / π) hτ 0
  have hb (n : ℤ) (z : ℂ) (hz : z ∈ Metric.ball 0 1) : ‖f n z‖ ≤ g n := by
    apply norm_jacobiTheta₂_term_le hτ _ le_rfl n
    have him : (((z + (π : ℂ) / 2) / π)).im = z.im / π := by
      simp [Complex.div_ofReal_im]
    rw [him, abs_div, abs_of_pos Real.pi_pos]
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    exact (abs_im_le_norm z).trans (le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hz))
  have hD := Complex.iteratedDeriv_tsum_of_locally_dominated Metric.isOpen_ball
    (f := f) (fun n => (by dsimp only [f]; unfold jacobiTheta₂_term; fun_prop))
    (fun z hz => ⟨Metric.ball 0 1, Metric.isOpen_ball.mem_nhds hz, g, hg, hb⟩) 2
    (by simp : (0 : ℂ) ∈ Metric.ball 0 1)
  have heq : (fun z => ∑' n : ℤ, f n z) = fun z => jacobiThetaFourTau z τ := by
    rfl
  rw [heq] at hD
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hD
  rw [hD, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : f n = fun z =>
      ((-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ)) * cexp ((2 * I * n) * z) := by
    funext z
    exact thetaFour_term_factor n z τ
  have hterm := iteratedDeriv_const_mul_field (n := 2) (x := 0)
    ((-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ)) (fun z => cexp ((2 * I * n) * z))
  simp only [iteratedDeriv_cexp_const_mul] at hterm
  rw [he]
  have hterm' : deriv (deriv (fun z =>
      ((-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ)) * cexp ((2 * I * n) * z))) 0 =
        ((-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ)) *
          ((2 * I * n) ^ 2 * cexp ((2 * I * n) * 0)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hterm
  rw [hterm']
  simp only [mul_zero, exp_zero, mul_one]
  ring_nf
  simp only [I_sq]
  ring

/-- Integer powers preserve Gaussian summability of theta-four summands. -/
private lemma summable_thetaFour_null_weighted {τ : ℂ} (hτ : 0 < τ.im) (j : ℕ) :
    Summable (fun n : ℤ => (n : ℂ) ^ j * (-1 : ℂ) ^ n *
      cexp (π * I * n ^ 2 * τ)) := by
  apply (summable_pow_mul_jacobiTheta₂_term_bound 0 hτ j).of_norm_bounded
  intro n
  have he : cexp (π * I * n ^ 2 * τ) = jacobiTheta₂_term n 0 τ := by
    simp only [jacobiTheta₂_term, mul_zero, zero_add]
  rw [he, norm_mul, norm_mul, norm_pow, norm_zpow, norm_neg, norm_one, one_zpow,
    mul_one, norm_intCast, norm_jacobiTheta₂_term]
  simp only [zero_im, mul_zero, sub_zero]
  rw [Int.cast_abs]
  apply le_of_eq
  congr 2
  ring

/-- The Fourier series of the second derivative of the fourth theta function at zero. -/
public theorem jacobiThetaFourTau_second_deriv_zero_hasSum {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ 2 *
      cexp (π * I * τ) ^ ((n + 1) ^ 2))
      (-deriv (deriv (fun z => jacobiThetaFourTau z τ)) 0 / 8) := by
  have h := (summable_thetaFour_null_weighted hτ 2).hasSum.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero,
    Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero, neg_zero, sub_zero] at h
  have ht (n : ℕ) :
      (((n + 1 : ℕ) : ℂ) ^ 2 * (-1 : ℂ) ^ ((n + 1 : ℕ) : ℤ) *
        cexp (π * I * ((n + 1 : ℕ) : ℂ) ^ 2 * τ) +
      (-((n + 1 : ℕ) : ℂ)) ^ 2 * (-1 : ℂ) ^ (-((n + 1 : ℕ) : ℤ)) *
        cexp (π * I * (-((n + 1 : ℕ) : ℂ)) ^ 2 * τ)) =
      2 * ((-1 : ℂ) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ 2 *
        cexp (π * I * τ) ^ ((n + 1) ^ 2)) := by
    have he : cexp (π * I * τ) ^ ((n + 1) ^ 2) =
        cexp (π * I * ((n + 1 : ℕ) : ℂ) ^ 2 * τ) := by
      rw [← exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one, neg_sq, he]
    ring
  have h' := (h.congr_fun fun n => (ht n).symm).div_const 2
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] at h'
  convert h' using 1
  rw [jacobiThetaFourTau_second_deriv_eq_tsum hτ]
  ring

/-- The second theta-four derivative at zero is holomorphic in the upper half-plane. -/
public theorem differentiableOn_jacobiThetaFourTau_second_deriv_zero :
    DifferentiableOn ℂ (fun τ => deriv (deriv (fun z => jacobiThetaFourTau z τ)) 0)
      {τ : ℂ | 0 < τ.im} := by
  have hs : DifferentiableOn ℂ (fun τ => ∑' n : ℤ, (n : ℂ) ^ 2 * (-1 : ℂ) ^ n *
      cexp (π * I * n ^ 2 * τ)) {τ : ℂ | 0 < τ.im} := by
    intro τ hτ
    have hτ0 : 0 < τ.im := hτ
    let T := τ.im / 2
    have hT : 0 < T := half_pos hτ
    let U : Set ℂ := {σ | T < σ.im}
    have hU : IsOpen U := isOpen_lt continuous_const continuous_im
    have hm := summable_pow_mul_jacobiTheta₂_term_bound 0 hT 2
    have hf := Complex.differentiableOn_tsum_of_summable_norm hm
      (fun n => (by fun_prop : Differentiable ℂ (fun σ : ℂ =>
        (n : ℂ) ^ 2 * (-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * σ))).differentiableOn)
      hU (fun n σ hσ => ?_)
    · have hmem : τ ∈ U := by dsimp only [U, T, mem_ofPred_eq]; linarith [hτ0]
      exact (hf.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
    · have he : cexp (π * I * n ^ 2 * σ) = jacobiTheta₂_term n 0 σ := by
        simp only [jacobiTheta₂_term, mul_zero, zero_add]
      rw [he, norm_mul, norm_mul, norm_pow, norm_zpow, norm_neg, norm_one,
        one_zpow, mul_one, norm_intCast]
      simpa only [Int.cast_abs] using mul_le_mul_of_nonneg_left
        (norm_jacobiTheta₂_term_le (S := 0) (z := 0) hT (by norm_num) hσ.le n)
        (sq_nonneg |(n : ℝ)|)
  exact (hs.const_mul (-4)).congr (fun τ hτ =>
    jacobiThetaFourTau_second_deriv_eq_tsum hτ)
end DLMF.Theta
