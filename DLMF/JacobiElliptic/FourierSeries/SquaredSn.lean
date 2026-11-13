/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
public import DLMF.Elliptic.Basic.Integrals
import DLMF.JacobiElliptic.Related.EpsilonTheta
import DLMF.Theta.Products.LogDerivativeFourier
import DLMF.JacobiElliptic.EisensteinSeries
import DLMF.JacobiElliptic.Addition.ThetaAndQuotients
import DLMF.Theta.SeriesAndZeros

/-!
# Fourier series for the square of Jacobi's sine

The series in DLMF 22.11.13 follows by differentiating the theta logarithmic derivative
series, with its constant term determined by the value of Jacobi's Epsilon at `2K`.
-/

public section

set_option maxHeartbeats 0

open Complex Filter DLMF.Elliptic DLMF.Theta DLMF.EllipticIntegrals
open scoped Real Topology

namespace DLMF.JacobiElliptic

/-- DLMF 22.11.13: `sn²(z,k) = (1 - E/K)/k² - (2π²/(k²K²)) ∑_{n≥1} n qⁿ cos(2nζ)/(1 - q^{2n})`,
for real `0 < k < 1`, `E = E(k)`, and `q e^{2|Im ζ|} < 1`. -/
@[dlmf 22.11.E13 "special case: real 0 < k < 1 (complex E(k) not yet defined)"]
theorem jacobiSn_sq_hasSum_fourier {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1) {z : ℂ}
    (hq : ‖jacobiNome κ‖ * Real.exp (2 * |(jacobiThetaArgument z κ).im|) < 1) :
    HasSum (fun n : ℕ => 2 * π ^ 2 / ((κ : ℂ) ^ 2 * completeEllipticK κ ^ 2) * (n + 1) *
        jacobiNome κ ^ (n + 1) / (1 - jacobiNome κ ^ (2 * (n + 1))) *
          cos (2 * (n + 1) * jacobiThetaArgument z κ))
      (1 / (κ : ℂ) ^ 2 * (1 - (DLMF.Elliptic.Real.completeEllipticEOfParameter (κ ^ 2) : ℂ) /
          completeEllipticK κ) -
        jacobiSn z κ ^ 2) := by
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  let τ := jacobiTau (κ : ℂ)
  let A := jacobiThetaThreeTau 0 τ ^ 2
  have hτ : 0 < τ.im := jacobiTau_im_pos hk
  have hA : A ≠ 0 := pow_ne_zero 2 (jacobiThetaThreeTau_zero_ne_zero hτ)
  have hkne : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hk0)
  have hKne := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hK := (jacobi_inversion_k hk).2.2
  have hAscale : A = 2 * completeEllipticK (κ : ℂ) / π := by
    rw [completeEllipticKOfTau] at hK
    apply (eq_div_iff (ofReal_ne_zero.mpr Real.pi_ne_zero)).2
    linear_combination 2 * hK
  have harg (w : ℂ) : jacobiThetaArgument w (κ : ℂ) = w / A := by
    rw [jacobiThetaArgument, hAscale]
    field_simp [hKne]
  have hs : |(jacobiThetaArgument z (κ : ℂ)).im| < π * τ.im / 2 := by
    rw [jacobiNome_eq_exp_jacobiTau hk, Complex.norm_exp,
      ← Real.exp_add, Real.exp_lt_one_iff] at hq
    have he : (π * I * τ).re = -(π * τ.im) := by simp
    change (π * I * τ).re + 2 * |(jacobiThetaArgument z κ).im| < 0 at hq
    rw [he] at hq
    linarith
  have hz4 : jacobiThetaFourTau (z / A) τ ≠ 0 := by
    rw [← harg, Ne, (jacobiThetaTau_eq_zero_iff hτ _).2.2.2]
    rintro ⟨m, n, he⟩
    have hi := congrArg Complex.im he
    simp only [mul_im, add_im, intCast_im, ofReal_im, ofReal_re, intCast_re, div_ofNat_re,
      div_ofNat_im, add_re, mul_zero, zero_add, one_re, one_im] at hi
    have hi' : (jacobiThetaArgument z κ).im = ((n : ℝ) + 1 / 2) * (τ.im * π) := by
      simpa [mul_assoc] using hi
    have hp : 0 < τ.im * π := mul_pos hτ Real.pi_pos
    have hs' : |(n : ℝ) + 1 / 2| < 1 / 2 := by
      apply (mul_lt_mul_iff_of_pos_right hp).mp
      simpa only [hi', abs_mul, abs_of_pos hτ, abs_of_pos Real.pi_pos, div_eq_mul_inv,
        mul_assoc, mul_comm, mul_left_comm, one_mul] using hs
    have hn0 : n < 0 := by exact_mod_cast (show (n : ℝ) < 0 by linarith [(abs_lt.mp hs').2])
    have hn1 : (-1 : ℤ) < n := by
      exact_mod_cast (show (-1 : ℝ) < n by linarith [(abs_lt.mp hs').1])
    omega
  have hr : IsJacobiRegular .n z (κ : ℂ) := by
    rw [IsJacobiRegular, jacobiLetterTheta, harg]
    exact div_ne_zero hz4 (jacobiThetaFourTau_zero_ne_zero hτ)
  have hraw := EpsilonTheta.hasDerivAt_thetaFour_logDeriv hτ hz4
  have hcomp := ((hraw.comp z ((hasDerivAt_id z).div_const A)).div_const A)
  have hnorm := EpsilonTheta.hasDerivAt_normalized_thetaFour_logDeriv hk hr
  have heqfun : (fun w : ℂ => deriv (fun u => jacobiThetaFourTau u τ) (w / A) /
        (A * jacobiThetaFourTau (w / A) τ)) =
      fun w => (deriv (fun u => jacobiThetaFourTau u τ) (w / A) /
        jacobiThetaFourTau (w / A) τ) / A := by
    funext w
    rw [div_div, mul_comm A]
  change HasDerivAt _
    (deriv (deriv (fun u => jacobiThetaFourTau u τ)) 0 /
      (A ^ 2 * jacobiThetaFourTau 0 τ) - (κ : ℂ) ^ 2 * jacobiSn z κ ^ 2) z at hnorm
  rw [heqfun] at hnorm
  have heqd := hnorm.unique hcomp
  have hsraw := jacobiThetaFourTau_logDeriv_deriv_hasSum hτ hs
  rw [harg, hraw.deriv] at hsraw
  have hc := EpsilonTheta.thetaFour_second_deriv_zero_div_eq hk0 hk1
  have hc' : deriv (deriv (fun u => jacobiThetaFourTau u τ)) 0 /
      (A ^ 2 * jacobiThetaFourTau 0 τ) =
      1 - (DLMF.Elliptic.Real.completeEllipticEOfParameter (κ ^ 2) : ℂ) /
        completeEllipticK κ := by
    convert hc using 1
    dsimp only [A, τ]
    ring_nf
  have hcoef : 8 / (A ^ 2 * (κ : ℂ) ^ 2) =
      2 * π ^ 2 / ((κ : ℂ) ^ 2 * completeEllipticK κ ^ 2) := by
    rw [hAscale]
    field_simp [hKne, hkne]
    ring_nf
  convert hsraw.div_const (A ^ 2 * (κ : ℂ) ^ 2) using 1
  · funext n
    rw [jacobiNome_eq_exp_jacobiTau hk, harg]
    dsimp only [τ]
    calc
      _ = (8 / (A ^ 2 * (κ : ℂ) ^ 2)) * (n + 1) *
          (cexp (π * I * jacobiTau κ) ^ (n + 1) /
            (1 - cexp (π * I * jacobiTau κ) ^ (2 * (n + 1)))) *
          cos (2 * (n + 1) * (z / A)) := by rw [hcoef]; ring_nf
      _ = _ := by ring_nf
  · rw [div_mul_eq_div_div]
    have heqd' : _ = _ := heqd
    simp only [← mul_div_assoc, mul_one, div_div, ← pow_two] at heqd'
    rw [← heqd', hc']
    field_simp [hkne]

end DLMF.JacobiElliptic
