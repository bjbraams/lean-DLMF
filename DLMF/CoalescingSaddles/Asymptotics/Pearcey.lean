/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
import DLMF.CoalescingSaddles.CanonicalIntegrals.PearceyBessel
import DLMF.Bessel.Asymptotics

/-!
# The Pearcey asymptotic on the negative symmetry axis

The quarter-order Bessel evaluation of the Pearcey integral gives its two oscillatory
leading terms as the symmetry-line argument tends to minus infinity (DLMF 36.11.3).
The normalized Bessel error tends to zero, and the remaining exponential has unit norm.

* `cuspoidIntegral_two_zero_atBot`: the negative-axis Pearcey asymptotic.

The proof reuses `PearceySymmetryLine.value_bessel` and
`DLMF.Bessel.besselJ_sub_cos_mul_sqrt_tendsto_zero`, with Mathlib's complex exponential,
real square-root and asymptotic-calculus APIs.
-/

public noncomputable section

open Complex Filter Asymptotics
open scoped Real Topology

namespace DLMF.CoalescingSaddles

set_option maxHeartbeats 1000000 in
/-- The Pearcey integral on the symmetry line `x = 0`, `y → -∞` (DLMF 36.11.3):
`Ψ₂(0, y) = √(π/|y|) exp(-iπ/4)(1 + i√2 exp(-iy²/4) + o(1))`. -/
@[dlmf 36.11.E3]
theorem cuspoidIntegral_two_zero_atBot :
    (fun y : ℝ => cuspoidIntegral 2 ![0, y] -
        (Real.sqrt (π / |y|) : ℂ) * exp (-(I * π / 4)) *
          (1 + I * Real.sqrt 2 * exp (-(I * y ^ 2 / 4)))) =o[atBot]
      (fun y : ℝ => Real.sqrt (π / |y|)) := by
  have hR {y : ℝ} (hy : y < 0) :
      cuspoidIntegral 2 ![0, y] -
        (Real.sqrt (π / |y|) : ℂ) * exp (-(I * π / 4)) *
          (1 + I * Real.sqrt 2 * exp (-(I * (y : ℂ) ^ 2 / 4))) =
        (Real.sqrt (π / |y|) : ℂ) * Real.sqrt π * exp (-I * (y : ℂ) ^ 2 / 8) *
          (exp (I * π / 8) * ((Complex.besselJ (-1 / 4) ((y : ℂ) ^ 2 / 8) -
            (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ) * cos ((y : ℂ) ^ 2 / 8 - π / 8)) *
              (Real.sqrt (y ^ 2 / 8) : ℂ)) +
          exp (-I * π / 8) * ((Complex.besselJ (1 / 4) ((y : ℂ) ^ 2 / 8) -
            (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ) * cos ((y : ℂ) ^ 2 / 8 - 3 * π / 8)) *
              (Real.sqrt (y ^ 2 / 8) : ℂ))) := by
    have phase_combination (t : ℂ) :
        exp (I * π / 8) * cos (t - π / 8) +
          exp (-I * π / 8) * cos (t - 3 * π / 8) =
            exp (-(I * π / 4)) / (Real.sqrt 2 : ℂ) * exp (I * t) +
              I * exp (-(I * π / 4)) * exp (-(I * t)) := by
      have hphase : exp (-(I * π / 4)) =
          ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I) := by
        rw [show -(I * (π : ℂ) / 4) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring,
          exp_mul_I, ← ofReal_cos, ← ofReal_sin]
        simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
          ofReal_div, ofReal_ofNat, ofReal_neg]
        ring
      have hp : exp (I * π / 4) = I * exp (-(I * π / 4)) := by
        calc
          _ = exp (π / 2 * I) * exp (-(I * π / 4)) := by
            rw [← exp_add]; congr 1; ring
          _ = _ := by rw [exp_pi_div_two_mul_I]
      have hm : exp (-I * π / 2) = -I := by
        convert exp_neg_pi_div_two_mul_I using 1; congr 1; ring
      have h1 : exp (I * π / 8) * exp ((t - π / 8) * I) = exp (I * t) := by
        rw [← exp_add]; congr 1; ring
      have h2 : exp (I * π / 8) * exp (-(t - π / 8) * I) =
          exp (I * π / 4) * exp (-(I * t)) := by
        rw [← exp_add, ← exp_add]; congr 1; ring
      have h3 : exp (-I * π / 8) * exp ((t - 3 * π / 8) * I) =
          -I * exp (I * t) := by
        calc
          _ = exp (-I * π / 2) * exp (I * t) := by
            rw [← exp_add, ← exp_add]; congr 1; ring
          _ = _ := by rw [hm]
      have h4 : exp (-I * π / 8) * exp (-(t - 3 * π / 8) * I) =
          exp (I * π / 4) * exp (-(I * t)) := by
        rw [← exp_add, ← exp_add]; congr 1; ring
      simp only [cos]
      rw [← mul_div_assoc, ← mul_div_assoc, mul_add, mul_add, h1, h2, h3, h4, hp]
      rw [hphase]
      have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
      push_cast
      field_simp [hs]
      ring_nf
    have prefactor {y : ℝ} (hy : y ≠ 0) :
        π / 2 * Real.sqrt (|y| / 2) * Real.sqrt (2 / (π * (y ^ 2 / 8))) =
          Real.sqrt (π / |y|) * Real.sqrt 2 := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
      have habs : |y| ^ 2 = y ^ 2 := sq_abs y
      have hy0 : |y| ≠ 0 := abs_ne_zero.mpr hy
      field_simp
      nlinarith [habs]
    have normalization {y : ℝ} (hy : y ≠ 0) :
        π / 2 * Real.sqrt (|y| / 2) =
          Real.sqrt (π / |y|) * Real.sqrt π * Real.sqrt (y ^ 2 / 8) := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt (by positivity)]
      have hy0 : |y| ≠ 0 := abs_ne_zero.mpr hy
      field_simp
      nlinarith [sq_abs y]
    have leading_term {y : ℝ} (hy : y ≠ 0) :
        (π / 2 * (Real.sqrt (|y| / 2) : ℂ)) * exp (-I * (y : ℂ) ^ 2 / 8) *
          ((exp (I * π / 8) * (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ) *
              cos ((y : ℂ) ^ 2 / 8 - π / 8)) +
           (exp (-I * π / 8) * (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ) *
              cos ((y : ℂ) ^ 2 / 8 - 3 * π / 8))) =
          (Real.sqrt (π / |y|) : ℂ) * exp (-(I * π / 4)) *
            (1 + I * Real.sqrt 2 * exp (-(I * (y : ℂ) ^ 2 / 4))) := by
      have hp : (π / 2 * (Real.sqrt (|y| / 2) : ℂ)) *
          (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ) =
            (Real.sqrt (π / |y|) : ℂ) * Real.sqrt 2 := by
        exact_mod_cast prefactor hy
      calc
        _ = ((π / 2 * (Real.sqrt (|y| / 2) : ℂ)) *
            (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ)) * exp (-I * (y : ℂ) ^ 2 / 8) *
              (exp (I * π / 8) * cos ((y : ℂ) ^ 2 / 8 - π / 8) +
                exp (-I * π / 8) * cos ((y : ℂ) ^ 2 / 8 - 3 * π / 8)) := by ring
        _ = _ := by
          rw [hp, phase_combination]
          have he1 : exp (-I * (y : ℂ) ^ 2 / 8) * exp (I * ((y : ℂ) ^ 2 / 8)) = 1 := by
            rw [← exp_add]; ring_nf; exact exp_zero
          have he2 : exp (-I * (y : ℂ) ^ 2 / 8) * exp (-(I * ((y : ℂ) ^ 2 / 8))) =
              exp (-(I * (y : ℂ) ^ 2 / 4)) := by
            rw [← exp_add]; congr 1; ring
          have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
          have hc : (Real.sqrt 2 : ℂ) * (exp (-(I * π / 4)) / Real.sqrt 2) =
              exp (-(I * π / 4)) := by field_simp
          have harg : -I * (y : ℂ) ^ 2 / 8 = -(I * ((y : ℂ) ^ 2 / 8)) := by ring
          rw [harg] at he1 he2 ⊢
          calc
            _ = (Real.sqrt (π / |y|) : ℂ) *
                ((Real.sqrt 2 : ℂ) * (exp (-(I * π / 4)) / Real.sqrt 2)) *
                  (exp (-(I * ((y : ℂ) ^ 2 / 8))) * exp (I * ((y : ℂ) ^ 2 / 8))) +
                (Real.sqrt (π / |y|) : ℂ) * Real.sqrt 2 * I * exp (-(I * π / 4)) *
                  (exp (-(I * ((y : ℂ) ^ 2 / 8))) * exp (-(I * ((y : ℂ) ^ 2 / 8)))) := by ring
            _ = _ := by rw [hc, he1, he2]; ring
    have remainder_eq {y : ℝ} (hy : y < 0) :
        cuspoidIntegral 2 ![0, y] -
          (Real.sqrt (π / |y|) : ℂ) * exp (-(I * π / 4)) *
            (1 + I * Real.sqrt 2 * exp (-(I * (y : ℂ) ^ 2 / 4))) =
          (π / 2 * (Real.sqrt (|y| / 2) : ℂ)) * exp (-I * (y : ℂ) ^ 2 / 8) *
            (exp (I * π / 8) * (Complex.besselJ (-1 / 4) ((y : ℂ) ^ 2 / 8) -
              (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ) * cos ((y : ℂ) ^ 2 / 8 - π / 8)) +
            exp (-I * π / 8) * (Complex.besselJ (1 / 4) ((y : ℂ) ^ 2 / 8) -
              (Real.sqrt (2 / (π * (y ^ 2 / 8))) : ℂ) * cos ((y : ℂ) ^ 2 / 8 - 3 * π / 8))) := by
      rw [PearceySymmetryLine.value_bessel hy.ne]
      rw [ite_eq_right (not_lt_of_ge hy.le)]
      have h := leading_term hy.ne
      linear_combination h
    rw [remainder_eq hy]
    have hn : π / 2 * (Real.sqrt (|y| / 2) : ℂ) =
        (Real.sqrt (π / |y|) : ℂ) * Real.sqrt π * Real.sqrt (y ^ 2 / 8) := by
      exact_mod_cast normalization hy.ne
    rw [hn]
    ring
  have ht : Tendsto (fun y : ℝ => y ^ 2 / 8) atBot atTop := by
    have h := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_abs_atBot_atTop
    simpa only [Function.comp_def, sq_abs, div_eq_mul_inv] using
      h.atTop_mul_const (by norm_num : (0 : ℝ) < (8 : ℝ)⁻¹)
  have hm := (DLMF.Bessel.besselJ_sub_cos_mul_sqrt_tendsto_zero (-1 / 4)).comp ht
  have hp := (DLMF.Bessel.besselJ_sub_cos_mul_sqrt_tendsto_zero (1 / 4)).comp ht
  have hcosm (s : ℝ) : cos ((s : ℂ) - (-1 / 4) * π / 2 - π / 4) =
      cos ((s : ℂ) - π / 8) := by congr 1; ring
  have hcosp (s : ℝ) : cos ((s : ℂ) - (1 / 4) * π / 2 - π / 4) =
      cos ((s : ℂ) - 3 * π / 8) := by congr 1; ring
  simp only [Function.comp_def, hcosm, hcosp, ofReal_div, ofReal_pow, ofReal_ofNat] at hm hp
  have hN := (isLittleO_one_iff ℝ).mpr
    (by simpa only [mul_zero, add_zero] using
      (hm.const_mul (exp (I * π / 8))).add (hp.const_mul (exp (-I * π / 8))))
  have hU : (fun y : ℝ => (Real.sqrt π : ℂ) * exp (-I * (y : ℂ) ^ 2 / 8)) =O[atBot]
      (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound (Real.sqrt π) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_exp]
    simp [← ofReal_pow]
  have hW : (fun y : ℝ => (Real.sqrt (π / |y|) : ℂ)) =O[atBot]
      (fun y : ℝ => Real.sqrt (π / |y|)) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun y => by simp)
  refine (hW.mul_isLittleO (hU.mul_isLittleO hN)).congr' ?_
    (Eventually.of_forall fun y => by simp)
  filter_upwards [eventually_lt_atBot 0] with y hy
  simpa only [mul_assoc] using (hR hy).symm

end DLMF.CoalescingSaddles
