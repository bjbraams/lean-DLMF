/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Derivatives
public import DLMF.Hypergeometric.EulerIntegral
public import DLMF.Statistical.Basic.IncompleteBeta

/-!
# Incomplete Beta functions: hypergeometric form (Temme §11.3; DLMF §8.17)

The incomplete Beta functions `Real.incBeta` and `Real.normIncBetaI` and their basic properties
are in `DLMF.Statistical.Basic.IncompleteBeta`.

## Main results

* `Real.incBeta_eq_ordinaryHypergeometric`: `B_x(a,b) = xᵃ/a · F(a, 1-b; a+1; x)` for
  `0 < x < 1` (DLMF 8.17.7), from Euler's integral.
-/

@[expose] public section

open Complex Set MeasureTheory intervalIntegral
open scoped Real
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Statistical

/-- The hypergeometric form `B_x(a,b) = xᵃ/a · F(a, 1-b; a+1; x)` for `0 < x < 1`
(DLMF 8.17.7), from Euler's integral after the substitution `t = xs`. -/
@[dlmf 8.17.E7]
theorem Real.incBeta_eq_ordinaryHypergeometric {a : ℂ} (ha : 0 < a.re) (b : ℂ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    Real.incBeta a b x = (x : ℂ) ^ a / a * ₂F₁ a (1 - b) (a + 1) (x : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hxn : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hx0.le]; exact hx1
  have hE := ordinaryHypergeometric_eq_integral (a := 1 - b) (b := a) (c := a + 1)
    ha (by simp) hxn
  rw [show a + 1 - a = 1 by ring, Gamma_one, mul_one, Gamma_add_one a ha0] at hE
  have hsub : Real.incBeta a b x = (x : ℂ) * ∫ s in (0 : ℝ)..1,
      ((x * s : ℝ) : ℂ) ^ (a - 1) * (1 - ((x * s : ℝ) : ℂ)) ^ (b - 1) := by
    have h := intervalIntegral.integral_comp_mul_left
      (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) (a := 0) (b := 1) hx0.ne'
    rw [mul_zero, mul_one] at h
    rw [Real.incBeta, h, real_smul, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hx0.ne',
      ofReal_one, one_mul]
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  rw [hsub, DLMF.Hypergeometric.ordinaryHypergeometric_symm, hE, mul_div_assoc, div_self hΓ,
    mul_one]
  have hcongr : ∫ s in (0 : ℝ)..1, ((x * s : ℝ) : ℂ) ^ (a - 1) * (1 - ((x * s : ℝ) : ℂ)) ^ (b - 1) =
      ∫ s in (0 : ℝ)..1, (x : ℂ) ^ (a - 1) * ((s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ ((1 : ℂ) - 1) *
        (1 - (x : ℂ) * s) ^ (-(1 - b))) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by rw [uIcc_of_le zero_le_one] at hs; exact hs.1
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hx0.le hs0, sub_self, cpow_zero, mul_one,
      show -(1 - b) = b - 1 by ring]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hx : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  rw [show (x : ℂ) ^ a = (x : ℂ) ^ (a - 1) * x by
    rw [cpow_sub _ _ hx, cpow_one]; field_simp]
  field_simp

end DLMF.Statistical
