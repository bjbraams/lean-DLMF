/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
public import DLMF.Confluent.Basic.KummerM
public import Mathlib.Analysis.SpecialFunctions.Bessel
import DLMF.Confluent.ParabolicCylinder.EquationAndIntegrals
import DLMF.Bessel.RegularizedSeries
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Pearcey integral on its symmetry line

A quadratic substitution in the absolutely convergent rotated quartic integral identifies
`Ψ₂(0,y)` with a parabolic-cylinder function. Its two Kummer terms then give the
Bessel expression of DLMF 36.2.19 for real `y ≠ 0`.

The proof reuses `parabolicCylinderU_eq_integral`, the canonical parabolic-cylinder
normalization, `besselJ_eq_kummerM`, and Mathlib's half-line changes of variables.

## Main results

* `PearceySymmetryLine.pearcey_eq_quartic`: the quartic Laplace representation.
* `PearceySymmetryLine.pearcey_eq_kummer`: the entire Kummer-function expression.
* `PearceySymmetryLine.value_bessel`: the quarter-order Bessel evaluation.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology
public noncomputable section

namespace DLMF.CoalescingSaddles.PearceySymmetryLine

/-- The Pearcey symmetry line is an absolutely convergent quartic Laplace integral. -/
lemma pearcey_eq_quartic (y : ℝ) :
    cuspoidIntegral 2 ![0, y] = 2 * exp ((π / 8:ℂ) * I) *
      ∫ r : ℝ in Ioi 0, exp (-(r:ℂ) ^ 4 + I * y * exp ((π / 4:ℂ) * I) * (r:ℂ) ^ 2) := by
  let d : ℂ := exp ((π / 8:ℂ) * I)
  let f : ℝ → ℂ := fun r => d * exp (-(r:ℂ) ^ 4 + I * y * d ^ 2 * (r:ℂ) ^ 2)
  have hd4 : d ^ 4 = I := by
    dsimp only [d]
    rw [← exp_nat_mul]
    norm_num
    rw [show (4:ℂ) * (π / 8 * I) = π / 2 * I by ring, exp_pi_div_two_mul_I]
  have hd2 : d ^ 2 = exp ((π / 4:ℂ) * I) := by
    dsimp only [d]
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hf : (fun r : ℝ => cuspoidContourDir 2 r *
      exp (I * cuspoidPotential 2 (cuspoidContour 2 r) ![0, y])) = f := by
    funext r
    simp only [cuspoidContour, cuspoidContourDir_of_even (by decide : Even 2)]
    have hθ : cuspoidAngle 2 = π / 8 := by unfold cuspoidAngle;norm_num
    have hphase (t : ℂ) : cuspoidPotential 2 t ![0, y] = t ^ 4 + y * t ^ 2 + 0 * t := by
      norm_num [cuspoidPotential, Fin.sum_univ_two]
    rw [hθ, hphase]
    simp only [ofReal_div, ofReal_ofNat]
    -- Express the phase and contour direction in the quartic normal form.
    change d * exp (I * ((((r:ℂ) * d) ^ 4) + y * ((r:ℂ) * d) ^ 2 + 0 * ((r:ℂ) * d))) = f r
    dsimp only [f]
    congr 2
    rw [mul_pow, hd4]
    simp only [zero_mul, add_zero]
    linear_combination (r:ℂ) ^ 4 * I_sq
  have hfi : Integrable f := hf ▸ integrable_cuspoidIntegral_integrand 2 ![0, y]
  have hneg := integral_comp_neg_Ioi 0 f
  rw [neg_zero] at hneg
  have hsymm : (fun r : ℝ => f (-r)) = f := by
    funext r
    dsimp only [f]
    rw [ofReal_neg]
    congr 2; ring
  rw [hsymm] at hneg
  unfold cuspoidIntegral
  rw [hf, ← intervalIntegral.integral_Iic_add_Ioi hfi.integrableOn hfi.integrableOn (b:=0),
    ← hneg]
  simp only [f, hd2]
  rw [integral_const_mul]
  dsimp only [d]
  ring

/-- The Pearcey symmetry line is a linear combination of two entire Kummer functions. -/
lemma pearcey_eq_kummer (y : ℝ) :
    cuspoidIntegral 2 ![0, y] =
      π * exp ((π / 8:ℂ) * I) / (Real.sqrt 2 * Gamma (3 / 4)) *
        DLMF.Confluent.kummerM (1 / 4) (1 / 2) (-I * (y:ℂ) ^ 2 / 4) -
      π * (y:ℂ) * exp (-(π / 8:ℂ) * I) / (Real.sqrt 2 * Gamma (1 / 4)) *
        DLMF.Confluent.kummerM (3 / 4) (3 / 2) (-I * (y:ℂ) ^ 2 / 4) := by
  have hsqrtTwoPower : (Real.sqrt 2 : ℂ) ^ (-1 / 2:ℂ) = (2:ℂ) ^ (-1 / 4:ℂ) := by
    rw [Real.sqrt_eq_rpow, ← cpow_mul_ofReal_nonneg (by norm_num : (0:ℝ)≤2) (1 / 2)]
    norm_num
  have hquarticIntegral (b : ℂ) :
      (∫ t : ℝ in Ioi 0, exp (-(t:ℂ) ^ 4 + b * (t:ℂ) ^ 2)) =
        (1 / 2:ℂ) * (Real.sqrt 2 : ℂ) ^ (-1 / 2:ℂ) * Gamma (1 / 2) *
          exp ((-b / (Real.sqrt 2 : ℂ)) ^ 2 / 4) *
          DLMF.Confluent.parabolicCylinderU 0 (-b / (Real.sqrt 2 : ℂ)) := by
    have hsubstitution (b : ℂ) :
        (∫ t : ℝ in Ioi 0, exp (-(t:ℂ) ^ 4 + b * (t:ℂ) ^ 2)) =
          (1 / 2 : ℂ) * ∫ r : ℝ in Ioi 0, (r:ℂ) ^ (-1 / 2:ℂ) * exp (-(r:ℂ) ^ 2 + b * r) := by
      have h := integral_comp_rpow_Ioi_of_pos (g := fun r : ℝ =>
        (r:ℂ) ^ (-1 / 2:ℂ) * exp (-(r:ℂ) ^ 2 + b * r)) (by norm_num : (0:ℝ)<2)
      have he (t : ℝ) (ht : 0 < t) :
          (2 * t ^ (2 - 1:ℝ)) • (((t ^ (2:ℝ):ℝ):ℂ) ^ (-1 / 2:ℂ) *
            exp (-(((t ^ (2:ℝ):ℝ):ℂ)) ^ 2 + b * (t ^ (2:ℝ):ℝ))) =
          (2:ℂ) * exp (-(t:ℂ) ^ 4 + b * (t:ℂ) ^ 2) := by
        have hp : (((t ^ 2 : ℝ):ℂ)) ^ (-1 / 2:ℂ) = (t:ℂ)⁻¹ := by
          have hc : ((-1 / 2:ℝ):ℂ) = (-1 / 2:ℂ) := by norm_num
          rw [← hc, ← ofReal_cpow (sq_nonneg t) (-1 / 2:ℝ)]
          have hr : (t ^ 2) ^ (-1 / 2:ℝ) = t⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
            norm_num [Real.rpow_neg_one]
          rw [hr, ofReal_inv]
        rw [show (2 - 1:ℝ) = 1 by norm_num, Real.rpow_one, Real.rpow_two, hp]
        rw [Complex.real_smul]
        push_cast
        have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
        field_simp
      have h2 : (2:ℂ) * (∫ t : ℝ in Ioi 0, exp (-(t:ℂ) ^ 4 + b * (t:ℂ) ^ 2)) =
          ∫ r : ℝ in Ioi 0, (r:ℂ) ^ (-1 / 2:ℂ) * exp (-(r:ℂ) ^ 2 + b * r) := by
        rw [← h, ← integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Ioi fun t ht => (he t ht).symm
      linear_combination (1 / 2:ℂ) * h2

    let c : ℝ := Real.sqrt 2
    have hc : 0 < c := Real.sqrt_pos.mpr (by norm_num)
    have hc0 : (c:ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    have hc2 : (c:ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    let g : ℝ → ℂ := fun r => (r:ℂ) ^ (-1 / 2:ℂ) * exp (-(r:ℂ) ^ 2 / 2 + (b / (c:ℂ)) * r)
    have hscale := integral_comp_mul_left_Ioi g 0 hc
    simp only [mul_zero, Complex.real_smul, ofReal_inv] at hscale
    have hleft : (∫ r : ℝ in Ioi 0, g (c * r)) = (c:ℂ) ^ (-1 / 2:ℂ) *
        ∫ r : ℝ in Ioi 0, (r:ℂ) ^ (-1 / 2:ℂ) * exp (-(r:ℂ) ^ 2 + b * r) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      dsimp only [g]
      rw [ofReal_mul, mul_cpow_ofReal_nonneg hc.le hr.le]
      have he : -((c:ℂ) * r) ^ 2 / 2 + b / (c:ℂ) * ((c:ℂ) * r) = -(r:ℂ) ^ 2 + b * r := by
        rw [mul_pow, hc2]
        field_simp
      rw [he]
      ring
    rw [hleft] at hscale
    have hq : (c:ℂ) ^ (-1 / 2:ℂ) * (c:ℂ) ^ (-1 / 2:ℂ) = (c:ℂ)⁻¹ := by
      rw [← cpow_add _ _ hc0]
      rw [show (-1 / 2:ℂ) + (-1 / 2) = -1 by ring, cpow_neg, cpow_one]
    have hq0 : (c:ℂ) ^ (-1 / 2:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hc0)
    have hi : (∫ r : ℝ in Ioi 0, (r:ℂ) ^ (-1 / 2:ℂ) * exp (-(r:ℂ) ^ 2 + b * r)) =
        (c:ℂ) ^ (-1 / 2:ℂ) * ∫ r : ℝ in Ioi 0, g r := by
      apply mul_left_cancel₀ hq0
      rw [← mul_assoc, hq]
      exact hscale
    have hU := DLMF.Confluent.parabolicCylinderU_eq_integral
      (a := (0:ℂ)) (by norm_num) (-b / (c:ℂ))
    simp only [zero_sub, add_zero, neg_div] at hU
    have hUg : DLMF.Confluent.parabolicCylinderU 0 (-b / (c:ℂ)) =
        exp (-(-b / (c:ℂ)) ^ 2 / 4) / Gamma (1 / 2:ℂ) * (∫ r : ℝ in Ioi 0, g r) := by
      convert hU using 1 <;> norm_num [g, neg_div]
    have hG0 : Gamma (1 / 2:ℂ) ≠ 0 := by
      rw [Gamma_one_half_eq_sqrt]
      exact ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hJ : (∫ r : ℝ in Ioi 0, g r) = Gamma (1 / 2:ℂ) *
        exp ((-b / (c:ℂ)) ^ 2 / 4) * DLMF.Confluent.parabolicCylinderU 0 (-b / (c:ℂ)) := by
      rw [hUg]
      have he : exp ((-b / (c:ℂ)) ^ 2 / 4) * exp (-(-b / (c:ℂ)) ^ 2 / 4) = 1 := by
        rw [← exp_add]
        ring_nf
        simp
      linear_combination (norm := (field_simp [hG0];ring))
        (-(∫ r : ℝ in Ioi 0, g r)) * he
    rw [hsubstitution, hi, hJ]
    dsimp only [c]
    ring

  let d : ℂ := exp ((π / 8:ℂ) * I)
  have hd2 : d ^ 2 = exp ((π / 4:ℂ) * I) := by
    dsimp only [d]; rw [←exp_nat_mul]; congr 1; push_cast; ring
  have hd4 : d ^ 4 = I := by
    dsimp only [d]; rw [←exp_nat_mul]
    norm_num
    rw [show (4:ℂ) * (π / 8 * I) = π / 2 * I by ring, exp_pi_div_two_mul_I]
  have hdm : -I * d ^ 3 = exp (-(π / 8:ℂ) * I) := by
    dsimp only [d]
    rw [←exp_nat_mul, ←exp_neg_pi_div_two_mul_I, ←exp_add]
    congr 1
    push_cast
    ring
  let c : ℝ := Real.sqrt 2
  have hc : 0 < c := Real.sqrt_pos.mpr (by norm_num)
  have hc0 : (c:ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hc2 : (c:ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  let z : ℂ := -I * y * d ^ 2 / c
  have hz2 : z ^ 2 / 2 = -I * (y:ℂ) ^ 2 / 4 := by
    dsimp only [z]
    rw [div_pow, hc2]
    have hdd : (d ^ 2) ^ 2 = I := by simpa only [←pow_mul] using hd4
    rw [mul_pow, mul_pow, neg_sq, I_sq, hdd]
    ring
  have hzd : d * z = (y:ℂ) * exp (-(π / 8:ℂ) * I) / c := by
    calc d * z = (-I * d ^ 3) * ((y:ℂ) / c) := by dsimp only [z];ring
      _ = exp (-(π / 8:ℂ) * I) * ((y:ℂ) / c) := by rw [hdm]
      _ = _ := by ring
  have hp0 := pearcey_eq_quartic y
  rw [hquarticIntegral] at hp0
  rw [←hd2] at hp0
  have hz : -(I * (y:ℂ) * d ^ 2) / (Real.sqrt 2 : ℂ) = z := by dsimp only [z, c];ring
  rw [hz] at hp0
  rw [DLMF.Confluent.parabolicCylinderU, DLMF.Confluent.parabolicCylinderEven,
    DLMF.Confluent.parabolicCylinderOdd] at hp0
  norm_num only [zero_div, zero_add, zero_sub, add_zero] at hp0
  rw [show (-(1 / 2:ℂ)) = (-1 / 2:ℂ) by ring] at hp0
  rw [hz2, Gamma_one_half_eq_sqrt, hsqrtTwoPower] at hp0
  have he : exp (z ^ 2 / 4) * exp (-z ^ 2 / 4) = 1 := by rw [←exp_add];ring_nf;simp
  have hs : (Real.sqrt π : ℂ) ^ 2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have h22 : (2:ℂ) ^ (-1 / 4:ℂ) * (2:ℂ) ^ (1 / 4:ℂ) = 1 := by
    rw [←cpow_add _ _ two_ne_zero]
    norm_num
  have h2m : (2:ℂ) ^ (-1 / 4:ℂ) * (2:ℂ) ^ (-1 / 4:ℂ) = 1 / (Real.sqrt 2 : ℂ) := by
    rw [←hsqrtTwoPower, ←cpow_add _ _ hc0]
    norm_num [cpow_neg, cpow_one]
    rfl
  have hG1 : Gamma (1 / 4:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hG3 : Gamma (3 / 4:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  calc cuspoidIntegral 2 ![0, y] =
      d * ((2:ℂ) ^ (-1 / 4:ℂ) * (2:ℂ) ^ (-1 / 4:ℂ)) * (Real.sqrt π:ℂ) ^ 2 / Gamma (3 / 4) *
          (exp (z ^ 2 / 4) * exp (-z ^ 2 / 4)) *
            DLMF.Confluent.kummerM (1 / 4) (1 / 2) (-I * (y:ℂ) ^ 2 / 4) -
      (d * z) * ((2:ℂ) ^ (-1 / 4:ℂ) * (2:ℂ) ^ (1 / 4:ℂ)) * (Real.sqrt π:ℂ) ^ 2 / Gamma (1 / 4) *
          (exp (z ^ 2 / 4) * exp (-z ^ 2 / 4)) *
            DLMF.Confluent.kummerM (3 / 4) (3 / 2) (-I * (y:ℂ) ^ 2 / 4) := by
        rw [hp0]
        dsimp only [d]
        norm_num only [neg_div] at *
        field_simp
    _ = _ := by
      rw [h2m, h22, hs, he, hzd]
      dsimp only [d, c]
      field_simp

/-- The Bessel evaluation of the Pearcey symmetry line away from zero, DLMF 36.2.19. -/
lemma value_bessel {y : ℝ} (hy : y ≠ 0) :
    cuspoidIntegral 2 ![0, y] = π / 2 * (Real.sqrt (|y| / 2) : ℂ) * exp (-I * (y : ℂ) ^ 2 / 8) *
      (exp (I * π / 8) * Complex.besselJ (-1 / 4) ((y : ℂ) ^ 2 / 8) -
        (if 0 < y then 1 else -1 : ℂ) * exp (-I * π / 8) *
          Complex.besselJ (1 / 4) ((y : ℂ) ^ 2 / 8)) := by
  have hconversion {ν : ℂ} {s : ℝ} (hs : 0 < s)
      (hν : ∀ k : ℕ, ν + 1 ≠ -k) (h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k) :
      DLMF.Confluent.kummerM (ν + 1 / 2) (2 * ν + 1) (-2 * I * s) =
        Gamma (ν + 1) * exp (-I * s) * (s / 2:ℂ) ^ (-ν) * Complex.besselJ ν s := by
    have hK := DLMF.Confluent.kummerM_kummer_transform
      (a := ν + 1 / 2) (z := -2 * I * s) h2ν
    have hpars : 2 * ν + 1 - (ν + 1 / 2) = ν + 1 / 2 := by ring
    have harg : -(-2 * I * (s:ℂ)) = 2 * I * s := by ring
    rw [hpars, harg] at hK
    rw [hK, DLMF.Bessel.besselJ_eq_kummerM hν h2ν]
    have hs0 : (s / 2:ℂ) ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hs.ne') two_ne_zero
    have hp : (s / 2:ℂ) ^ (-ν) * (s / 2:ℂ) ^ ν = 1 := by
      rw [←cpow_add _ _ hs0]
      simp
    have he : exp (-I * (s:ℂ)) * exp (-I * s) = exp (-2 * I * s) := by
      rw [←exp_add]
      congr 1
      ring
    have hG0 := Gamma_ne_zero hν
    symm
    calc _ = ((s / 2:ℂ) ^ (-ν) * (s / 2:ℂ) ^ ν) * (exp (-I * (s:ℂ)) * exp (-I * s)) *
        DLMF.Confluent.kummerM (ν + 1 / 2) (2 * ν + 1) (2 * I * s) := by
          field_simp
      _ = _ := by rw [hp, he, one_mul]
  have hquarterPower (y : ℝ) :
      ((y:ℂ) ^ 2 / 16) ^ (1 / 4:ℂ) = (Real.sqrt |y| : ℂ) / 2 := by
    have hsq : (Real.sqrt |y| / 2) ^ 4 = y ^ 2 / 16 := by
      calc (Real.sqrt |y| / 2) ^ 4 = (Real.sqrt |y| ^ 2) ^ 2 / 16 := by ring
        _ = _ := by rw [Real.sq_sqrt (abs_nonneg y), sq_abs]
    have hp := Complex.ofReal_cpow (x := y ^ 2 / 16) (by positivity) (1 / 4:ℝ)
    norm_num only [ofReal_div, ofReal_pow, ofReal_ofNat, ofReal_one] at hp
    rw [←hp, ←hsq]
    have hr : ((Real.sqrt |y| / 2) ^ 4) ^ (1 / 4:ℝ) = Real.sqrt |y| / 2 := by
      rw [←Real.rpow_natCast, ←Real.rpow_mul (by positivity)]
      norm_num
    rw [hr, ofReal_div, ofReal_ofNat]

  have hy2 : 0 < y ^ 2 / 8 := div_pos (sq_pos_of_ne_zero hy) (by norm_num)
  have hM1 := hconversion (ν := (-1 / 4:ℂ)) hy2
    (DLMF.Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
    (DLMF.Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
  have hM2 := hconversion (ν := (1 / 4:ℂ)) hy2
    (DLMF.Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
    (DLMF.Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
  have hMp : DLMF.Confluent.kummerM (1 / 4) (1 / 2) (-I * (y:ℂ) ^ 2 / 4) =
      Gamma (3 / 4) * exp (-I * (y:ℂ) ^ 2 / 8) * ((y:ℂ) ^ 2 / 16) ^ (1 / 4:ℂ) *
        Complex.besselJ (-1 / 4) ((y:ℂ) ^ 2 / 8) := by
    convert hM1 using 1 <;> push_cast <;> congr 1 <;> norm_num <;> ring_nf
  have hMm : DLMF.Confluent.kummerM (3 / 4) (3 / 2) (-I * (y:ℂ) ^ 2 / 4) =
      Gamma (5 / 4) * exp (-I * (y:ℂ) ^ 2 / 8) * ((y:ℂ) ^ 2 / 16) ^ (-1 / 4:ℂ) *
        Complex.besselJ (1 / 4) ((y:ℂ) ^ 2 / 8) := by
    convert hM2 using 1 <;> push_cast <;> congr 1 <;> norm_num <;> ring_nf
  have hq := hquarterPower y
  have hqn : ((y:ℂ) ^ 2 / 16) ^ (-1 / 4:ℂ) = 2 / (Real.sqrt |y| : ℂ) := by
    rw [show (-1 / 4:ℂ) = -(1 / 4) by ring, cpow_neg, hq]
    field_simp
  have hG := Gamma_add_one (1 / 4:ℂ) (by norm_num)
  rw [show (1 / 4:ℂ) + 1 = 5 / 4 by ring] at hG
  have hG0 : Gamma (1 / 4:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hG3 : Gamma (3 / 4:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hs0 : (Real.sqrt |y| : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hy)).ne'
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hs : (Real.sqrt |y| : ℂ) ^ 2 = |y| := by exact_mod_cast Real.sq_sqrt (abs_nonneg y)
  have hsign : (y:ℂ) = (if 0 < y then 1 else -1:ℂ) * |y| := by
    split_ifs with hp
    · simp only [abs_of_pos hp, one_mul]
    · simp only [abs_of_neg (lt_of_le_of_ne (le_of_not_gt hp) hy), ofReal_neg,
        neg_mul, one_mul, neg_neg]
  rw [pearcey_eq_kummer, hMp, hMm, hq, hqn, hG, Real.sqrt_div (abs_nonneg y)]
  have hEp : exp ((π / 8:ℂ) * I) = exp (I * π / 8) := by congr 1;ring
  have hEm : exp (-(π / 8:ℂ) * I) = exp (-I * π / 8) := by congr 1;ring
  rw [hEp, hEm]
  simp only [ofReal_div]
  rw [hsign, ←hs]
  field_simp [hG0, hG3, hs0, hs2]
  ring

end DLMF.CoalescingSaddles.PearceySymmetryLine
