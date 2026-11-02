/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
public import DLMF.Core.Basic
public import DLMF.Airy.IntegralRepresentations
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The fold canonical integral and the Airy function

The canonical integrals of DLMF §36.2 that reduce to Airy functions.

## Main results

* `cuspoidIntegral_one`: the fold integral is an Airy function (DLMF 36.2.13).
* `hyperbolicUmbilicIntegral_z_zero`: `Ψ^{(H)}(x, y, 0)` as a product of Airy functions
  (DLMF 36.2.21).

## Implementation notes

The integrability of the contour integrands, the other special values and the symmetries
(DLMF 36.2.12–36.2.27) are in `DLMF.CoalescingSaddles.Basic.ContoursAndSymmetries`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter

open scoped Real Topology ComplexConjugate

namespace DLMF.CoalescingSaddles

/-! ### The fold: `Ψ₁` and the Airy function -/

/-- The fold ray integral along `arg t = π/6` equals `i w(x)`, with `w` the Airy ray integral. -/
private lemma integral_airyInt_osc_ray_pi_div_six (x : ℝ) :
    ∫ r in Ioi (0 : ℝ), exp (((π / 6 : ℝ) : ℂ) * I) *
      DLMF.Airy.airyInt_osc x (r * exp (((π / 6 : ℝ) : ℂ) * I)) = I * DLMF.Airy.airyInt_w x := by
  rw [DLMF.Airy.airyInt_w, DLMF.Airy.rayIntegral, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun r _ => DLMF.Airy.airyInt_osc_rotate x r

/-- For `K = 1` the sign flip `x_m ↦ (-1)^m x_m` is the identity. -/
private lemma alternating_sign_vecCons_one (x : ℝ) :
    (fun m : Fin 1 => (-1 : ℝ) ^ (m : ℕ) * ![x] m) = ![x] := by
  funext m; rw [Fin.fin_one_eq_zero m]; simp

/-- For odd `K` and `r > 0`, the integrand at `-r` is the conjugate of the integrand at `r` with
the parameters `x'_m = (-1)^m x_m`. -/
private lemma cuspoidContourIntegrand_neg_of_odd {K : ℕ} (hK : ¬ Even K) (x : Fin K → ℝ)
    {r : ℝ} (hr : 0 < r) :
    cuspoidContourDir K (-r) * exp (I * cuspoidPotential K (cuspoidContour K (-r)) x) =
      conj (cuspoidContourDir K r *
        exp (I * cuspoidPotential K (cuspoidContour K r) (fun m => (-1) ^ (m : ℕ) * x m))) := by
  have hd : conj (cuspoidContourDir K r) = cuspoidContourDir K (-r) := by
    rw [cuspoidContourDir_of_nonneg K hr.le,
        cuspoidContourDir_of_odd_of_neg hK (by linarith), ← exp_conj]
    congr 1; simp [conj_ofReal]
  have hc : cuspoidContour K (-r) = -conj (cuspoidContour K r) := by
    simp only [cuspoidContour, map_mul, conj_ofReal, hd]; push_cast; ring
  rw [map_mul, ← exp_conj, map_mul, conj_I, conj_cuspoidPotential, hd, hc,
    cuspoidPotential_neg_of_odd hK, mul_neg, neg_mul]

/-- `Ψ₁(x) = (2π/3^{1/3}) Ai(x/3^{1/3})` (DLMF 36.2.13): the fold canonical integral is an Airy
function. -/
@[dlmf 36.2.E13]
theorem cuspoidIntegral_one (x : ℝ) :
    cuspoidIntegral 1 ![x] = 2 * π / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      DLMF.Airy.airyAi ((x / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
  set a : ℝ := (3 : ℝ) ^ (1 / 3 : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have ha3 : (a : ℂ) ^ 3 = 3 := by
    have : a ^ 3 = 3 := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    exact_mod_cast this
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  set u : ℂ := exp (((π / 6 : ℝ) : ℂ) * I) with hu
  have hθ : (cuspoidAngle 1 : ℂ) = ((π / 6 : ℝ) : ℂ) := by
    unfold cuspoidAngle; push_cast; ring
  have hint := integrable_cuspoidIntegral_integrand 1 ![x]
  set f := fun r : ℝ =>
    cuspoidContourDir 1 r * exp (I * cuspoidPotential 1 (cuspoidContour 1 r) ![x]) with hf
  have hR : ∫ r in Ioi (0 : ℝ), f r = (a⁻¹ : ℝ) * (I * DLMF.Airy.airyInt_w (x / a)) := by
    have h1 : ∀ r ∈ Ioi (0 : ℝ),
        f r = (fun ρ : ℝ => u * DLMF.Airy.airyInt_osc (x / a) (ρ * u)) (a * r) := by
      intro r hr
      simp only [hf, cuspoidContour, cuspoidContourDir_of_nonneg 1 (le_of_lt hr), hθ,
          cuspoidPotential,
        DLMF.Airy.airyInt_osc, Fin.sum_univ_one]
      congr 2
      simp only [Matrix.cons_val_fin_one, Fin.val_zero, zero_add, pow_one]
      rw [ofReal_div x a, ofReal_mul, ← hu]
      field_simp
      linear_combination (-(r : ℂ) ^ 3 * u ^ 3) * ha3
    rw [setIntegral_congr_fun measurableSet_Ioi h1]
    rw [integral_comp_mul_left_Ioi (fun ρ : ℝ => u * DLMF.Airy.airyInt_osc (x / a) (ρ * u)) 0 ha,
      mul_zero, integral_airyInt_osc_ray_pi_div_six, Complex.real_smul]
  have hL : ∫ r in Iic (0 : ℝ), f r = conj (∫ r in Ioi (0 : ℝ), f r) := by
    have := integral_comp_neg_Ioi 0 f
    rw [neg_zero] at this
    rw [← this, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    have := cuspoidContourIntegrand_neg_of_odd (K := 1) (by decide) ![x] hr
    rw [alternating_sign_vecCons_one] at this
    exact this
  unfold cuspoidIntegral
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := 0),
    ← hf, hL, hR]
  have hpi := DLMF.Airy.airyInt_pi_airyAi (x / a)
  have hAi : DLMF.Airy.airyAi ((x / a : ℝ) : ℂ) =
      (((-(DLMF.Airy.airyInt_w (x / a)).im : ℝ) : ℂ)) / π := by
    rw [← hpi]; field_simp
  rw [hAi]
  apply Complex.ext <;> simp [map_mul, conj_ofReal]
  field_simp
  ring

/-- `Ψ^{(H)}(x, y, 0) = (4π²/3^{2/3}) Ai(x/3^{1/3}) Ai(y/3^{1/3})` (DLMF 36.2.21). -/
@[dlmf 36.2.E21]
theorem hyperbolicUmbilicIntegral_z_zero (x y : ℝ) :
    hyperbolicUmbilicIntegral x y 0 = 4 * π ^ 2 / (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      DLMF.Airy.airyAi ((x / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      DLMF.Airy.airyAi ((y / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
  rw [hyperbolicUmbilicIntegral_z_zero_eq, cuspoidIntegral_one, cuspoidIntegral_one]
  have h : ((3 : ℝ) ^ (2 / 3 : ℝ)) = ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h0 : ((3 : ℝ) ^ (1 / 3 : ℝ)) ≠ 0 := by positivity
  rw [h]; push_cast; field_simp; ring

end DLMF.CoalescingSaddles
end
