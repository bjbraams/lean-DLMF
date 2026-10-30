/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.ErrorFunctions

public import DLMF.Confluent.Asymptotics
public import DLMF.Confluent.Relations

/-!
# Fresnel integrals and Dawson's integral (Temme §§7.3.4, 7.3.6; DLMF Chapter 7)

The error function `erf` and its complement are defined in `DLMF.Confluent.Basic`, and the
asymptotic expansion of `erfc` is in `DLMF.Confluent.IncompleteGamma`. This file adds the
Fresnel integrals `C`, `S` and Dawson's integral `F` on the real line.

## Main results

* `Real.fresnelCosInt_add_I_mul_fresnelSinInt`: `C(x) + i S(x) = (1+i)/2 · erf(√π (1-i) x / 2)`
  (DLMF 7.5.8).
* `Real.tendsto_fresnelCosInt_atTop`, `Real.tendsto_fresnelSinInt_atTop`: `C(∞) = S(∞) = 1/2`
  (DLMF 7.2.9), from the generalized Fresnel integrals of `DLMF.Gamma`.
* `Real.dawsonF_eq_kummerM`: `F(x) = x M(1, 3/2, -x²)`.
* `Real.hasAsymptoticExpansion_dawsonF`: `F(x) ~ ∑ (1/2)_k / (2 x^{2k+1})`, from the expansion of
  the regularized Kummer function.

The auxiliary functions `f`, `g` of DLMF 7.2.10–7.2.11 and their asymptotic expansions, which
need the complementary error function off the real axis, are not yet formalized.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- `C'(x) = cos(πx²/2)` for the Fresnel integral `C`. -/
theorem Real.hasDerivAt_fresnelCosInt (x : ℝ) : HasDerivAt Real.fresnelCosInt
    (Real.cos (π * x ^ 2 / 2)) x :=
  intervalIntegral.integral_hasDerivAt_right ((by fun_prop : Continuous fun t : ℝ =>
    Real.cos (π * t ^ 2 / 2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Real.cos (π * t ^ 2 / 2)
      ).stronglyMeasurableAtFilter _ _) (by fun_prop)

/-- `S'(x) = sin(πx²/2)` for the Fresnel integral `S`. -/
theorem Real.hasDerivAt_fresnelSinInt (x : ℝ) : HasDerivAt Real.fresnelSinInt
    (Real.sin (π * x ^ 2 / 2)) x :=
  intervalIntegral.integral_hasDerivAt_right ((by fun_prop : Continuous fun t : ℝ =>
    Real.sin (π * t ^ 2 / 2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Real.sin (π * t ^ 2 / 2)
      ).stronglyMeasurableAtFilter _ _) (by fun_prop)

/-- **Fresnel integrals through the error function** (DLMF 7.5.7, 7.5.8):
`C(x) + i S(x) = (1+i)/2 · erf(√π (1-i) x / 2)`. -/
@[dlmf 7.5.E8]
theorem Real.fresnelCosInt_add_I_mul_fresnelSinInt (x : ℝ) :
    (Real.fresnelCosInt x : ℂ) + I * Real.fresnelSinInt x =
      (1 + I) / 2 * erf ((Real.sqrt π : ℂ) * (1 - I) / 2 * x) := by
  set c : ℂ := (Real.sqrt π : ℂ) * (1 - I) / 2 with hc
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hπsq : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 + I) / 2 * erf (c * t))
      (exp (I * (π * t ^ 2 / 2))) t := by
    intro t
    have hP := ((hasDerivAt_gaussianPrimitive (c * t)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).const_mul c)).const_mul ((1 + I) / 2 * (2 / (Real.sqrt π : ℂ)))
    have hE : HasDerivAt (fun w : ℂ => (1 + I) / 2 * erf (c * w))
        (exp (I * (π * t ^ 2 / 2))) (t : ℂ) := by
      refine (hP.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
      · simp only [mul_one]
        rw [show -(c * (t : ℂ)) ^ 2 = I * (π * t ^ 2 / 2) by
          rw [hc, mul_pow, div_pow, mul_pow, hπsq, sub_sq, Complex.I_sq]; ring]
        rw [hc]
        field_simp
        linear_combination (-1 : ℂ) * Complex.I_sq
      · simp only [erf, Function.comp]
        ring
    exact hE.comp_ofReal
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => exp (I * (π * t ^ 2 / 2))).intervalIntegrable 0 x)
  rw [Complex.ofReal_zero, mul_zero, erf_zero, mul_zero, sub_zero] at hint
  rw [← hint, Real.fresnelCosInt, Real.fresnelSinInt, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((by fun_prop : Continuous fun t : ℝ =>
      ((Real.cos (π * t ^ 2 / 2) : ℝ) : ℂ)).intervalIntegrable 0 x)
      ((by fun_prop : Continuous fun t : ℝ =>
      I * ((Real.sin (π * t ^ 2 / 2) : ℝ) : ℂ)).intervalIntegrable 0 x)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [show I * ((π : ℂ) * (t : ℂ) ^ 2 / 2) = ((π * t ^ 2 / 2 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- The scaling `∫₀ˣ g(π t²/2) dt = √(2/π) ∫₀^{x√(π/2)} g(u²) du`. -/
theorem integral_comp_pi_mul_sq_div_two (g : ℝ → ℝ) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, g (π * t ^ 2 / 2) =
      (Real.sqrt (π / 2))⁻¹ * ∫ u in (0 : ℝ)..(Real.sqrt (π / 2) * x), g (u ^ 2) := by
  have hc : Real.sqrt (π / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have h := intervalIntegral.integral_comp_mul_left (fun u => g (u ^ 2)) hc (a := 0) (b := x)
  rw [mul_zero] at h
  rw [← smul_eq_mul, ← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring_nf

/-- `C(x) → 1/2` as `x → +∞` (DLMF 7.2.9). -/
@[dlmf 7.2.E9]
theorem Real.tendsto_fresnelCosInt_atTop : Tendsto Real.fresnelCosInt atTop (𝓝 (1 / 2)) := by
  have hc : 0 < Real.sqrt (π / 2) := Real.sqrt_pos.mpr (by positivity)
  have h := ((DLMF.Gamma.Gamma_cos_pow 2 le_rfl).comp
    (tendsto_id.const_mul_atTop hc)).const_mul (Real.sqrt (π / 2))⁻¹
  convert h using 1
  · funext x
    simp only [Function.comp_apply, id, Real.fresnelCosInt]
    rw [integral_comp_pi_mul_sq_div_two Real.cos x]
  · rw [show (1 : ℝ) + 1 / (2 : ℕ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq, show π / (2 * ((2 : ℕ) : ℝ)) = π / 4 by norm_num,
      Real.cos_pi_div_four, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    congr 1
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- `S(x) → 1/2` as `x → +∞` (DLMF 7.2.9). -/
@[dlmf 7.2.E9]
theorem Real.tendsto_fresnelSinInt_atTop : Tendsto Real.fresnelSinInt atTop (𝓝 (1 / 2)) := by
  have hc : 0 < Real.sqrt (π / 2) := Real.sqrt_pos.mpr (by positivity)
  have h := ((DLMF.Gamma.Gamma_sin_pow 2 le_rfl).comp
    (tendsto_id.const_mul_atTop hc)).const_mul (Real.sqrt (π / 2))⁻¹
  convert h using 1
  · funext x
    simp only [Function.comp_apply, id, Real.fresnelSinInt]
    rw [integral_comp_pi_mul_sq_div_two Real.sin x]
  · rw [show (1 : ℝ) + 1 / (2 : ℕ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq, show π / (2 * ((2 : ℕ) : ℝ)) = π / 4 by norm_num,
      Real.sin_pi_div_four, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    congr 1
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- `∫₀ˣ e^{t²} dt = x M(1/2, 3/2, x²)`. -/
theorem integral_exp_sq_eq_kummerM (x : ℝ) :
    ((∫ t in (0 : ℝ)..x, Real.exp (t ^ 2) : ℝ) : ℂ) =
      x * kummerM (1 / 2) (3 / 2) ((x : ℂ) ^ 2) := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (t : ℂ) * kummerM (1 / 2) (3 / 2) ((t : ℂ) ^ 2))
      (exp ((t : ℂ) ^ 2)) t := by
    intro t
    have hP := ((hasDerivAt_gaussianPrimitive (I * t)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).const_mul I)).const_mul (-I)
    have hE : HasDerivAt (fun w : ℂ => w * kummerM (1 / 2) (3 / 2) (w ^ 2))
        (exp ((t : ℂ) ^ 2)) (t : ℂ) := by
      refine (hP.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
      · simp only [mul_one, mul_pow, Complex.I_sq]
        rw [show -(-1 * (t : ℂ) ^ 2) = (t : ℂ) ^ 2 by ring]
        linear_combination (-exp ((t : ℂ) ^ 2)) * Complex.I_mul_I
      · simp only [Function.comp, mul_pow, Complex.I_sq]
        rw [show -(-1 * w ^ 2) = w ^ 2 by ring]
        linear_combination (w * kummerM (1 / 2) (3 / 2) (w ^ 2)) * Complex.I_mul_I
    exact hE.comp_ofReal
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => exp ((t : ℂ) ^ 2)).intervalIntegrable 0 x)
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hint
  rw [← hint, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t _ => ?_
  push_cast
  rfl

/-- Dawson's integral as a Kummer function: `F(x) = x M(1, 3/2, -x²)`. -/
theorem Real.dawsonF_eq_kummerM (x : ℝ) :
    (Real.dawsonF x : ℂ) = x * kummerM 1 (3 / 2) (-(x : ℂ) ^ 2) := by
  rw [Real.dawsonF, Complex.ofReal_mul, integral_exp_sq_eq_kummerM,
    kummerM_kummer_transform three_half_ne_neg_nat]
  push_cast
  rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num, show -(x : ℂ) ^ 2 = -((x : ℂ) ^ 2) by ring]
  have he : exp (-(x : ℂ) ^ 2) * exp ((x : ℂ) ^ 2) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination (x * kummerM 1 (3 / 2) (-((x : ℂ) ^ 2))) * he

/-- **Asymptotic expansion of Dawson's integral** (Temme §7.3.4 with §7.1):
`F(x) ~ ∑ (1/2)_k / (2 x^{2k+1})` as `x → +∞`. -/
theorem Real.hasAsymptoticExpansion_dawsonF :
    HasAsymptoticExpansion atTop (fun (k : ℕ) (x : ℝ) => (x : ℂ) ^ (-1 - 2 * (k : ℂ)))
      (fun k => poch (1 / 2) k / 2) (fun x : ℝ => (Real.dawsonF x : ℂ)) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h := (((hasAsymptoticExpansion_regularizedConfluent (1 / 2) (3 / 2)).comp_tendsto
    hsq).mul_left (fun x : ℝ => (x : ℂ) * exp (-(x : ℂ) ^ 2))).const_smul
      (Gamma (3 / 2 : ℂ))
  refine ((h.congr' ?_).congr_scale fun k => ?_).congr_coeff ?_
  · filter_upwards with x
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [Real.dawsonF, Complex.ofReal_mul, integral_exp_sq_eq_kummerM,
      kummerM_eq_mul_regularizedHGFun three_half_ne_neg_nat]
    push_cast
    ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    push_cast
    rw [sq_cpow_of_re_pos (by simpa using hx)]
    have he : exp (-(x : ℂ) ^ 2) * exp ((x : ℂ) ^ 2) = 1 := by rw [← Complex.exp_add]; simp
    rw [show (x : ℂ) * exp (-(x : ℂ) ^ 2) * (exp ((x : ℂ) ^ 2) *
      (x : ℂ) ^ (2 * (1 / 2 - 3 / 2 - (k : ℂ)))) = (exp (-(x : ℂ) ^ 2) * exp ((x : ℂ) ^ 2)) *
        ((x : ℂ) * (x : ℂ) ^ (2 * (1 / 2 - 3 / 2 - (k : ℂ)))) by ring, he, one_mul]
    rw [show (x : ℂ) * (x : ℂ) ^ (2 * (1 / 2 - 3 / 2 - (k : ℂ))) =
      (x : ℂ) ^ (1 + 2 * (1 / 2 - 3 / 2 - (k : ℂ))) by
        rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]]
    ring_nf
  · funext k
    simp only [Pi.smul_apply, smul_eq_mul, kummerCoeff]
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num,
      poch_nat_one, Gamma_one_half_eq_sqrt, show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num,
      Complex.Gamma_add_one _ (by norm_num), Gamma_one_half_eq_sqrt]
    have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp

end DLMF.Confluent
