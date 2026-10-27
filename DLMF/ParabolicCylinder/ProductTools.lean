/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Initial integral for the parabolic-cylinder product formula

The substitution `x = exp (-4t)` evaluates the hyperbolic kernel at argument zero
as a beta integral. This supplies initial data for DLMF 12.12.4.
-/

@[expose] public noncomputable section
open Complex Set MeasureTheory
open scoped Real
namespace DLMF.Confluent

/-- Exponential substitution for the hyperbolic weight in DLMF 12.12.4. -/
theorem pcfIntegral4_base_beta (a : ℂ) :
    (∫ t : ℝ in Ioi 0, exp (2*a*t) / (Real.sqrt (Real.sinh (2*t)) : ℂ)) =
      betaIntegral (1/4-a/2) (1/2) / (2*Real.sqrt 2) := by
  let f : ℝ → ℝ := fun t => Real.exp (-4*t)
  have hder (t : ℝ) : HasDerivAt f (-4*Real.exp (-4*t)) t := by
    exact (((hasDerivAt_id t).const_mul (-4)).exp).congr_deriv (by simp only [id_eq]; ring)
  have himg : f '' Ioi 0 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith [show 0 < t from ht])⟩
    · intro hx
      refine ⟨-Real.log x/4, ?_, ?_⟩
      · have := Real.log_neg hx.1 hx.2
        change 0 < -Real.log x/4
        linarith
      · dsimp only [f]
        rw [show -4*(-Real.log x/4) = Real.log x by ring, Real.exp_log hx.1]
  have hinj : InjOn f (Ioi 0) := by
    intro x _ y _ h
    have := Real.exp_injective h
    linarith
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hder t).hasDerivWithinAt) hinj
    (fun x : ℝ => (x:ℂ)^(1/4-a/2-1)*(1-(x:ℂ))^((1/2:ℂ)-1))
  rw [himg] at hsub
  have hpt {t : ℝ} (ht : 0 < t) :
      |(-4*Real.exp (-4*t))| •
        ((f t:ℂ)^(1/4-a/2-1)*(1-(f t:ℂ))^((1/2:ℂ)-1)) =
      (2*Real.sqrt 2:ℂ) * (exp (2*a*t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) := by
    have hx : 0 < 1-Real.exp (-4*t) := by
      have := Real.exp_lt_one_iff.mpr (show -4*t < 0 by linarith)
      linarith
    have hs : 0 < Real.sinh (2*t) := Real.sinh_pos_iff.mpr (by linarith)
    have hsq : Real.sqrt (Real.sinh (2*t)) =
        Real.exp t * Real.sqrt (1-Real.exp (-4*t)) / Real.sqrt 2 := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt hs.le, div_pow, mul_pow, Real.sq_sqrt hx.le,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      have hE : Real.exp t ^ 2 = Real.exp (2*t) := by
        rw [pow_two, ← Real.exp_add]; congr 1; ring
      have hE' : Real.exp (2*t) * Real.exp (-4*t) = Real.exp (-(2*t)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hE, Real.sinh_eq]
      linear_combination hE' / 2
    have hp : (f t:ℂ)^(1/4-a/2-1) = exp ((-4*(t:ℂ))*(1/4-a/2-1)) := by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
      rw [← ofReal_log (Real.exp_pos _).le, Real.log_exp]
      push_cast
      rfl
    have hhalf : (1-(f t:ℂ))^((1/2:ℂ)-1) =
        (Real.sqrt (1-Real.exp (-4*t)):ℂ)⁻¹ := by
      rw [show (1/2:ℂ)-1 = -(1/2:ℂ) by ring, cpow_neg,
        show 1-(f t:ℂ) = ((1-Real.exp (-4*t):ℝ):ℂ) by simp [f],
        show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
        ← ofReal_cpow hx.le, ← Real.sqrt_eq_rpow]
    rw [hp, hhalf, abs_of_neg (by have := Real.exp_pos (-4*t); linarith), real_smul,
      hsq]
    push_cast
    have he : exp (-4*t) * exp ((-4*t)*(1/4-a/2-1)) * exp t = exp (2*a*t) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring
    have htwo : (Real.sqrt 2:ℂ)^2 = 2 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    have hsn : (Real.sqrt (1-Real.exp (-4*t)):ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
    have ht2 : (Real.sqrt 2:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    have het : exp (t:ℂ) ≠ 0 := exp_ne_zero _
    generalize exp (-4*(t:ℂ)) = E0 at he ⊢
    generalize exp ((-4*(t:ℂ))*(1/4-a/2-1)) = E1 at he ⊢
    generalize exp (t:ℂ) = Et at he het ⊢
    generalize exp (2*a*t) = E2 at he ⊢
    generalize (Real.sqrt (1-Real.exp (-4*t)):ℂ) = S at hsn ⊢
    generalize (Real.sqrt 2:ℂ) = T at htwo ht2 ⊢
    field_simp
    linear_combination 4 * he - 2 * E2 * htwo
  have hval : betaIntegral (1/4-a/2) (1/2) =
      (2*Real.sqrt 2:ℂ) * (∫ t : ℝ in Ioi 0,
        exp (2*a*t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      hsub, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt ht
  rw [hval]
  field_simp
end DLMF.Confluent
