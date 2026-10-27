/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Generating
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Bessel's integral (DLMF 10.9.1–10.9.2)

On the unit circle `t = e^{iθ}` the generating function becomes the Fourier series
`e^{iz sin θ} = ∑ₘ Jₘ(z) e^{imθ}` (Jacobi–Anger), whose coefficients are summable in absolute
value. Integrating term by term against `e^{-inθ}` over a period gives
`Jₙ(z) = (2π)⁻¹ ∫₀^{2π} e^{i(z sin θ - nθ)} dθ`, and folding the period at `θ = π` gives
Bessel's integral `Jₙ(z) = π⁻¹ ∫₀^π cos(z sin θ - nθ) dθ`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Bessel

/-- The Jacobi–Anger expansion `e^{iz sin θ} = ∑ₘ Jₘ(z) e^{imθ}` (DLMF 10.12.1). -/
@[dlmf 10.12.E1]
theorem hasSum_besselJ_jacobiAnger (z : ℂ) (θ : ℝ) :
    HasSum (fun m : ℤ => besselJ m z * exp (I * m * θ)) (exp (I * z * sin θ)) := by
  have h := hasSum_besselJ_generating_function z (exp (I * θ)) (exp_ne_zero _)
  have hsin : z / 2 * (exp (I * θ) - (exp (I * θ))⁻¹) = I * z * sin θ := by
    rw [← exp_neg, sin, show -(I * (θ : ℂ)) = -(θ : ℂ) * I by ring,
      show I * (θ : ℂ) = (θ : ℂ) * I by ring]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hsin] at h
  convert h using 2 with m
  rw [← exp_int_mul]
  ring_nf

/-- The integer-order coefficients are absolutely summable. -/
theorem summable_norm_besselJ_int (z : ℂ) : Summable fun m : ℤ => ‖besselJ m z‖ := by
  have h := (hasSum_besselJ_generating_function z 1 one_ne_zero).summable
  simp only [one_zpow, mul_one] at h
  exact summable_norm_iff.mpr h

/-- `∫₀^{2π} e^{ikθ} dθ = 2π δ_{k0}` for integer `k`. -/
theorem integral_exp_int_mul_I (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * k * θ) = if k = 0 then 2 * π else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : I * (k : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hk)
    rw [integral_exp_mul_complex hc]
    have h1 : exp (I * k * (2 * π)) = 1 := by
      rw [← exp_int_mul_two_pi_mul_I k]
      ring_nf
    simp [h1]

/-- The complex form of Bessel's integral: `Jₙ(z) = (2π)⁻¹ ∫₀^{2π} e^{i(z sin θ - nθ)} dθ`. -/
theorem besselJ_int_eq_integral_exp (n : ℤ) (z : ℂ) :
    besselJ n z = (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π, exp (I * (z * sin θ - n * θ)) := by
  have hlim (θ : ℝ) : HasSum (fun m : ℤ => besselJ m z * exp (I * (m - n : ℤ) * θ))
      (exp (I * (z * sin θ - n * θ))) := by
    have h := (hasSum_besselJ_jacobiAnger z θ).mul_right (exp (-(I * n * θ)))
    convert h using 1
    · funext m
      rw [mul_assoc _ (exp _), ← exp_add]
      push_cast
      congr 2
      ring_nf
    · rw [← exp_add]
      ring_nf
  have hcont (m : ℤ) : Continuous fun θ : ℝ => besselJ m z * exp (I * (m - n : ℤ) * θ) := by
    fun_prop
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (F := fun (m : ℤ) (θ : ℝ) => besselJ m z * exp (I * (m - n : ℤ) * θ))
    (f := fun θ : ℝ => exp (I * (z * sin θ - n * θ)))
    (fun m _ => ‖besselJ m z‖)
    (fun m => (hcont m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, show I * ((m - n : ℤ) : ℂ) * (θ : ℂ) = ((((m - n : ℤ) : ℝ) * θ : ℝ) : ℂ) * I
        by push_cast; ring, norm_exp_ofReal_mul_I, mul_one])
    (Filter.Eventually.of_forall fun _ _ => summable_norm_besselJ_int z)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => hlim θ)
  have hterm (m : ℤ) : ∫ θ in (0 : ℝ)..2 * π, besselJ m z * exp (I * (m - n : ℤ) * θ) =
      if m = n then 2 * π * besselJ n z else 0 := by
    rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
    by_cases hm : m = n
    · simp [hm, mul_comm]
    · simp [hm, sub_ne_zero.mpr hm]
  simp only [hterm] at hint
  have hsingle : HasSum (fun m : ℤ => if m = n then 2 * π * besselJ n z else 0)
      (2 * π * besselJ n z) := hasSum_ite_eq n _
  rw [hint.unique hsingle]
  field_simp

/-- Bessel's integral `Jₙ(z) = π⁻¹ ∫₀^π cos(z sin θ - nθ) dθ` (DLMF 10.9.2). -/
@[dlmf 10.9.E2]
theorem besselJ_int_eq_integral_cos (n : ℤ) (z : ℂ) :
    besselJ n z = (1 / π) * ∫ θ in (0 : ℝ)..π, cos (z * sin θ - n * θ) := by
  set g : ℝ → ℂ := fun θ => exp (I * (z * sin θ - n * θ)) with hg
  have hgc : Continuous g := by fun_prop
  have hrefl : ∫ θ in π..2 * π, g θ = ∫ θ in (0 : ℝ)..π, exp (-(I * (z * sin θ - n * θ))) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) g (2 * π)
    rw [show 2 * π - π = π by ring, sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hg]
    have hp : exp (-(I * (n * (2 * π)))) = 1 := by
      rw [← exp_int_mul_two_pi_mul_I (-n)]
      push_cast
      ring_nf
    push_cast
    rw [show (2 * (π : ℂ) - θ) = -(θ : ℂ) + 2 * π by ring, sin_add_two_pi, sin_neg]
    rw [← mul_one (exp (-(I * (z * sin θ - n * θ)))), ← hp, ← exp_add]
    congr 1
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgc.intervalIntegrable (μ := MeasureTheory.volume) 0 π)
    (hgc.intervalIntegrable (μ := MeasureTheory.volume) π (2 * π))
  have hc' : Continuous fun θ : ℝ => exp (-(I * (z * sin θ - n * θ))) := by fun_prop
  rw [besselJ_int_eq_integral_exp, ← hsplit, hrefl, ← intervalIntegral.integral_add
    (hgc.intervalIntegrable (μ := MeasureTheory.volume) 0 π)
    (hc'.intervalIntegrable (μ := MeasureTheory.volume) 0 π)]
  have hcos : (fun θ : ℝ => g θ + exp (-(I * (z * sin θ - n * θ)))) =
      fun θ : ℝ => 2 * cos (z * sin θ - n * θ) := by
    funext θ
    simp only [hg, cos]
    ring_nf
  rw [hcos, intervalIntegral.integral_const_mul]
  field_simp

/-- The case `n = 0` of Bessel's integral (DLMF 10.9.1). -/
@[dlmf 10.9.E1]
theorem besselJ_zero_eq_integral_cos (z : ℂ) :
    besselJ 0 z = (1 / π) * ∫ θ in (0 : ℝ)..π, cos (z * sin θ) := by
  simpa using besselJ_int_eq_integral_cos 0 z

end DLMF.Bessel
