/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic.Properties

/-!
# Rotated solutions, Wronskians and connection formulas for Airy functions (DLMF §9.2)

## Main results

* `isAirySolution_rotated`: `z ↦ Ai(ωz)` solves Airy's equation for a unitCube root of unity `ω`
  (DLMF 9.2.2).
* `airy_general_solution`: every entire solution of Airy's equation is a combination of `Ai`
  and `Bi`.
* `airyAi_zero_mul_airyAiDeriv_zero`: `Ai(0) Ai'(0) = -1/(2π√3)`.
* `wronskian_airyAi_rotated`, `wronskian_airyAi_rotations`: DLMF 9.2.8, 9.2.9.
* `airyAi_neg_connection`, `airyBi_neg_connection`: DLMF 9.2.14, 9.2.15.
* `airy_log_derivative_riccati`: the Riccati equation for `w'/w` (DLMF 9.2.16).

## Implementation notes

The numerically satisfactory pairs of DLMF Table 9.2.1 need asymptotics and are in
`DLMF.Airy.Equation`.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Airy

/-- For a unitCube root of unity `ω`, `z ↦ Ai(ωz)` solves Airy's equation, with derivative
`ω Ai'(ωz)` (DLMF 9.2.2). -/
@[dlmf 9.2.E2]
theorem isAirySolution_rotated {ω : ℂ} (hω : ω ^ 3 = 1) :
    IsAirySolution (fun z => airyAi (ω * z)) (fun z => ω * airyAiDeriv (ω * z)) := by
  intro z
  have h1 := (hasDerivAt_airyAi (ω * z)).comp z ((hasDerivAt_id z).const_mul ω)
  have h2 := ((hasDerivAt_airyAiDeriv (ω * z)).comp z ((hasDerivAt_id z).const_mul ω)).const_mul ω
  change HasDerivAt (fun z => airyAi (ω * z)) _ z at h1
  change HasDerivAt (fun z => ω * airyAiDeriv (ω * z)) _ z at h2
  constructor
  · exact h1.congr_deriv (by ring)
  · exact h2.congr_deriv (by linear_combination z * airyAi (ω * z) * hω)

/-- Every entire Airy solution is a linear combination of Ai and Bi. -/
theorem airy_general_solution {w w' : ℂ → ℂ} (hw : IsAirySolution w w') :
    ∃ a b : ℂ, ∀ z, w z = a * airyAi z + b * airyBi z := by
  let a : ℂ := π * (w 0 * airyBiDeriv 0 - w' 0 * airyBi 0)
  let b : ℂ := π * (airyAi 0 * w' 0 - airyAiDeriv 0 * w 0)
  refine ⟨a, b, ?_⟩
  have hs : IsAirySolution (fun z => a * airyAi z + b * airyBi z)
      (fun z => a * airyAiDeriv z + b * airyBiDeriv z) := fun z => ⟨
    ((hasDerivAt_airyAi z).const_mul a).add ((hasDerivAt_airyBi z).const_mul b),
    (((hasDerivAt_airyAiDeriv z).const_mul a).add
      ((hasDerivAt_airyBiDeriv z).const_mul b)).congr_deriv (by ring)⟩
  have hW := wronskian_airyAi_airyBi 0
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h0 : w 0 = a * airyAi 0 + b * airyBi 0 := by
    dsimp only [a, b]
    field_simp at hW
    linear_combination -(w 0) * hW
  have h1 : w' 0 = a * airyAiDeriv 0 + b * airyBiDeriv 0 := by
    dsimp only [a, b]
    field_simp at hW
    linear_combination -(w' 0) * hW
  exact hw.eq_of_initial hs h0 h1

/-- The initial-value product, normalized using the already proved Airy Wronskian. -/
theorem airyAi_zero_mul_airyAiDeriv_zero :
    airyAi 0 * airyAiDeriv 0 = -1 / (2 * π * Real.sqrt 3) := by
  have hB : airyBi 0 = (Real.sqrt 3 : ℂ) * airyAi 0 := by
    simp only [airyBi, airyAi, airyG_zero, mul_zero, add_zero, sub_zero]
  have hB' : airyBiDeriv 0 = -(Real.sqrt 3 : ℂ) * airyAiDeriv 0 := by
    simp only [airyBiDeriv, airyAiDeriv, airyFDeriv_zero, mul_zero, zero_add, zero_sub]
    ring
  have hW := wronskian_airyAi_airyBi 0
  rw [hB, hB'] at hW
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp at hW ⊢
  linear_combination -hW

/-- `𝒲{Ai(z), Ai(z e^{∓2πi/3})} = e^{±πi/6}/(2π)` (DLMF 9.2.8). -/
@[dlmf 9.2.E8]
theorem wronskian_airyAi_rotated (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAi z * (-ε * (2 * π * I / 3) |>.exp) * airyAiDeriv (z * exp (-ε * (2 * π * I / 3))) -
      airyAiDeriv z * airyAi (z * exp (-ε * (2 * π * I / 3))) =
      exp (ε * (π * I / 6)) / (2 * π) := by
  let ω : ℂ := exp (-ε * (2 * π * I / 3))
  have hω : ω ^ 3 = 1 := by
    rcases hε with rfl | rfl
    · simpa [ω] using omega_recip_cube
    · simpa [ω] using omega_cube
  have hr := isAirySolution_airyAi.wronskian_eq (isAirySolution_rotated hω) z
  simp only [mul_zero] at hr
  have he : ω - 1 = -(Real.sqrt 3 : ℂ) * exp (ε * (π * I / 6)) := by
    rcases hε with rfl | rfl
    · simp only [ω, ofReal_one, one_mul, neg_mul]
      rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_six]
      push_cast
      linear_combination sqrt_three_sq / 2
    · simp only [ω, ofReal_neg, ofReal_one, neg_mul, one_mul, neg_neg]
      rw [exp_two_pi_I_div_three, exp_neg_pi_I_div_six]
      push_cast
      linear_combination sqrt_three_sq / 2
  change airyAi z * ω * airyAiDeriv (z * ω) - airyAiDeriv z * airyAi (z * ω) = _
  calc
    _ = (ω - 1) * (airyAi 0 * airyAiDeriv 0) := by
      rw [mul_comm z ω]
      linear_combination hr
    _ = _ := by
      rw [he, airyAi_zero_mul_airyAiDeriv_zero]
      have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
      field_simp

/-- `𝒲{Ai(z e^{-2πi/3}), Ai(z e^{2πi/3})} = 1/(2πi)` (DLMF 9.2.9). -/
@[dlmf 9.2.E9]
theorem wronskian_airyAi_rotations (z : ℂ) :
    airyAi (z * exp (-2 * π * I / 3)) * exp (2 * π * I / 3) *
        airyAiDeriv (z * exp (2 * π * I / 3)) -
      exp (-2 * π * I / 3) * airyAiDeriv (z * exp (-2 * π * I / 3)) *
        airyAi (z * exp (2 * π * I / 3)) = 1 / (2 * π * I) := by
  have hr := (isAirySolution_rotated omega_recip_cube).wronskian_eq
      (isAirySolution_rotated omega_cube) z
  simp only [mul_zero] at hr
  have he : exp (2 * π * I / 3) - exp (-(2 * π * I / 3)) = (Real.sqrt 3 : ℂ) * I := by
    rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three]
    push_cast
    ring
  calc
    _ = (exp (2 * π * I / 3) - exp (-(2 * π * I / 3))) * (airyAi 0 * airyAiDeriv 0) := by
      simp only [neg_mul, neg_div] at hr ⊢
      rw [mul_comm z (exp (2 * π * I / 3)), mul_comm z (exp (-(2 * π * I / 3)))]
      linear_combination hr
    _ = _ := by
      rw [he, airyAi_zero_mul_airyAiDeriv_zero]
      have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp
      norm_num [I_sq]

/-- `Ai(-z) = e^{πi/3} Ai(z e^{πi/3}) + e^{-πi/3} Ai(z e^{-πi/3})` (DLMF 9.2.14). -/
@[dlmf 9.2.E14]
theorem airyAi_neg_connection (z : ℂ) :
    airyAi (-z) = exp (π * I / 3) * airyAi (z * exp (π * I / 3)) +
      exp (-π * I / 3) * airyAi (z * exp (-π * I / 3)) := by
  have h := airyAi_add_omega (-z)
  have e1 : -exp (-(2 * π * I / 3)) = exp (π * I / 3) := by
    rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_three]
    push_cast; ring
  have e2 : -exp (2 * π * I / 3) = exp (-π * I / 3) := by
    rw [show -π * I / 3 = -(π * I / 3) by ring, exp_two_pi_I_div_three, exp_neg_pi_I_div_three]
    push_cast; ring
  rw [show -z * exp (-(2 * π * I / 3)) = z * exp (π * I / 3) by rw [← e1]; ring,
    show -z * exp (2 * π * I / 3) = z * exp (-π * I / 3) by rw [← e2]; ring] at h
  linear_combination h + airyAi (z * exp (π * I / 3)) * e1 +
    airyAi (z * exp (-π * I / 3)) * e2

/-- `Bi(-z) = e^{-πi/6} Ai(z e^{πi/3}) + e^{πi/6} Ai(z e^{-πi/3})` (DLMF 9.2.15). -/
@[dlmf 9.2.E15]
theorem airyBi_neg_connection (z : ℂ) :
    airyBi (-z) = exp (-π * I / 6) * airyAi (z * exp (π * I / 3)) +
      exp (π * I / 6) * airyAi (z * exp (-π * I / 3)) := by
  have h := airyBi_eq_airyAi_omega (-z)
  have e1 : -exp (-(2 * π * I / 3)) = exp (π * I / 3) := by
    rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_three]
    push_cast; ring
  have e2 : -exp (2 * π * I / 3) = exp (-π * I / 3) := by
    rw [show -π * I / 3 = -(π * I / 3) by ring, exp_two_pi_I_div_three, exp_neg_pi_I_div_three]
    push_cast; ring
  simpa only [neg_mul, neg_div, show -z * exp (-(2 * π * I / 3)) = z * exp (π * I / 3) by
    rw [← e1]; ring, show -z * exp (2 * π * I / 3) = z * exp (-π * I / 3) by
    rw [← e2]; ring] using h

/-- If `w` solves Airy's equation and `w(z) ≠ 0`, the logarithmic derivative `W = w'/w`
satisfies the Riccati equation `W' = z - W²` at `z` (DLMF 9.2.16). -/
@[dlmf 9.2.E16]
theorem airy_log_derivative_riccati {w w' : ℂ → ℂ} (hw : IsAirySolution w w') {z : ℂ}
    (hz : w z ≠ 0) :
    HasDerivAt (fun t => w' t / w t) (z - (w' z / w z) ^ 2) z := by
  have h := (hw z).2.div (hw z).1 hz
  exact h.congr_deriv (by field_simp)

end DLMF.Airy
