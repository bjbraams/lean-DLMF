/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.ComplexValues

/-!
# Airy functions expressed through Bessel functions

Bessel and Hankel representations of the Airy functions, with the real and complex branch
conventions retained.

Source references and common attribution are retained in
`DLMF.Airy.Relations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology

namespace DLMF.Airy

/-- The inverse substitution on the logarithmic ζ plane. -/
@[dlmf 9.6.E10]
def airyInverseZetaOnLog (w : ℂ) : ℂ := exp (2 / 3 * (log (3 / 2 : ℂ) + w))

/-- The inverse substitution recovers `z` from `log ζ`, `ζ = (2/3) z^{3/2}`, for `z ≠ 0`
(DLMF 9.6.10). -/
@[dlmf 9.6.E10]
theorem airyInverseZeta_logZeta {z : ℂ} (hz : z ≠ 0) :
    airyInverseZetaOnLog (airyLogZeta z) = z := by
  have h : log (3 / 2 : ℂ) + log (2 / 3 : ℂ) = 0 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
      show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_log (by norm_num), ← ofReal_log (by norm_num), ← ofReal_add,
      ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [airyInverseZetaOnLog, airyLogZeta,
    show 2 / 3 * (log (3 / 2 : ℂ) + (log (2 / 3) + 3 / 2 * log z)) =
      2 / 3 * (log (3 / 2 : ℂ) + log (2 / 3)) + log z by ring, h, mul_zero, zero_add, exp_log hz]

/-- `log (2/3) = log 2 - log 3`. -/
theorem log_two_thirds : log (2 / 3 : ℂ) = log 2 - log 3 := by
  rw [show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by norm_num),
    Real.log_div (by norm_num) (by norm_num)]
  push_cast
  rw [ofReal_log (by norm_num), ofReal_log (by norm_num)]
  push_cast; ring

/-- `exp (2ζ)/4 = z³/9` for the logarithmic Airy variable `ζ`. -/
theorem exp_two_mul_airyLogZeta {z : ℂ} (hz : z ≠ 0) : exp (2 * airyLogZeta z) / 4 = z ^ 3 / 9 := by
  rw [airyLogZeta, show 2 * (log (2 / 3 : ℂ) + 3 / 2 * log z) =
    ((2 : ℕ) : ℂ) * log (2 / 3 : ℂ) + ((3 : ℕ) : ℂ) * log z by push_cast; ring, exp_add,
    exp_nat_mul, exp_nat_mul, exp_log (by norm_num), exp_log hz]
  ring

/-- The `I`-Bessel function on the logarithmic plane at the Airy argument `ζ = (2/3) z^{3/2}`. -/
theorem airyBesselIOnLog_airyLogZeta (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    airyBesselIOnLog ν (airyLogZeta z) =
      exp (-ν * log 3) * exp (3 / 2 * ν * log z) *
        regularizedHGFun ∅ {ν + 1} (z ^ 3 / 9) := by
  rw [airyBesselIOnLog, exp_two_mul_airyLogZeta hz, ← exp_add]
  congr 2
  rw [airyLogZeta, log_two_thirds]
  ring

/-- The `J`-Bessel function on the logarithmic plane at the Airy argument. -/
theorem airyBesselJOnLog_airyLogZeta (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    airyBesselJOnLog ν (airyLogZeta z) =
      exp (-ν * log 3) * exp (3 / 2 * ν * log z) *
        regularizedHGFun ∅ {ν + 1} (-(z ^ 3 / 9)) := by
  rw [airyBesselJOnLog, neg_div, exp_two_mul_airyLogZeta hz, ← exp_add]
  congr 2
  rw [airyLogZeta, log_two_thirds]
  ring

/-- Real powers of `3` as complex exponentials. -/
theorem three_rpow_eq_exp (a : ℝ) : (((3 : ℝ) ^ a : ℝ) : ℂ) = exp (a * log 3) := by
  rw [ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3), cpow_def_of_ne_zero (by norm_num)]
  push_cast; ring_nf

/-- `Ai(z) = (z^{1/2}/3) (I_{-1/3}(ζ) - I_{1/3}(ζ))` with `ζ = (2/3) z^{3/2}`, the Bessel
functions continued on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z =
      z ^ (1 / 2 : ℂ) / 3 *
        (airyBesselIOnLog (-(1 / 3)) (airyLogZeta z) -
            airyBesselIOnLog (1 / 3) (airyLogZeta z)) := by
  rw [airyBesselIOnLog_airyLogZeta _ hz, airyBesselIOnLog_airyLogZeta _ hz,
    cpow_def_of_ne_zero hz]
  simp only [airyAi, airyF, airyG, three_rpow_eq_exp]
  have e1 : exp (log z * (1 / 2)) * exp (3 / 2 * -(1 / 3) * log z) = 1 := by
    rw [← exp_add, show log z * (1 / 2) + 3 / 2 * -(1 / 3) * log z = 0 by ring, exp_zero]
  have e2 : exp (log z * (1 / 2)) * exp (3 / 2 * (1 / 3) * log z) = z := by
    rw [← exp_add, show log z * (1 / 2) + 3 / 2 * (1 / 3) * log z = log z by ring, exp_log hz]
  have e3 : exp (-(-(1 / 3)) * log 3) / 3 = exp (((-(2 / 3) : ℝ) : ℂ) * log 3) := by
    rw [div_eq_iff (by norm_num), ← exp_log (show (3 : ℂ) ≠ 0 by norm_num), ← exp_add,
      exp_log (show (3 : ℂ) ≠ 0 by norm_num)]
    congr 1; push_cast; ring
  have e4 : exp (-(1 / 3) * log 3) / 3 = exp (((-(4 / 3) : ℝ) : ℂ) * log 3) := by
    rw [div_eq_iff (by norm_num), ← exp_log (show (3 : ℂ) ≠ 0 by norm_num), ← exp_add,
      exp_log (show (3 : ℂ) ≠ 0 by norm_num)]
    congr 1; push_cast; ring
  rw [show (-(1 / 3 : ℂ)) + 1 = 2 / 3 by norm_num, show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num]
  set F := regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (z ^ 3 / 9)
  set G := regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (z ^ 3 / 9)
  linear_combination (-F) * e3 - F * (exp (-(-(1 / 3)) * log 3) / 3) * e1 +
    G * (exp (-(1 / 3) * log 3) / 3) * e2 + G * z * e4

/-- `√3 = exp (log 3 / 2)` in `ℂ`. -/
theorem sqrt_three_eq_exp : ((Real.sqrt 3 : ℝ) : ℂ) = exp (1 / 2 * log 3) := by
  rw [Real.sqrt_eq_rpow, three_rpow_eq_exp]; push_cast; ring_nf

/-- `3⁻¹ = exp (-log 3)` in `ℂ`. -/
theorem recip_three_eq_exp : (3 : ℂ)⁻¹ = exp (-log 3) := by
  rw [exp_neg, exp_log (by norm_num)]

/-- `log (z/3) = log z - log 3` for `z ≠ 0`. -/
theorem log_div_three {z : ℂ} (hz : z ≠ 0) : log (z / 3) = log z - log 3 := by
  rw [show z / 3 = z * ((1 / 3 : ℝ) : ℂ) by push_cast; ring, log_mul_ofReal _ (by norm_num) _ hz,
    one_div, Real.log_inv, ofReal_neg, ofReal_log (by norm_num)]
  push_cast; ring

/-- `(z/3)^{1/2}` as a complex exponential. -/
theorem half_cpow_div_three {z : ℂ} (hz : z ≠ 0) :
    (z / 3) ^ (1 / 2 : ℂ) = exp ((log z - log 3) * (1 / 2)) := by
  rw [cpow_def_of_ne_zero (div_ne_zero hz (by norm_num)), log_div_three hz]

/-- `Bi(z) = (z/3)^{1/2} (I_{1/3}(ζ) + I_{-1/3}(ζ))` with `ζ = (2/3) z^{3/2}` on the logarithmic
plane, for `z ≠ 0` (DLMF 9.6.4). -/
@[dlmf 9.6.E4]
theorem airyBi_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi z =
      ((z / 3) ^ (1 / 2 : ℂ)) *
        (airyBesselIOnLog (1 / 3) (airyLogZeta z) +
            airyBesselIOnLog (-(1 / 3)) (airyLogZeta z)) := by
  rw [airyBesselIOnLog_airyLogZeta _ hz, airyBesselIOnLog_airyLogZeta _ hz, half_cpow_div_three hz]
  simp only [airyBi, airyF, airyG]
  have f1 : exp ((log z - log 3) * (1 / 2)) * exp (-(-(1 / 3)) * log 3) *
      exp (3 / 2 * -(1 / 3) * log z) =
        ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) := by
    rw [three_rpow_eq_exp, sqrt_three_eq_exp]
    simp only [← exp_add]; congr 1; push_cast; ring
  have f2 : exp ((log z - log 3) * (1 / 2)) * exp (-(1 / 3) * log 3) *
      exp (3 / 2 * (1 / 3) * log z) =
        ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * exp (log z) := by
    rw [three_rpow_eq_exp, sqrt_three_eq_exp]
    simp only [← exp_add]; congr 1; push_cast; ring
  rw [exp_log hz] at f2
  rw [show (-(1 / 3 : ℂ)) + 1 = 2 / 3 by norm_num, show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num]
  set F := regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (z ^ 3 / 9)
  set G := regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (z ^ 3 / 9)
  linear_combination (-F) * f1 - G * f2

/-- Contiguous relation for the regularized `0F1` at parameter `1/3`. -/
lemma reg0F1_one_third (w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {1 / 3} w =
      1 / 3 * regularizedHGFun ∅ {4 / 3} w + w * regularizedHGFun ∅ {7 / 3} w :=
  reg0F1_contiguous' (by norm_num) (by norm_num) w

/-- Exponent relations for the derivative forms: `z · 3^{-2/3} z = 3^{-2/3} z²`
and `z · 3^{2/3} z^{-1} = 9 · 3^{-4/3}`. -/
theorem airy_deriv_exp_relations {z : ℂ} (hz : z ≠ 0) :
    z * exp (-(2 / 3) * log 3) * exp (3 / 2 * (2 / 3) * log z) =
        (((3 : ℝ) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * (z * z) ∧
      z * exp (-(-(2 / 3)) * log 3) * exp (3 / 2 * -(2 / 3) * log z) =
        (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * (3 * 3) := by
  have a1 : exp (log z) * exp (-(2 / 3) * log 3) * exp (3 / 2 * (2 / 3) * log z) =
      (((3 : ℝ) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * (exp (log z) * exp (log z)) := by
    rw [three_rpow_eq_exp]
    simp only [← exp_add]; congr 1; push_cast; ring
  have a2 : exp (log z) * exp (-(-(2 / 3)) * log 3) * exp (3 / 2 * -(2 / 3) * log z) =
      (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * (exp (log 3) * exp (log 3)) := by
    rw [three_rpow_eq_exp]
    simp only [← exp_add]; congr 1; push_cast; ring
  rw [exp_log hz] at a1 a2
  rw [exp_log (by norm_num : (3 : ℂ) ≠ 0)] at a2
  exact ⟨a1, a2⟩

/-- `Ai'(z) = (z/3) (I_{2/3}(ζ) - I_{-2/3}(ζ))` with `ζ = (2/3) z^{3/2}` on the logarithmic
plane, for `z ≠ 0` (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z =
      z / 3 *
        (airyBesselIOnLog (2 / 3) (airyLogZeta z) -
            airyBesselIOnLog (-(2 / 3)) (airyLogZeta z)) := by
  rw [airyBesselIOnLog_airyLogZeta _ hz, airyBesselIOnLog_airyLogZeta _ hz]
  simp only [airyAiDeriv, airyFDeriv, airyGDeriv]
  obtain ⟨g1, g2⟩ := airy_deriv_exp_relations hz
  have hC := reg0F1_one_third (z ^ 3 / 9)
  rw [show (-(2 / 3 : ℂ)) + 1 = 1 / 3 by norm_num, show (2 / 3 : ℂ) + 1 = 5 / 3 by norm_num]
  set F53 := regularizedHGFun (∅ : Multiset ℂ) {5 / 3} (z ^ 3 / 9)
  set F13 := regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (z ^ 3 / 9)
  linear_combination (-F53 / 3) * g1 + (F13 / 3) * g2 +
    3 * (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * hC

/-- `Bi'(z) = (z/√3) (I_{2/3}(ζ) + I_{-2/3}(ζ))` with `ζ = (2/3) z^{3/2}` on the logarithmic
plane, for `z ≠ 0` (DLMF 9.6.5). -/
@[dlmf 9.6.E5]
theorem airyBiDeriv_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z =
      (z / Real.sqrt 3) *
        (airyBesselIOnLog (2 / 3) (airyLogZeta z) +
            airyBesselIOnLog (-(2 / 3)) (airyLogZeta z)) := by
  rw [airyBesselIOnLog_airyLogZeta _ hz, airyBesselIOnLog_airyLogZeta _ hz]
  simp only [airyBiDeriv, airyFDeriv, airyGDeriv]
  obtain ⟨g1, g2⟩ := airy_deriv_exp_relations hz
  have hC := reg0F1_one_third (z ^ 3 / 9)
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [show z / ((Real.sqrt 3 : ℝ) : ℂ) = z * ((Real.sqrt 3 : ℝ) : ℂ) / 3 by
    field_simp; linear_combination -hs]
  rw [show (-(2 / 3 : ℂ)) + 1 = 1 / 3 by norm_num, show (2 / 3 : ℂ) + 1 = 5 / 3 by norm_num]
  set F53 := regularizedHGFun (∅ : Multiset ℂ) {5 / 3} (z ^ 3 / 9)
  set F13 := regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (z ^ 3 / 9)
  set r := ((Real.sqrt 3 : ℝ) : ℂ)
  linear_combination (-(r / 3) * F53) * g1 - (r / 3 * F13) * g2 -
    3 * r * (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * hC

/-- The logarithmic `K`-Bessel function is even in its order. -/
theorem airyBesselKOnLog_neg (ν w : ℂ) : airyBesselKOnLog (-ν) w = airyBesselKOnLog ν w := by
  simp only [airyBesselKOnLog, neg_neg, mul_neg, Complex.sin_neg]
  rw [div_neg]; ring

/-- `sin (π/3) = √3/2` in `ℂ`. -/
theorem sin_pi_mul_one_third : sin (π * (1 / 3)) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
  rw [show (π * (1 / 3) : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_div_three]

/-- `sin (2π/3) = √3/2` in `ℂ`. -/
theorem sin_pi_mul_two_thirds : sin (π * (2 / 3)) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
  rw [show (π * (2 / 3) : ℂ) = ((π - π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_sub, Real.sin_pi_div_three]

/-- `(z/3)^{1/2}` in terms of `z^{1/2}` and `√3`. -/
theorem half_cpow_div_three_mul_sqrt {z : ℂ} (hz : z ≠ 0) :
    (z / 3) ^ (1 / 2 : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = z ^ (1 / 2 : ℂ) := by
  rw [half_cpow_div_three hz, cpow_def_of_ne_zero hz, sqrt_three_eq_exp, ← exp_add]
  congr 1; ring

/-- `Ai(z) = π⁻¹ (z/3)^{1/2} K_{±1/3}(ζ)` with `ζ = (2/3) z^{3/2}` on the logarithmic plane,
for `z ≠ 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_besselK_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAi z = ((z / 3) ^ (1 / 2 : ℂ)) / π * airyBesselKOnLog (ε * (1 / 3)) (airyLogZeta z) := by
  have hK : airyBesselKOnLog (ε * (1 / 3)) (airyLogZeta z) =
      airyBesselKOnLog (1 / 3) (airyLogZeta z) := by
    rcases hε with rfl | rfl
    · norm_num
    · rw [show ((-1 : ℝ) : ℂ) * (1 / 3) = -(1 / 3) by push_cast; ring, airyBesselKOnLog_neg]
  rw [hK, airyBesselKOnLog, sin_pi_mul_one_third, airyAi_eq_besselI_complex hz,
    ← half_cpow_div_three_mul_sqrt hz]
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  linear_combination ((z / 3) ^ (1 / 2 : ℂ) * (airyBesselIOnLog (-(1 / 3)) (airyLogZeta z) -
    airyBesselIOnLog (1 / 3) (airyLogZeta z))) * hs

/-- `Ai'(z) = -π⁻¹ (z/√3) K_{±2/3}(ζ)` with `ζ = (2/3) z^{3/2}` on the logarithmic plane,
for `z ≠ 0` (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_besselK_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAiDeriv z = -(z / Real.sqrt 3) / π * airyBesselKOnLog (ε * (2 / 3)) (airyLogZeta z) := by
  have hK : airyBesselKOnLog (ε * (2 / 3)) (airyLogZeta z) =
      airyBesselKOnLog (2 / 3) (airyLogZeta z) := by
    rcases hε with rfl | rfl
    · norm_num
    · rw [show ((-1 : ℝ) : ℂ) * (2 / 3) = -(2 / 3) by push_cast; ring, airyBesselKOnLog_neg]
  rw [hK, airyBesselKOnLog, sin_pi_mul_two_thirds, airyAiDeriv_eq_besselI_complex hz]
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  linear_combination (airyBesselIOnLog (2 / 3) (airyLogZeta z) -
    airyBesselIOnLog (-(2 / 3)) (airyLogZeta z)) * hs

/-- `Ai(-z) = (z^{1/2}/3) (J_{1/3}(ζ) + J_{-1/3}(ζ))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.6). -/
@[dlmf 9.6.E6]
theorem airyAi_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi (-z) =
      z ^ (1 / 2 : ℂ) / 3 *
        (airyBesselJOnLog (1 / 3) (airyLogZeta z) + airyBesselJOnLog (-1 / 3) (airyLogZeta z)) := by
  rw [airyBesselJOnLog_airyLogZeta _ hz, airyBesselJOnLog_airyLogZeta _ hz,
    cpow_def_of_ne_zero hz]
  simp only [airyAi, airyF, airyG, three_rpow_eq_exp]
  rw [show (-z) ^ 3 / 9 = -(z ^ 3 / 9) by ring]
  have e1 : exp (log z * (1 / 2)) * exp (3 / 2 * (-1 / 3) * log z) = 1 := by
    rw [← exp_add, show log z * (1 / 2) + 3 / 2 * (-1 / 3) * log z = 0 by ring, exp_zero]
  have e2 : exp (log z * (1 / 2)) * exp (3 / 2 * (1 / 3) * log z) = z := by
    rw [← exp_add, show log z * (1 / 2) + 3 / 2 * (1 / 3) * log z = log z by ring, exp_log hz]
  have e3 : exp (-(-1 / 3) * log 3) / 3 = exp (((-(2 / 3) : ℝ) : ℂ) * log 3) := by
    rw [div_eq_iff (by norm_num), ← exp_log (show (3 : ℂ) ≠ 0 by norm_num), ← exp_add,
      exp_log (show (3 : ℂ) ≠ 0 by norm_num)]
    congr 1; push_cast; ring
  have e4 : exp (-(1 / 3) * log 3) / 3 = exp (((-(4 / 3) : ℝ) : ℂ) * log 3) := by
    rw [div_eq_iff (by norm_num), ← exp_log (show (3 : ℂ) ≠ 0 by norm_num), ← exp_add,
      exp_log (show (3 : ℂ) ≠ 0 by norm_num)]
    congr 1; push_cast; ring
  rw [show (-1 / 3 : ℂ) + 1 = 2 / 3 by norm_num, show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num]
  set F := regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (-(z ^ 3 / 9))
  set G := regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (-(z ^ 3 / 9))
  linear_combination (-F) * e3 - F * (exp (-(-1 / 3) * log 3) / 3) * e1 -
    G * (exp (-(1 / 3) * log 3) / 3) * e2 - G * z * e4

/-- `Bi(-z) = (z/3)^{1/2} (J_{-1/3}(ζ) - J_{1/3}(ζ))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.8). -/
@[dlmf 9.6.E8]
theorem airyBi_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi (-z) =
      ((z / 3) ^ (1 / 2 : ℂ)) *
        (airyBesselJOnLog (-(1 / 3)) (airyLogZeta z) -
            airyBesselJOnLog (1 / 3) (airyLogZeta z)) := by
  rw [airyBesselJOnLog_airyLogZeta _ hz, airyBesselJOnLog_airyLogZeta _ hz, half_cpow_div_three hz]
  simp only [airyBi, airyF, airyG]
  rw [show (-z) ^ 3 / 9 = -(z ^ 3 / 9) by ring]
  have f1 : exp ((log z - log 3) * (1 / 2)) * exp (-(-(1 / 3)) * log 3) *
      exp (3 / 2 * -(1 / 3) * log z) =
        ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) := by
    rw [three_rpow_eq_exp, sqrt_three_eq_exp]
    simp only [← exp_add]; congr 1; push_cast; ring
  have f2 : exp ((log z - log 3) * (1 / 2)) * exp (-(1 / 3) * log 3) *
      exp (3 / 2 * (1 / 3) * log z) =
        ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * exp (log z) := by
    rw [three_rpow_eq_exp, sqrt_three_eq_exp]
    simp only [← exp_add]; congr 1; push_cast; ring
  rw [exp_log hz] at f2
  rw [show (-(1 / 3 : ℂ)) + 1 = 2 / 3 by norm_num, show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num]
  set F := regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (-(z ^ 3 / 9))
  set G := regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (-(z ^ 3 / 9))
  linear_combination (-F) * f1 + G * f2

/-- `Ai'(-z) = (z/3) (J_{2/3}(ζ) - J_{-2/3}(ζ))` with `ζ = (2/3) z^{3/2}` on the logarithmic
plane, for `z ≠ 0` (DLMF 9.6.7). -/
@[dlmf 9.6.E7]
theorem airyAiDeriv_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv (-z) =
      z / 3 *
        (airyBesselJOnLog (2 / 3) (airyLogZeta z) - airyBesselJOnLog (-2 / 3) (airyLogZeta z)) := by
  rw [show (-2 / 3 : ℂ) = -(2 / 3) by ring]
  rw [airyBesselJOnLog_airyLogZeta _ hz, airyBesselJOnLog_airyLogZeta _ hz]
  simp only [airyAiDeriv, airyFDeriv, airyGDeriv]
  rw [show (-z) ^ 3 / 9 = -(z ^ 3 / 9) by ring]
  obtain ⟨g1, g2⟩ := airy_deriv_exp_relations hz
  have hC := reg0F1_one_third (-(z ^ 3 / 9))
  rw [show (-(2 / 3 : ℂ)) + 1 = 1 / 3 by norm_num, show (2 / 3 : ℂ) + 1 = 5 / 3 by norm_num]
  set F53 := regularizedHGFun (∅ : Multiset ℂ) {5 / 3} (-(z ^ 3 / 9))
  set F13 := regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (-(z ^ 3 / 9))
  linear_combination (-F53 / 3) * g1 + (F13 / 3) * g2 +
    3 * (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * hC

/-- `Bi'(-z) = (z/√3) (J_{-2/3}(ζ) + J_{2/3}(ζ))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.9). -/
@[dlmf 9.6.E9]
theorem airyBiDeriv_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv (-z) =
      (z / Real.sqrt 3) *
        (airyBesselJOnLog (-(2 / 3)) (airyLogZeta z) +
            airyBesselJOnLog (2 / 3) (airyLogZeta z)) := by
  rw [airyBesselJOnLog_airyLogZeta _ hz, airyBesselJOnLog_airyLogZeta _ hz]
  simp only [airyBiDeriv, airyFDeriv, airyGDeriv]
  rw [show (-z) ^ 3 / 9 = -(z ^ 3 / 9) by ring]
  obtain ⟨g1, g2⟩ := airy_deriv_exp_relations hz
  have hC := reg0F1_one_third (-(z ^ 3 / 9))
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [show z / ((Real.sqrt 3 : ℝ) : ℂ) = z * ((Real.sqrt 3 : ℝ) : ℂ) / 3 by
    field_simp; linear_combination -hs]
  rw [show (-(2 / 3 : ℂ)) + 1 = 1 / 3 by norm_num, show (2 / 3 : ℂ) + 1 = 5 / 3 by norm_num]
  set F53 := regularizedHGFun (∅ : Multiset ℂ) {5 / 3} (-(z ^ 3 / 9))
  set F13 := regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (-(z ^ 3 / 9))
  set r := ((Real.sqrt 3 : ℝ) : ℂ)
  linear_combination (-(r / 3) * F53) * g1 - (r / 3 * F13) * g2 -
    3 * r * (((3 : ℝ) ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) * hC

/-- `z^{1/2} · z^{-1/2} = 1` for `z ≠ 0`. -/
theorem half_cpow_mul_neg_half {z : ℂ} (hz : z ≠ 0) :
    z ^ (1 / 2 : ℂ) * z ^ (-(1 / 2) : ℂ) = 1 := by
  rw [← cpow_add _ _ hz]; norm_num

/-- `√3 · √3 = 3` in `ℂ`. -/
theorem sqrt_three_mul_self_complex : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-- `√3 ≠ 0` in `ℂ`. -/
theorem sqrt_three_ne_zero_complex : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'

/-- `J_ν(w + iπ/2) = e^{iπν/2} I_ν(w)` on the logarithmic plane. -/
theorem airyBesselJOnLog_add_half_pi_I (ν w : ℂ) :
    airyBesselJOnLog ν (w + π * I / 2) = exp (ν * (π * I / 2)) * airyBesselIOnLog ν w := by
  simp only [airyBesselJOnLog, airyBesselIOnLog]
  rw [show 2 * (w + π * I / 2) = 2 * w + π * I by ring, exp_add, exp_pi_mul_I,
    show ν * (w + π * I / 2 - log 2) = ν * (π * I / 2) + ν * (w - log 2) by ring, exp_add,
    show -(exp (2 * w) * -1) / 4 = exp (2 * w) / 4 by ring, mul_assoc]

/-- `J_ν(w - iπ/2) = e^{-iπν/2} I_ν(w)` on the logarithmic plane. -/
theorem airyBesselJOnLog_sub_half_pi_I (ν w : ℂ) :
    airyBesselJOnLog ν (w - π * I / 2) = exp (-ν * (π * I / 2)) * airyBesselIOnLog ν w := by
  simp only [airyBesselJOnLog, airyBesselIOnLog]
  rw [show 2 * (w - π * I / 2) = 2 * w - π * I by ring, exp_sub, exp_pi_mul_I,
    show ν * (w - π * I / 2 - log 2) = -ν * (π * I / 2) + ν * (w - log 2) by ring, exp_add,
    show -(exp (2 * w) / -1) / 4 = exp (2 * w) / 4 by ring, mul_assoc]

/-- `exp (c π i) = cos (c π) + i sin (c π)` for real `c`. -/
theorem exp_real_mul_pi_I (c : ℝ) {x : ℂ} (hx : x = (c : ℂ) * (π * I)) :
    exp x = (Real.cos (c * π) : ℂ) + (Real.sin (c * π) : ℂ) * I := by
  rw [hx, show (c : ℂ) * (π * I) = ((c * π : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin]

/-- `exp (iπ/6) = √3/2 + i/2`. -/
theorem exp_pi_I_sixth {x : ℂ} (hx : x = (1 / 6 : ℝ) * (π * I)) :
    exp x = ((Real.sqrt 3 : ℝ) : ℂ) / 2 + 1 / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (1 / 6 : ℝ) * π = π / 6 by ring, Real.cos_pi_div_six,
    Real.sin_pi_div_six]; push_cast; ring

/-- `exp (-iπ/6) = √3/2 - i/2`. -/
theorem exp_neg_pi_I_sixth {x : ℂ} (hx : x = (-(1 / 6) : ℝ) * (π * I)) :
    exp x = ((Real.sqrt 3 : ℝ) : ℂ) / 2 - 1 / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (-(1 / 6) : ℝ) * π = -(π / 6) by ring, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six]; push_cast; ring

/-- `exp (iπ/3) = 1/2 + i√3/2`. -/
theorem exp_pi_I_third {x : ℂ} (hx : x = (1 / 3 : ℝ) * (π * I)) :
    exp x = 1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (1 / 3 : ℝ) * π = π / 3 by ring, Real.cos_pi_div_three,
    Real.sin_pi_div_three]; push_cast; ring

/-- `exp (-iπ/3) = 1/2 - i√3/2`. -/
theorem exp_neg_pi_I_third {x : ℂ} (hx : x = (-(1 / 3) : ℝ) * (π * I)) :
    exp x = 1 / 2 - ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (-(1 / 3) : ℝ) * π = -(π / 3) by ring, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three]; push_cast; ring

/-- `exp (2iπ/3) = -1/2 + i√3/2`. -/
theorem exp_two_pi_I_third {x : ℂ} (hx : x = (2 / 3 : ℝ) * (π * I)) :
    exp x = -1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (2 / 3 : ℝ) * π = π - π / 3 by ring, Real.cos_pi_sub,
    Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]; push_cast; ring

/-- `exp (-2iπ/3) = -1/2 - i√3/2`. -/
theorem exp_neg_two_pi_I_third {x : ℂ} (hx : x = (-(2 / 3) : ℝ) * (π * I)) :
    exp x = -1 / 2 - ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (-(2 / 3) : ℝ) * π = -(π - π / 3) by ring, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three]; push_cast; ring

/-- `exp (5iπ/6) = -√3/2 + i/2`. -/
theorem exp_five_pi_I_sixth {x : ℂ} (hx : x = (5 / 6 : ℝ) * (π * I)) :
    exp x = -((Real.sqrt 3 : ℝ) : ℂ) / 2 + 1 / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (5 / 6 : ℝ) * π = π - π / 6 by ring, Real.cos_pi_sub,
    Real.sin_pi_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]; push_cast; ring

/-- `exp (-5iπ/6) = -√3/2 - i/2`. -/
theorem exp_neg_five_pi_I_sixth {x : ℂ} (hx : x = (-(5 / 6) : ℝ) * (π * I)) :
    exp x = -((Real.sqrt 3 : ℝ) : ℂ) / 2 - 1 / 2 * I := by
  rw [exp_real_mul_pi_I _ hx, show (-(5 / 6) : ℝ) * π = -(π - π / 6) by ring, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_six,
    Real.sin_pi_div_six]; push_cast; ring

/-- `cos (π/3) = 1/2` in `ℂ`. -/
theorem cos_pi_mul_one_third : cos (π * (1 / 3)) = 1 / 2 := by
  rw [show (π * (1 / 3) : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_pi_div_three]; push_cast; ring

/-- `cos (2π/3) = -1/2` in `ℂ`. -/
theorem cos_pi_mul_two_thirds : cos (π * (2 / 3)) = -1 / 2 := by
  rw [show (π * (2 / 3) : ℂ) = ((π - π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_pi_sub, Real.cos_pi_div_three]; push_cast; ring

/-- `sin (π/3) = √3/2` in `ℂ`. -/
theorem sin_pi_mul_third_eq : sin (π * (1 / 3)) = ((Real.sqrt 3 : ℝ) : ℂ) / 2 := by
  rw [sin_pi_mul_one_third]; push_cast; ring

/-- `cos (-π/3) = 1/2` in `ℂ`. -/
theorem cos_pi_mul_neg_third_eq : cos (π * -(1 / 3)) = 1 / 2 := by
  rw [mul_neg, cos_neg, cos_pi_mul_one_third]

/-- `sin (-π/3) = -√3/2` in `ℂ`. -/
theorem sin_pi_mul_neg_third_eq : sin (π * -(1 / 3)) = -(((Real.sqrt 3 : ℝ) : ℂ) / 2) := by
  rw [mul_neg, sin_neg, sin_pi_mul_third_eq]

/-- `sin (2π/3) = √3/2` in `ℂ`. -/
theorem sin_pi_mul_two_thirds_eq : sin (π * (2 / 3)) = ((Real.sqrt 3 : ℝ) : ℂ) / 2 := by
  rw [sin_pi_mul_two_thirds]; push_cast; ring

/-- `cos (-2π/3) = -1/2` in `ℂ`. -/
theorem cos_pi_mul_neg_two_thirds_eq : cos (π * -(2 / 3)) = -1 / 2 := by
  rw [mul_neg, cos_neg, cos_pi_mul_two_thirds]

/-- `sin (-2π/3) = -√3/2` in `ℂ`. -/
theorem sin_pi_mul_neg_two_thirds_eq : sin (π * -(2 / 3)) = -(((Real.sqrt 3 : ℝ) : ℂ) / 2) := by
  rw [mul_neg, sin_neg, sin_pi_mul_two_thirds_eq]

/-- `√3 ^ 3 = 3√3` in `ℂ`. -/
theorem sqrt_three_pow_three_complex : ((Real.sqrt 3 : ℝ) : ℂ) ^ 3 = 3 *
    ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [pow_succ, sqrt_three_sq]

/-- `Ai(z) = ½ (z/3)^{1/2} e^{2πi/3} H⁽¹⁾_{1/3}(ζ e^{πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel1_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (2 * π * I / 3) *
        airyHankel1OnLog (1 * (1 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (1 / 3) : ℂ) = 1 / 3 by ring]
  rw [show (airyLogZeta z + 1 * (π * I / 2) : ℂ) = airyLogZeta z + π * I / 2 by ring]
  rw [airyAi_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I]
  rw [exp_two_pi_I_third (x := (2 * π * I / 3 : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (1 / 3 * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(1 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_one_third, sin_pi_mul_third_eq]
  rw [← hR] at hPQ ⊢
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai(z) = ½ (z/3)^{1/2} e^{πi/3} H⁽¹⁾_{-1/3}(ζ e^{πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel1_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (π * I / 3) * airyHankel1OnLog (-1 * (1 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (1 / 3) : ℂ) = -(1 / 3) by ring]
  rw [show (airyLogZeta z + 1 * (π * I / 2) : ℂ) = airyLogZeta z + π * I / 2 by ring]
  rw [airyAi_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I]
  rw [exp_pi_I_third (x := (π * I / 3 : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(1 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-(1 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_third_eq, sin_pi_mul_neg_third_eq]
  rw [← hR] at hPQ ⊢
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai(z) = ½ (z/3)^{1/2} e^{-2πi/3} H⁽²⁾_{1/3}(ζ e^{-πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel2_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (-(2 * π * I / 3)) *
        airyHankel2OnLog (1 * (1 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (1 / 3) : ℂ) = 1 / 3 by ring]
  rw [show (airyLogZeta z + -1 * (π * I / 2) : ℂ) = airyLogZeta z - π * I / 2 by ring]
  rw [airyAi_eq_besselI_complex hz]
  simp only [airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_sub_half_pi_I]
  rw [exp_neg_two_pi_I_third (x := (-(2 * π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(1 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-(1 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_one_third, sin_pi_mul_third_eq]
  rw [← hR] at hPQ ⊢
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai(z) = ½ (z/3)^{1/2} e^{-πi/3} H⁽²⁾_{-1/3}(ζ e^{-πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel2_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (-(π * I / 3)) *
        airyHankel2OnLog (-1 * (1 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (1 / 3) : ℂ) = -(1 / 3) by ring]
  rw [show (airyLogZeta z + -1 * (π * I / 2) : ℂ) = airyLogZeta z - π * I / 2 by ring]
  rw [airyAi_eq_besselI_complex hz]
  simp only [airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_sub_half_pi_I]
  rw [exp_neg_pi_I_third (x := (-(π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-(1 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(-(-(1 / 3))) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_third_eq, sin_pi_mul_neg_third_eq]
  rw [← hR] at hPQ ⊢
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai'(z) = ½ (z/√3) e^{-πi/6} H⁽¹⁾_{2/3}(ζ e^{πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel1_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-π * I / 6) * airyHankel1OnLog (1 * (2 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (2 / 3) : ℂ) = 2 / 3 by ring]
  rw [show (airyLogZeta z + 1 * (π * I / 2) : ℂ) = airyLogZeta z + π * I / 2 by ring]
  rw [airyAiDeriv_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I]
  rw [exp_neg_pi_I_sixth (x := (-π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (2 / 3 * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(2 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_two_thirds, sin_pi_mul_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai'(z) = ½ (z/√3) e^{-5πi/6} H⁽¹⁾_{-2/3}(ζ e^{πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel1_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-5 * π * I / 6) *
        airyHankel1OnLog (-1 * (2 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (2 / 3) : ℂ) = -(2 / 3) by ring]
  rw [show (airyLogZeta z + 1 * (π * I / 2) : ℂ) = airyLogZeta z + π * I / 2 by ring]
  rw [airyAiDeriv_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I]
  rw [exp_neg_five_pi_I_sixth (x := (-5 * π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(2 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (-(-(2 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_two_thirds_eq, sin_pi_mul_neg_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai'(z) = ½ (z/√3) e^{πi/6} H⁽²⁾_{2/3}(ζ e^{-πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel2_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-(-π * I / 6)) * airyHankel2OnLog (1 * (2 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (2 / 3) : ℂ) = 2 / 3 by ring]
  rw [show (airyLogZeta z + -1 * (π * I / 2) : ℂ) = airyLogZeta z - π * I / 2 by ring]
  rw [airyAiDeriv_eq_besselI_complex hz]
  simp only [airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_sub_half_pi_I]
  rw [exp_pi_I_sixth (x := (-(-π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(2 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (-(-(2 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_two_thirds, sin_pi_mul_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai'(z) = ½ (z/√3) e^{5πi/6} H⁽²⁾_{-2/3}(ζ e^{-πi/2})`, `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel2_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-(-5 * π * I / 6)) *
        airyHankel2OnLog (-1 * (2 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (2 / 3) : ℂ) = -(2 / 3) by ring]
  rw [show (airyLogZeta z + -1 * (π * I / 2) : ℂ) = airyLogZeta z - π * I / 2 by ring]
  rw [airyAiDeriv_eq_besselI_complex hz]
  simp only [airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_sub_half_pi_I]
  rw [exp_five_pi_I_sixth (x := (-(-5 * π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (-(-(2 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(-(-(2 / 3))) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_two_thirds_eq, sin_pi_mul_neg_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Bi(z) = ½ (z/3)^{1/2} (e^{πi/6} H⁽¹⁾_{1/3}(ζ e^{-πi/2}) + e^{-πi/6} H⁽²⁾_{1/3}(ζ e^{πi/2}))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.4). -/
@[dlmf 9.6.E4]
theorem airyBi_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (1 * (π * I / 6)) * airyHankel1OnLog (1 * (1 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(1 * (π * I / 6))) * airyHankel2OnLog (1 * (1 / 3)) (airyLogZeta z + π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (1 / 3) : ℂ) = 1 / 3 by ring]
  rw [airyBi_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I, airyBesselJOnLog_sub_half_pi_I]
  rw [exp_pi_I_sixth (x := (1 * (π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(1 * (π * I / 6)) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (1 / 3 * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(1 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-(1 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_one_third, sin_pi_mul_third_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Bi(z) = ½ (z/3)^{1/2} (e^{-πi/6} H⁽¹⁾_{-1/3}(ζ e^{-πi/2}) + e^{πi/6} H⁽²⁾_{-1/3}(ζ e^{πi/2}))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.4). -/
@[dlmf 9.6.E4]
theorem airyBi_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (-1 * (π * I / 6)) * airyHankel1OnLog (-1 * (1 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(-1 * (π * I / 6))) *
            airyHankel2OnLog (-1 * (1 / 3)) (airyLogZeta z + π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (1 / 3) : ℂ) = -(1 / 3) by ring]
  rw [airyBi_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I, airyBesselJOnLog_sub_half_pi_I]
  rw [exp_neg_pi_I_sixth (x := (-1 * (π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-1 * (π * I / 6)) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(1 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-(1 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(-(-(1 / 3))) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_third_eq, sin_pi_mul_neg_third_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Bi'(z) = ½ (z/√3) (e^{πi/3} H⁽¹⁾_{2/3}(ζ e^{-πi/2}) + e^{-πi/3} H⁽²⁾_{2/3}(ζ e^{πi/2}))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.5). -/
@[dlmf 9.6.E5]
theorem airyBiDeriv_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = 1 / 2 * (z / Real.sqrt 3) *
      (exp (1 * (π * I / 3)) * airyHankel1OnLog (1 * (2 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(1 * (π * I / 3))) * airyHankel2OnLog (1 * (2 / 3)) (airyLogZeta z + π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (2 / 3) : ℂ) = 2 / 3 by ring]
  rw [airyBiDeriv_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I, airyBesselJOnLog_sub_half_pi_I]
  rw [exp_pi_I_third (x := (1 * (π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(1 * (π * I / 3)) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (2 / 3 * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(2 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (-(-(2 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_two_thirds, sin_pi_mul_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Bi'(z) = ½ (z/√3) (e^{-πi/3} H⁽¹⁾_{-2/3}(ζ e^{-πi/2}) + e^{πi/3} H⁽²⁾_{-2/3}(ζ e^{πi/2}))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.5). -/
@[dlmf 9.6.E5]
theorem airyBiDeriv_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-1 * (π * I / 3)) * airyHankel1OnLog (-1 * (2 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(-1 * (π * I / 3))) *
            airyHankel2OnLog (-1 * (2 / 3)) (airyLogZeta z + π * I / 2)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (2 / 3) : ℂ) = -(2 / 3) by ring]
  rw [airyBiDeriv_eq_besselI_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  simp only [airyBesselJOnLog_add_half_pi_I, airyBesselJOnLog_sub_half_pi_I]
  rw [exp_neg_pi_I_third (x := (-1 * (π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (-(-1 * (π * I / 3)) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(2 / 3) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (-(-(2 / 3)) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(-(-(2 / 3))) * (π * I / 2) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_two_thirds_eq, sin_pi_mul_neg_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `Ai(-z) = ½ (z/3)^{1/2} (e^{πi/6} H⁽¹⁾_{1/3}(ζ) + e^{-πi/6} H⁽²⁾_{1/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.6). -/
@[dlmf 9.6.E6]
theorem airyAi_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (π * I / 6) * airyHankel1OnLog (1 * (1 / 3)) (airyLogZeta z) +
        exp (-(π * I / 6)) * airyHankel2OnLog (1 * (1 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (1 / 3) : ℂ) = 1 / 3 by ring]
  rw [airyAi_neg_eq_besselJ_complex hz, show (-1 / 3 : ℂ) = -(1 / 3) by ring]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_pi_I_sixth (x := (π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_sixth (x := (-(π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_one_third, sin_pi_mul_third_eq]
  rw [← hR] at hPQ ⊢
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq]
  ring_nf

/-- `Ai(-z) = ½ (z/3)^{1/2} (e^{-πi/6} H⁽¹⁾_{-1/3}(ζ) + e^{πi/6} H⁽²⁾_{-1/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.6). -/
@[dlmf 9.6.E6]
theorem airyAi_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (-π * I / 6) * airyHankel1OnLog (-1 * (1 / 3)) (airyLogZeta z) +
        exp (-(-π * I / 6)) * airyHankel2OnLog (-1 * (1 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (1 / 3) : ℂ) = -(1 / 3) by ring]
  rw [airyAi_neg_eq_besselJ_complex hz, show (-1 / 3 : ℂ) = -(1 / 3) by ring]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_neg_pi_I_sixth (x := (-π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_third_eq, sin_pi_mul_neg_third_eq]
  rw [← hR] at hPQ ⊢
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq]
  ring_nf

/-- `Ai'(-z) = ½ (z/√3) (e^{-πi/6} H⁽¹⁾_{2/3}(ζ) + e^{πi/6} H⁽²⁾_{2/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.7). -/
@[dlmf 9.6.E7]
theorem airyAiDeriv_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-π * I / 6) * airyHankel1OnLog (1 * (2 / 3)) (airyLogZeta z) +
        exp (-(-π * I / 6)) * airyHankel2OnLog (1 * (2 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (2 / 3) : ℂ) = 2 / 3 by ring]
  rw [airyAiDeriv_neg_eq_besselJ_complex hz, show (-2 / 3 : ℂ) = -(2 / 3) by ring]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_neg_pi_I_sixth (x := (-π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_sixth (x := (-(-π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_two_thirds, sin_pi_mul_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq]
  ring_nf

/-- `Ai'(-z) = ½ (z/√3) (e^{-5πi/6} H⁽¹⁾_{-2/3}(ζ) + e^{5πi/6} H⁽²⁾_{-2/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.7). -/
@[dlmf 9.6.E7]
theorem airyAiDeriv_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-5 * π * I / 6) * airyHankel1OnLog (-1 * (2 / 3)) (airyLogZeta z) +
        exp (-(-5 * π * I / 6)) * airyHankel2OnLog (-1 * (2 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (2 / 3) : ℂ) = -(2 / 3) by ring]
  rw [airyAiDeriv_neg_eq_besselJ_complex hz, show (-2 / 3 : ℂ) = -(2 / 3) by ring]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_neg_five_pi_I_sixth (x := (-5 * π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [exp_five_pi_I_sixth (x := (-(-5 * π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_two_thirds_eq, sin_pi_mul_neg_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq]
  ring_nf

/-- `Bi(-z) = ½ (z/3)^{1/2} (e^{2πi/3} H⁽¹⁾_{1/3}(ζ) + e^{-2πi/3} H⁽²⁾_{1/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.8). -/
@[dlmf 9.6.E8]
theorem airyBi_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (2 * π * I / 3) * airyHankel1OnLog (1 * (1 / 3)) (airyLogZeta z) +
        exp (-(2 * π * I / 3)) * airyHankel2OnLog (1 * (1 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (1 / 3) : ℂ) = 1 / 3 by ring]
  rw [airyBi_neg_eq_besselJ_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_two_pi_I_third (x := (2 * π * I / 3 : ℂ)) (by push_cast; ring)]
  rw [exp_neg_two_pi_I_third (x := (-(2 * π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_one_third, sin_pi_mul_third_eq]
  field_simp
  ring_nf
  simp only [I_sq]
  ring_nf

/-- `Bi(-z) = ½ (z/3)^{1/2} (e^{πi/3} H⁽¹⁾_{-1/3}(ζ) + e^{-πi/3} H⁽²⁾_{-1/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.8). -/
@[dlmf 9.6.E8]
theorem airyBi_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (π * I / 3) * airyHankel1OnLog (-1 * (1 / 3)) (airyLogZeta z) +
        exp (-(π * I / 3)) * airyHankel2OnLog (-1 * (1 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (1 / 3) : ℂ) = -(1 / 3) by ring]
  rw [airyBi_neg_eq_besselJ_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_pi_I_third (x := (π * I / 3 : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_third_eq, sin_pi_mul_neg_third_eq]
  field_simp
  ring_nf
  simp only [I_sq]
  ring_nf

/-- `Bi'(-z) = ½ (z/√3) (e^{πi/3} H⁽¹⁾_{2/3}(ζ) + e^{-πi/3} H⁽²⁾_{2/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.9). -/
@[dlmf 9.6.E9]
theorem airyBiDeriv_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (π * I / 3) * airyHankel1OnLog (1 * (2 / 3)) (airyLogZeta z) +
        exp (-(π * I / 3)) * airyHankel2OnLog (1 * (2 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1 * (2 / 3) : ℂ) = 2 / 3 by ring]
  rw [airyBiDeriv_neg_eq_besselJ_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_pi_I_third (x := (π * I / 3 : ℂ)) (by push_cast; ring)]
  rw [exp_neg_pi_I_third (x := (-(π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_two_thirds, sin_pi_mul_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq]
  ring_nf

/-- `Bi'(-z) = ½ (z/√3) (e^{-πi/3} H⁽¹⁾_{-2/3}(ζ) + e^{πi/3} H⁽²⁾_{-2/3}(ζ))`,
`ζ = (2/3) z^{3/2}` on the logarithmic plane, for `z ≠ 0` (DLMF 9.6.9). -/
@[dlmf 9.6.E9]
theorem airyBiDeriv_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-π * I / 3) * airyHankel1OnLog (-1 * (2 / 3)) (airyLogZeta z) +
        exp (-(-π * I / 3)) * airyHankel2OnLog (-1 * (2 / 3)) (airyLogZeta z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (-1 * (2 / 3) : ℂ) = -(2 / 3) by ring]
  rw [airyBiDeriv_neg_eq_besselJ_complex hz]
  simp only [airyHankel1OnLog, airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_neg_pi_I_third (x := (-π * I / 3 : ℂ)) (by push_cast; ring)]
  rw [exp_pi_I_third (x := (-(-π * I / 3) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_neg_two_thirds_eq, sin_pi_mul_neg_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq]
  ring_nf

/-- `J_{±1/3}(ζ) = ½ √(3/z) (√3 Ai(-z) ∓ Bi(-z))` with `ζ = (2/3) z^{3/2}` on the logarithmic
plane, for `z ≠ 0` (DLMF 9.6.11). The DLMF factor `√(3/z)` is written
`√3 z^{-1/2}`, which agrees with the logarithmic left side also on the negative real axis
(corrected 2026-10-20). The sign of `Bi` follows DLMF; the earlier transcription had
the bracket of 9.6.13. -/
@[dlmf 9.6.E11]
theorem besselJ_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselJOnLog (ε * (1 / 3)) (airyLogZeta z) =
      1 / 2 * (Real.sqrt 3 * z ^ (-(1 / 2) : ℂ)) *
          (Real.sqrt 3 * airyAi (-z) - ε * airyBi (-z)) := by
  have hA := airyAi_neg_eq_besselJ_complex hz
  have hB := airyBi_neg_eq_besselJ_complex hz
  rw [show (-1 / 3 : ℂ) = -(1 / 3) by ring] at hA
  have hPQ := half_cpow_mul_neg_half hz
  have hR := half_cpow_div_three_mul_sqrt hz
  have hs := sqrt_three_mul_self_complex
  rcases hε with rfl | rfl
  · push_cast; rw [one_mul]
    set P := z ^ (1 / 2 : ℂ)
    set Q := z ^ (-(1 / 2) : ℂ)
    set R := (z / 3) ^ (1 / 2 : ℂ)
    set s := ((Real.sqrt 3 : ℝ) : ℂ)
    set Jp := airyBesselJOnLog (1 / 3) (airyLogZeta z)
    set Jm := airyBesselJOnLog (-(1 / 3)) (airyLogZeta z)
    linear_combination (-1/2*s*s*Q) * hA + (1/2*s*Q)*hB - (Q*P*(Jp+Jm)/6)*hs - ((Jp+Jm)/2)*hPQ
      + ((Jm-Jp)/2)*hPQ + (Q*(Jm-Jp)/2)*hR
  · push_cast; rw [neg_one_mul]
    set P := z ^ (1 / 2 : ℂ)
    set Q := z ^ (-(1 / 2) : ℂ)
    set R := (z / 3) ^ (1 / 2 : ℂ)
    set s := ((Real.sqrt 3 : ℝ) : ℂ)
    set Jp := airyBesselJOnLog (1 / 3) (airyLogZeta z)
    set Jm := airyBesselJOnLog (-(1 / 3)) (airyLogZeta z)
    linear_combination (-1/2*s*s*Q) * hA - (1/2*s*Q)*hB - (Q*P*(Jp+Jm)/6)*hs - ((Jp+Jm)/2)*hPQ
      - ((Jm-Jp)/2)*hPQ - (Q*(Jm-Jp)/2)*hR

end DLMF.Airy
end
