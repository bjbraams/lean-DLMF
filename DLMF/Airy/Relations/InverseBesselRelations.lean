/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Relations.BesselRepresentations

/-!
# Bessel functions expressed through Airy functions

Inverse Bessel and Hankel relations and their confluent hypergeometric consequences.

Source references and common attribution are retained in
`DLMF.Airy.Relations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology

namespace DLMF.Airy

/-- `J_{±2/3}(ζ) = ½ (√3/z) (±√3 Ai'(-z) + Bi'(-z))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.12). -/
@[dlmf 9.6.E12]
theorem besselJ_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselJOnLog (ε * (2 / 3)) (airyLogZeta z) =
      1 / 2 * (Real.sqrt 3 / z) * (1 * ε * Real.sqrt 3 * airyAiDeriv (-z) + airyBiDeriv (-z)) := by
  have hA := airyAiDeriv_neg_eq_besselJ_complex hz
  have hB := airyBiDeriv_neg_eq_besselJ_complex hz
  rw [show (-2 / 3 : ℂ) = -(2 / 3) by ring] at hA
  have hs := sqrt_three_mul_self_complex
  have hs0 := sqrt_three_ne_zero_complex
  rcases hε with rfl | rfl
  · push_cast; rw [one_mul, hA, hB]
    field_simp
    linear_combination (airyBesselJOnLog (-(2 / 3)) (airyLogZeta z) -
      airyBesselJOnLog (2 / 3) (airyLogZeta z)) * hs
  · push_cast; rw [neg_one_mul, hA, hB]
    field_simp
    linear_combination (airyBesselJOnLog (2 / 3) (airyLogZeta z) -
      airyBesselJOnLog (-(2 / 3)) (airyLogZeta z)) * hs

/-- `I_{±1/3}(ζ) = ½ √(3/z) (∓√3 Ai(z) + Bi(z))` with `ζ = (2/3) z^{3/2}` on the logarithmic
plane, for `z ≠ 0` (DLMF 9.6.13). The DLMF factor `√(3/z)` is written
`√3 z^{-1/2}`, which agrees with the logarithmic left side also on the negative real axis
(corrected 2026-10-20). -/
@[dlmf 9.6.E13]
theorem besselI_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselIOnLog (ε * (1 / 3)) (airyLogZeta z) =
      1 / 2 * (Real.sqrt 3 * z ^ (-(1 / 2) : ℂ)) *
          (-1 * ε * Real.sqrt 3 * airyAi z + airyBi z) := by
  have hA := airyAi_eq_besselI_complex hz
  have hB := airyBi_eq_besselI_complex hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR := half_cpow_div_three_mul_sqrt hz
  have hs := sqrt_three_mul_self_complex
  rcases hε with rfl | rfl
  · push_cast; rw [one_mul]
    set P := z ^ (1 / 2 : ℂ)
    set Q := z ^ (-(1 / 2) : ℂ)
    set R := (z / 3) ^ (1 / 2 : ℂ)
    set s := ((Real.sqrt 3 : ℝ) : ℂ)
    set Jp := airyBesselIOnLog (1 / 3) (airyLogZeta z)
    set Jm := airyBesselIOnLog (-(1 / 3)) (airyLogZeta z)
    linear_combination (1/2*s*s*Q) * hA - (1/2*s*Q)*hB + (Q*P*(Jm-Jp)/6)*hs + ((Jm-Jp)/2)*hPQ
      - ((Jp+Jm)/2)*hPQ - (Q*(Jp+Jm)/2)*hR
  · push_cast; rw [neg_one_mul]
    set P := z ^ (1 / 2 : ℂ)
    set Q := z ^ (-(1 / 2) : ℂ)
    set R := (z / 3) ^ (1 / 2 : ℂ)
    set s := ((Real.sqrt 3 : ℝ) : ℂ)
    set Jp := airyBesselIOnLog (1 / 3) (airyLogZeta z)
    set Jm := airyBesselIOnLog (-(1 / 3)) (airyLogZeta z)
    linear_combination (-1/2*s*s*Q) * hA - (1/2*s*Q)*hB - (Q*P*(Jm-Jp)/6)*hs - ((Jm-Jp)/2)*hPQ
      - ((Jp+Jm)/2)*hPQ - (Q*(Jp+Jm)/2)*hR

/-- `I_{±2/3}(ζ) = ½ (√3/z) (±√3 Ai'(z) + Bi'(z))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.14). -/
@[dlmf 9.6.E14]
theorem besselI_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselIOnLog (ε * (2 / 3)) (airyLogZeta z) =
      1 / 2 * (Real.sqrt 3 / z) * (1 * ε * Real.sqrt 3 * airyAiDeriv z + airyBiDeriv z) := by
  have hA := airyAiDeriv_eq_besselI_complex hz
  have hB := airyBiDeriv_eq_besselI_complex hz
  have hs := sqrt_three_mul_self_complex
  have hs0 := sqrt_three_ne_zero_complex
  rcases hε with rfl | rfl
  · push_cast; rw [one_mul, hA, hB]
    field_simp
    linear_combination (airyBesselIOnLog (-(2 / 3)) (airyLogZeta z) -
      airyBesselIOnLog (2 / 3) (airyLogZeta z)) * hs
  · push_cast; rw [neg_one_mul, hA, hB]
    field_simp
    linear_combination (airyBesselIOnLog (2 / 3) (airyLogZeta z) -
      airyBesselIOnLog (-(2 / 3)) (airyLogZeta z)) * hs

/-- `K_{±1/3}(ζ) = π √(3/z) Ai(z)` with `ζ = (2/3) z^{3/2}` on the logarithmic plane, for
`z ≠ 0` (DLMF 9.6.15). The DLMF factor `√(3/z)` is written
`√3 z^{-1/2}`, which agrees with the logarithmic left side also on the negative real axis
(corrected 2026-10-20). -/
@[dlmf 9.6.E15]
theorem besselK_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselKOnLog (ε * (1 / 3)) (airyLogZeta z) = (π * (Real.sqrt 3 * z ^ (-(1 / 2) : ℂ))) *
        airyAi z := by
  have hA := airyAi_eq_besselK_complex hz hε
  have hPQ := half_cpow_mul_neg_half hz
  have hR := half_cpow_div_three_mul_sqrt hz
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hA]
  set K := airyBesselKOnLog (ε * (1 / 3)) (airyLogZeta z)
  rw [show (π : ℂ) * (((Real.sqrt 3 : ℝ) : ℂ) * z ^ (-(1 / 2) : ℂ)) *
      ((z / 3) ^ (1 / 2 : ℂ) / π * K) =
      (z / 3) ^ (1 / 2 : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) * z ^ (-(1 / 2) : ℂ) * K by
    field_simp, hR, hPQ, one_mul]

/-- `K_{±2/3}(ζ) = -(π√3/z) Ai'(z)` with `ζ = (2/3) z^{3/2}` on the logarithmic plane, for
`z ≠ 0` (DLMF 9.6.16). -/
@[dlmf 9.6.E16]
theorem besselK_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselKOnLog (ε * (2 / 3)) (airyLogZeta z) = (-π * Real.sqrt 3 / z) * airyAiDeriv z := by
  have hA := airyAiDeriv_eq_besselK_complex hz hε
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hA]
  field_simp

/-- `H⁽¹⁾_{1/3}(ζ) = e^{-πi/6} √(3/z) (Ai(-z) - i Bi(-z))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.17). The DLMF factor `√(3/z)` is written
`√3 z^{-1/2}`, which agrees with the logarithmic left side also on the negative real axis
(corrected 2026-10-20). -/
@[dlmf 9.6.E17]
theorem hankel1_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel1OnLog (1 / 3) (airyLogZeta z) = exp (-π * I / 6) *
        (Real.sqrt 3 * z ^ (-(1 / 2) : ℂ)) *
      (airyAi (-z) - I * airyBi (-z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [airyAi_neg_eq_besselJ_complex hz, show (-1 / 3 : ℂ) = -(1 / 3) by ring]
  rw [airyBi_neg_eq_besselJ_complex hz]
  simp only [airyHankel1OnLog, airyBesselYOnLog]
  rw [exp_neg_pi_I_sixth (x := (-π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_one_third, sin_pi_mul_third_eq]
  rw [← hR] at hPQ ⊢
  rw [eq_inv_of_mul_eq_one_right hPQ]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `H¹_ν = e^{-iπν} H¹_{-ν}` on the logarithmic plane, for `sin(πν) ≠ 0`. -/
lemma airyHankel1OnLog_neg_order {ν : ℂ} (hs : sin (π * ν) ≠ 0) (w : ℂ) :
    airyHankel1OnLog ν w = exp (-ν * π * I) * airyHankel1OnLog (-ν) w := by
  simp only [airyHankel1OnLog, airyBesselYOnLog, mul_neg, Complex.cos_neg, Complex.sin_neg,
    neg_neg]
  rw [show -ν * π * I = (-(π * ν)) * I by ring, exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  have h1 := sin_sq_add_cos_sq (π * ν)
  field_simp
  linear_combination (I * airyBesselJOnLog (-ν) w) * h1 -
    (sin (π * ν) * (cos (π * ν) * airyBesselJOnLog (-ν) w - airyBesselJOnLog ν w)) * I_sq

/-- `H²_ν = e^{iπν} H²_{-ν}` on the logarithmic plane, for `sin(πν) ≠ 0`. -/
lemma airyHankel2OnLog_neg_order {ν : ℂ} (hs : sin (π * ν) ≠ 0) (w : ℂ) :
    airyHankel2OnLog ν w = exp (ν * π * I) * airyHankel2OnLog (-ν) w := by
  simp only [airyHankel2OnLog, airyBesselYOnLog, mul_neg, Complex.cos_neg, Complex.sin_neg,
    neg_neg]
  rw [show ν * π * I = (π * ν) * I by ring, exp_mul_I]
  have h1 := sin_sq_add_cos_sq (π * ν)
  field_simp
  linear_combination (-I * airyBesselJOnLog (-ν) w) * h1 -
    (sin (π * ν) * (cos (π * ν) * airyBesselJOnLog (-ν) w - airyBesselJOnLog ν w)) * I_sq

/-- `sin(π/3) ≠ 0`. -/
theorem sin_pi_mul_third_ne_zero : sin (π * (1 / 3)) ≠ 0 := by
  rw [show (π * (1 / 3) : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_div_three, ofReal_ne_zero]
  positivity

/-- `sin(2π/3) ≠ 0`. -/
theorem sin_pi_mul_two_thirds_ne_zero : sin (π * (2 / 3)) ≠ 0 := by
  rw [show (π * (2 / 3) : ℂ) = ((π - π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_sub, Real.sin_pi_div_three, ofReal_ne_zero]
  positivity

/-- `H⁽¹⁾_{1/3}(w) = e^{-πi/3} H⁽¹⁾_{-1/3}(w)` on the logarithmic plane (DLMF 9.6.17). -/
@[dlmf 9.6.E17]
theorem hankel1_third_neg_order (w : ℂ) :
    airyHankel1OnLog (1 / 3) w = exp (-(1 / 3) * π * I) * airyHankel1OnLog (-(1 / 3)) w := by
  exact airyHankel1OnLog_neg_order sin_pi_mul_third_ne_zero w

/-- `H⁽¹⁾_{2/3}(ζ) = e^{πi/6} (√3/z) (Ai'(-z) - i Bi'(-z))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.18). -/
@[dlmf 9.6.E18]
theorem hankel1_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel1OnLog (2 / 3) (airyLogZeta z) = exp (π * I / 6) * (Real.sqrt 3 / z) *
      (airyAiDeriv (-z) - I * airyBiDeriv (-z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [airyAiDeriv_neg_eq_besselJ_complex hz, show (-2 / 3 : ℂ) = -(2 / 3) by ring]
  rw [airyBiDeriv_neg_eq_besselJ_complex hz]
  simp only [airyHankel1OnLog, airyBesselYOnLog]
  rw [exp_pi_I_sixth (x := (π * I / 6 : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_two_thirds, sin_pi_mul_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `H⁽¹⁾_{2/3}(w) = e^{-2πi/3} H⁽¹⁾_{-2/3}(w)` on the logarithmic plane (DLMF 9.6.18). -/
@[dlmf 9.6.E18]
theorem hankel1_two_thirds_neg_order (w : ℂ) :
    airyHankel1OnLog (2 / 3) w = exp (-(2 / 3) * π * I) * airyHankel1OnLog (-(2 / 3)) w := by
  exact airyHankel1OnLog_neg_order sin_pi_mul_two_thirds_ne_zero w

/-- `H⁽²⁾_{1/3}(ζ) = e^{πi/6} √(3/z) (Ai(-z) + i Bi(-z))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.19). The DLMF factor `√(3/z)` is written
`√3 z^{-1/2}`, which agrees with the logarithmic left side also on the negative real axis
(corrected 2026-10-20). -/
@[dlmf 9.6.E19]
theorem hankel2_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel2OnLog (1 / 3) (airyLogZeta z) = exp (-(-π * I / 6)) *
        (Real.sqrt 3 * z ^ (-(1 / 2) : ℂ)) *
      (airyAi (-z) + I * airyBi (-z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [airyAi_neg_eq_besselJ_complex hz, show (-1 / 3 : ℂ) = -(1 / 3) by ring]
  rw [airyBi_neg_eq_besselJ_complex hz]
  simp only [airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_pi_I_sixth (x := (-(-π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_one_third, sin_pi_mul_third_eq]
  rw [← hR] at hPQ ⊢
  rw [eq_inv_of_mul_eq_one_right hPQ]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `H⁽²⁾_{1/3}(w) = e^{πi/3} H⁽²⁾_{-1/3}(w)` on the logarithmic plane (DLMF 9.6.19). -/
@[dlmf 9.6.E19]
theorem hankel2_third_neg_order (w : ℂ) :
    airyHankel2OnLog (1 / 3) w = exp ((1 / 3) * π * I) * airyHankel2OnLog (-(1 / 3)) w := by
  exact airyHankel2OnLog_neg_order sin_pi_mul_third_ne_zero w

/-- `H⁽²⁾_{2/3}(ζ) = e^{-πi/6} (√3/z) (Ai'(-z) + i Bi'(-z))` with `ζ = (2/3) z^{3/2}` on the
logarithmic plane, for `z ≠ 0` (DLMF 9.6.20). -/
@[dlmf 9.6.E20]
theorem hankel2_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel2OnLog (2 / 3) (airyLogZeta z) = exp (-(π * I / 6)) * (Real.sqrt 3 / z) *
      (airyAiDeriv (-z) + I * airyBiDeriv (-z)) := by
  have hR := half_cpow_div_three_mul_sqrt hz
  have hPQ := half_cpow_mul_neg_half hz
  have hR0 : (z / 3) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz (by simpa using h.1)
  have hs0 := sqrt_three_ne_zero_complex
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [airyAiDeriv_neg_eq_besselJ_complex hz, show (-2 / 3 : ℂ) = -(2 / 3) by ring]
  rw [airyBiDeriv_neg_eq_besselJ_complex hz]
  simp only [airyHankel2OnLog, airyBesselYOnLog]
  rw [exp_neg_pi_I_sixth (x := (-(π * I / 6) : ℂ)) (by push_cast; ring)]
  rw [cos_pi_mul_two_thirds, sin_pi_mul_two_thirds_eq]
  field_simp
  ring_nf
  simp only [I_sq, sqrt_three_sq, sqrt_three_pow_three_complex]
  ring_nf

/-- `H⁽²⁾_{2/3}(w) = e^{2πi/3} H⁽²⁾_{-2/3}(w)` on the logarithmic plane (DLMF 9.6.20). -/
@[dlmf 9.6.E20]
theorem hankel2_two_thirds_neg_order (w : ℂ) :
    airyHankel2OnLog (2 / 3) w = exp ((2 / 3) * π * I) * airyHankel2OnLog (-(2 / 3)) w := by
  exact airyHankel2OnLog_neg_order sin_pi_mul_two_thirds_ne_zero w

/-- `(2ζ)²/16 = z³/9`. -/
theorem two_airyZetaComplex_sq_div (z : ℂ) : (2 * airyZetaComplex z) ^ 2 / 16 = z ^ 3 / 9 := by
  rw [airyZetaComplex, mul_pow, mul_pow, ← cpow_nat_mul,
    show ((2 : ℕ) : ℂ) * (3 / 2) = ((3 : ℕ) : ℂ) by norm_num, cpow_natCast]
  ring

/-- `exp (c L) = exp (c log(2/3) + (3c/2) log z)`. -/
theorem exp_mul_airyLogZeta (c z : ℂ) :
    exp (c * airyLogZeta z) = exp (c * (log 2 - log 3)) * exp (3 / 2 * c * log z) := by
  rw [airyLogZeta, log_two_thirds, ← exp_add]; congr 1; ring

/-- Kummer's second transformation at `M(a, 2a, w)` with `a = ν + 1/2`. -/
theorem kummerM_two_mul_eq {ν a b c : ℂ} (ha : ν + 1 / 2 = a) (hb : 2 * ν + 1 = b) (hc : ν + 1 = c)
    (hν : ∀ k : ℕ, ν + 1 ≠ -k) (h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k) (w : ℂ) :
    kummerM a b w = Gamma c * exp (w / 2) * regularizedHGFun (∅ : Multiset ℂ) {c} (w ^ 2 / 16) := by
  subst ha hb hc
  exact DLMF.Bessel.kummerM_eq_exp_mul_regularized0F1 hν h2ν w

/-- `Γ(4/3) = Γ(1/3)/3`. -/
theorem Gamma_four_thirds : Gamma (4 / 3) = 1 / 3 * Gamma (1 / 3) := by
  rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- `Γ(5/3) = (2/3)Γ(2/3)`. -/
theorem Gamma_five_thirds : Gamma (5 / 3) = 2 / 3 * Gamma (2 / 3) := by
  rw [show (5 / 3 : ℂ) = 2 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- Complex powers of `2` and `3` as exponentials. -/
theorem cpow_two_three (a : ℂ) : (2 : ℂ) ^ a = exp (a * log 2) ∧ (3 : ℂ) ^ a = exp (a * log 3) := by
  rw [cpow_def_of_ne_zero (by norm_num), cpow_def_of_ne_zero (by norm_num)]
  exact ⟨by ring_nf, by ring_nf⟩

/-- `Γ(4/3) = e^{-log 3} Γ(1/3)`. -/
theorem Gamma_four_thirds_exp : Gamma (4 / 3) = exp (-log 3) * Gamma (1 / 3) := by
  rw [Gamma_four_thirds, exp_neg, exp_log (by norm_num)]; ring

/-- `Γ(5/3) = 2 e^{-log 3} Γ(2/3)`. -/
theorem Gamma_five_thirds_exp : Gamma (5 / 3) = 2 * exp (-log 3) * Gamma (2 / 3) := by
  rw [Gamma_five_thirds, exp_neg, exp_log (by norm_num)]; ring

/-- `e^{-ζ} e^{2ζ/2} = 1`. -/
theorem exp_neg_mul_exp_two_div (ζ : ℂ) : exp (-ζ) * exp (2 * ζ / 2) = 1 := by
  rw [← exp_add, show -ζ + 2 * ζ / 2 = 0 by ring, exp_zero]

/-- `Γ(5/3) = e^{log 2 - log 3} Γ(2/3)`. -/
theorem Gamma_five_thirds_exp' : Gamma (5 / 3) = exp (log 2 - log 3) * Gamma (2 / 3) := by
  rw [Gamma_five_thirds, exp_sub, exp_log (by norm_num), exp_log (by norm_num)]

/-- `-1/3` is not a nonpositive integer. -/
theorem neg_one_third_ne_neg_nat : ∀ k : ℕ, (-1 / 3 : ℂ) ≠ -k := by
  intro k h
  have := congrArg re h
  simp at this
  rcases k with _ | k
  · norm_num at this
  · push_cast at this; linarith [k.cast_nonneg (α := ℝ)]

/-- `Bi(z)` as a combination of `e^{-ζ} M(1/6, 1/3, 2ζ)` and `ζ^{2/3} e^{-ζ} M(5/6, 5/3, 2ζ)`,
`ζ = (2/3) z^{3/2}`, for `z ≠ 0` (DLMF 9.6.25). -/
@[dlmf 9.6.E25]
theorem airyBi_eq_kummerM {z : ℂ} (hz : z ≠ 0) :
    airyBi z = (1 / ((3 : ℂ) ^ (1 / 6 : ℂ) * Gamma (2 / 3))) * exp (-airyZetaComplex z) *
        kummerM (1 / 6) (1 / 3) (2 * airyZetaComplex z) +
      ((3 : ℂ) ^ (5 / 6 : ℂ) / ((2 : ℂ) ^ (2 / 3 : ℂ) * Gamma (1 / 3))) *
          exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerM (5 / 6) (5 / 3) (2 * airyZetaComplex z) := by
  rw [kummerM_two_mul_eq (ν := -1 / 3) (c := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
      (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
          (Hypergeometric.not_neg_nat_of_re_pos (by norm_num)),
    kummerM_two_mul_eq (ν := 1 / 3) (c := 4 / 3) (by norm_num) (by norm_num) (by norm_num)
      (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
          (Hypergeometric.not_neg_nat_of_re_pos (by norm_num)),
    two_airyZetaComplex_sq_div, sub_eq_add_neg, exp_add, exp_mul_airyLogZeta]
  have ez : exp (3 / 2 * (2 / 3) * log z) = z := by
    rw [show (3 / 2 * (2 / 3) * log z) = log z by ring, exp_log hz]
  rw [ez]
  have hΓ1 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ2 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hF : 1 / ((3 : ℂ) ^ (1 / 6 : ℂ) * Gamma (2 / 3)) * Gamma (2 / 3) =
      ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [(cpow_two_three _).2, three_rpow_eq_exp, sqrt_three_eq_exp]
    field_simp
    simp only [← exp_add]; conv_lhs => rw [← exp_zero]
    congr 1; push_cast; ring
  have hG : (3 : ℂ) ^ (5 / 6 : ℂ) / ((2 : ℂ) ^ (2 / 3 : ℂ) * Gamma (1 / 3)) *
      exp (2 / 3 * (log 2 - log 3)) * Gamma (4 / 3) =
      ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [(cpow_two_three _).2, (cpow_two_three _).1, three_rpow_eq_exp, sqrt_three_eq_exp,
      Gamma_four_thirds_exp]
    field_simp
    simp only [← exp_add]
    congr 1; push_cast; ring
  have hζ := exp_neg_mul_exp_two_div (airyZetaComplex z)
  simp only [airyBi, airyF, airyG]
  set F := regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (z ^ 3 / 9)
  set G := regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (z ^ 3 / 9)
  linear_combination (-F) * hF + (-(z * G)) * hG -
    (1 / ((3 : ℂ) ^ (1 / 6 : ℂ) * Gamma (2 / 3)) * Gamma (2 / 3) * F +
      (3 : ℂ) ^ (5 / 6 : ℂ) / ((2 : ℂ) ^ (2 / 3 : ℂ) * Gamma (1 / 3)) *
        exp (2 / 3 * (log 2 - log 3)) * Gamma (4 / 3) * z * G) * hζ

/-- `Bi'(z)` as a combination of `e^{-ζ} M(-1/6, -1/3, 2ζ)` and `ζ^{4/3} e^{-ζ} M(7/6, 7/3, 2ζ)`,
`ζ = (2/3) z^{3/2}`, for `z ≠ 0` (DLMF 9.6.26). -/
@[dlmf 9.6.E26]
theorem airyBiDeriv_eq_kummerM {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = ((3 : ℂ) ^ (1 / 6 : ℂ) / Gamma (1 / 3)) * exp (-airyZetaComplex z) *
        kummerM (-1 / 6) (-1 / 3) (2 * airyZetaComplex z) +
      ((3 : ℂ) ^ (7 / 6 : ℂ) / ((2 : ℂ) ^ (7 / 3 : ℂ) * Gamma (2 / 3))) *
          exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerM (7 / 6) (7 / 3) (2 * airyZetaComplex z) := by
  rw [kummerM_two_mul_eq (ν := -2 / 3) (c := 1 / 3) (by norm_num) (by norm_num) (by norm_num)
      (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
          (by convert neg_one_third_ne_neg_nat using 2; norm_num),
    kummerM_two_mul_eq (ν := 2 / 3) (c := 5 / 3) (by norm_num) (by norm_num) (by norm_num)
      (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
          (Hypergeometric.not_neg_nat_of_re_pos (by norm_num)),
    two_airyZetaComplex_sq_div, sub_eq_add_neg, exp_add, exp_mul_airyLogZeta]
  have ez : exp (3 / 2 * (4 / 3) * log z) = z ^ 2 := by
    rw [show (3 / 2 * (4 / 3) * log z) = ((2 : ℕ) : ℂ) * log z by push_cast; ring, exp_nat_mul,
      exp_log hz]
  rw [ez]
  have hΓ1 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ2 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hF : (3 : ℂ) ^ (1 / 6 : ℂ) / Gamma (1 / 3) * Gamma (1 / 3) =
      ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * exp (log 3) := by
    rw [(cpow_two_three _).2, three_rpow_eq_exp, sqrt_three_eq_exp]
    field_simp
    simp only [← exp_add]
    congr 1; push_cast; ring
  have hG : (3 : ℂ) ^ (7 / 6 : ℂ) / ((2 : ℂ) ^ (7 / 3 : ℂ) * Gamma (2 / 3)) *
      exp (4 / 3 * (log 2 - log 3)) * Gamma (5 / 3) =
      ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * exp (-log 3) := by
    rw [(cpow_two_three _).2, (cpow_two_three _).1, three_rpow_eq_exp, sqrt_three_eq_exp,
      Gamma_five_thirds_exp']
    field_simp
    simp only [← exp_add]
    congr 1; push_cast; ring
  rw [exp_log (by norm_num)] at hF
  rw [exp_neg, exp_log (by norm_num)] at hG
  have hζ := exp_neg_mul_exp_two_div (airyZetaComplex z)
  have hC := reg0F1_one_third (z ^ 3 / 9)
  simp only [airyBiDeriv, airyFDeriv, airyGDeriv]
  set R13 := regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (z ^ 3 / 9)
  set R53 := regularizedHGFun (∅ : Multiset ℂ) {5 / 3} (z ^ 3 / 9)
  linear_combination (-R13) * hF + (-(z ^ 2 * R53)) * hG -
    ((3 : ℂ) ^ (1 / 6 : ℂ) / Gamma (1 / 3) * Gamma (1 / 3) * R13 +
      (3 : ℂ) ^ (7 / 6 : ℂ) / ((2 : ℂ) ^ (7 / 3 : ℂ) * Gamma (2 / 3)) *
        exp (4 / 3 * (log 2 - log 3)) * Gamma (5 / 3) * z ^ 2 * R53) * hζ
    -3 * ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * hC

/-- Whittaker M on the logarithmic argument plane. -/
def airyWhittakerMOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2 + (μ + 1 / 2) * w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) (exp w)
/-- Whittaker W on the logarithmic plane at nonintegral second Kummer parameter. -/
def airyWhittakerWOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2 + (μ + 1 / 2) * w) * kummerUOnLog (μ - κ + 1 / 2) (1 + 2 * μ) w

/-- `e^{log 2 + L} = 2ζ`. -/
theorem exp_log_two_add_airyLogZeta {z : ℂ} (hz : z ≠ 0) :
    exp (log 2 + airyLogZeta z) = 2 * airyZetaComplex z := by
  rw [airyLogZeta, airyZetaComplex, cpow_def_of_ne_zero hz, exp_add, exp_add,
    exp_log (by norm_num), exp_log (by norm_num)]
  ring_nf

/-- The imaginary part of `log 2 + L` is `(3/2) arg z`. -/
theorem im_log_two_add_airyLogZeta (z : ℂ) : (log 2 + airyLogZeta z).im = 3 / 2 * arg z := by
  rw [airyLogZeta, log_two_thirds]
  simp only [add_im, sub_im, mul_im, log_im]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
    arg_ofReal_of_nonneg (by norm_num), arg_ofReal_of_nonneg (by norm_num)]
  norm_num

/-- In the sector `|arg z| < 2π/3`, `log (2ζ) = log 2 + L`. -/
theorem log_two_airyZeta_bounds {z : ℂ} (hz : |arg z| < 2 * π / 3) :
    -π < (log 2 + airyLogZeta z).im ∧ (log 2 + airyLogZeta z).im ≤ π := by
  rw [im_log_two_add_airyLogZeta]
  have := abs_lt.mp hz
  constructor <;> linarith

/-- Whittaker `M` at `e^w` with `w` in the principal strip is its logarithmic-plane form. -/
theorem whittakerM_exp_eq_onLog (κ μ : ℂ) {w : ℂ} (h1 : -π < w.im) (h2 : w.im ≤ π) :
    whittakerM κ μ (exp w) = airyWhittakerMOnLog κ μ w := by
  rw [whittakerM, airyWhittakerMOnLog, cpow_def_of_ne_zero (exp_ne_zero w), log_exp h1 h2,
    neg_div, ← exp_add]
  ring_nf

/-- `Γ(1/3) Γ(2/3) √3 = 2π`. -/
theorem Gamma_one_third_mul_two_thirds :
    Gamma (1 / 3) * Gamma (2 / 3) * (Real.sqrt 3 : ℂ) = 2 * π := by
  have h := Gamma_mul_Gamma_one_sub (1 / 3 : ℂ)
  rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num, show (π : ℂ) * (1 / 3) = ((π / 3 : ℝ) : ℂ) by
    push_cast; ring, ← ofReal_sin, Real.sin_pi_div_three] at h
  rw [h]
  have : (Real.sqrt 3 : ℂ) ≠ 0 :=
      by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
  push_cast
  field_simp

/-- Legendre duplication at `1/3`: `Γ(1/3) Γ(5/6) = Γ(2/3) 2^{1/3} √π`. -/
theorem Gamma_one_third_mul_five_sixths :
    Gamma (1 / 3) * Gamma (5 / 6) = Gamma (2 / 3) * (2 : ℂ) ^ (1 / 3 : ℂ) * (Real.sqrt π : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_add_half (1 / 3)
  rw [show (1 / 3 : ℂ) + 1 / 2 = 5 / 6 by norm_num, show (2 : ℂ) * (1 / 3) = 2 / 3 by norm_num,
    show (1 : ℂ) - 2 / 3 = 1 / 3 by norm_num] at h
  exact h

/-- Legendre duplication at `1/6`: `Γ(1/6) Γ(2/3) = Γ(1/3) 2^{2/3} √π`. -/
theorem Gamma_one_sixth_mul_two_thirds :
    Gamma (1 / 6) * Gamma (2 / 3) = Gamma (1 / 3) * (2 : ℂ) ^ (2 / 3 : ℂ) * (Real.sqrt π : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_add_half (1 / 6)
  rw [show (1 / 6 : ℂ) + 1 / 2 = 2 / 3 by norm_num, show (2 : ℂ) * (1 / 6) = 1 / 3 by norm_num,
    show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num] at h
  exact h

/-- `2^{1/3} 2^{2/3} = 2`. -/
theorem two_cpow_third_mul : (2 : ℂ) ^ (1 / 3 : ℂ) * (2 : ℂ) ^ (2 / 3 : ℂ) = 2 := by
  rw [← cpow_add _ _ (by norm_num)]; norm_num

/-- `Γ(2/3)² √3 = 2^{2/3} √π Γ(5/6)`. -/
theorem Gamma_two_thirds_sq :
    Gamma (2 / 3) * Gamma (2 / 3) * (Real.sqrt 3 : ℂ) =
      (2 : ℂ) ^ (2 / 3 : ℂ) * (Real.sqrt π : ℂ) * Gamma (5 / 6) := by
  have G1 := Gamma_one_third_mul_two_thirds
  have G2 := Gamma_one_third_mul_five_sixths
  have h2 := two_cpow_third_mul
  have hp := Complex.ofReal_sqrt_pi_mul_self
  have hΓ : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have ha : (2 : ℂ) ^ (1 / 3 : ℂ) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hΓ ha) hsp)
  linear_combination ((2 : ℂ) ^ (1 / 3 : ℂ) * (Real.sqrt π : ℂ) * Gamma (2 / 3)) * G1 -
    (Gamma (1 / 3) * Gamma (5 / 6) * (2 : ℂ) ^ (1 / 3 : ℂ) * (2 : ℂ) ^ (2 / 3 : ℂ)) * hp -
    (π * Gamma (1 / 3) * Gamma (5 / 6)) * h2 - 2 * π * G2

/-- `Γ(1/3)² √3 = 2^{1/3} √π Γ(1/6)`. -/
theorem Gamma_one_third_sq :
    Gamma (1 / 3) * Gamma (1 / 3) * (Real.sqrt 3 : ℂ) =
      (2 : ℂ) ^ (1 / 3 : ℂ) * (Real.sqrt π : ℂ) * Gamma (1 / 6) := by
  have G1 := Gamma_one_third_mul_two_thirds
  have G3 := Gamma_one_sixth_mul_two_thirds
  have h2 := two_cpow_third_mul
  have hp := Complex.ofReal_sqrt_pi_mul_self
  have hΓ : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hb : (2 : ℂ) ^ (2 / 3 : ℂ) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hΓ hb) hsp)
  linear_combination ((2 : ℂ) ^ (2 / 3 : ℂ) * (Real.sqrt π : ℂ) * Gamma (1 / 3)) * G1 -
    (Gamma (1 / 6) * Gamma (2 / 3) * (2 : ℂ) ^ (1 / 3 : ℂ) * (2 : ℂ) ^ (2 / 3 : ℂ)) * hp -
    (π * Gamma (1 / 6) * Gamma (2 / 3)) * h2 - 2 * π * G3

/-- `Γ(-2/3) = -(3/2) Γ(1/3)`. -/
theorem Gamma_neg_two_thirds : Gamma (-2 / 3) = -(3 / 2) * Gamma (1 / 3) := by
  have h := Complex.Gamma_add_one (-2 / 3 : ℂ) (by norm_num)
  rw [show (-2 / 3 : ℂ) + 1 = 1 / 3 by norm_num] at h
  rw [h]; ring

/-- Tricomi's `U` on the logarithmic plane, unfolded at `(5/6, 5/3)`. -/
theorem kummerUOnLog_five_sixths (w : ℂ) :
    kummerUOnLog (5 / 6) (5 / 3) w = Gamma (-2 / 3) / Gamma (1 / 6) *
        kummerM (5 / 6) (5 / 3) (exp w) +
      Gamma (2 / 3) / Gamma (5 / 6) * exp (-2 / 3 * w) * kummerM (1 / 6) (1 / 3) (exp w) := by
  rw [kummerUOnLog]; norm_num

/-- `Ai(z) = 3^{-1/6} π^{-1/2} ζ^{2/3} e^{-ζ} U(5/6, 5/3, 2ζ)` for `z ≠ 0`, with `U` continued
on the logarithmic plane of `2ζ` (DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_kummerU_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAi z = ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π) *
      exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerUOnLog (5 / 6) (5 / 3) (log 2 + airyLogZeta z) := by
  have k1 := kummerM_two_mul_eq (ν := -1 / 3) (a := 1 / 6) (b := 1 / 3) (c := 2 / 3) (by norm_num)
    (by norm_num) (by norm_num) (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
    (Hypergeometric.not_neg_nat_of_re_pos (by norm_num)) (2 * airyZetaComplex z)
  have k2 := kummerM_two_mul_eq (ν := 1 / 3) (a := 5 / 6) (b := 5 / 3) (c := 4 / 3) (by norm_num)
    (by norm_num) (by norm_num) (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
    (Hypergeometric.not_neg_nat_of_re_pos (by norm_num)) (2 * airyZetaComplex z)
  rw [kummerUOnLog_five_sixths, exp_log_two_add_airyLogZeta hz, k1, k2,
    two_airyZetaComplex_sq_div, sub_eq_add_neg, exp_add, exp_mul_airyLogZeta]
  have ez : exp (3 / 2 * (2 / 3) * log z) = z := by
    rw [show (3 / 2 * (2 / 3) * log z) = log z by ring, exp_log hz]
  rw [ez]
  have hΓ1 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ2 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ5 : Gamma (5 / 6) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ6 : Gamma (1 / 6) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
  have hw : exp (2 / 3 * (log 2 - log 3)) * z * exp (-2 / 3 * (log 2 + airyLogZeta z)) =
      exp (-2 / 3 * log 2) := by
    rw [show exp (2 / 3 * (log 2 - log 3)) * z = exp (2 / 3 * (log 2 - log 3)) * exp (log z) by
      rw [exp_log hz], airyLogZeta, log_two_thirds]
    simp only [← exp_add]; congr 1; ring
  have hq1 : Gamma (2 / 3) / Gamma (5 / 6) * Gamma (2 / 3) =
      (2 : ℂ) ^ (2 / 3 : ℂ) * (Real.sqrt π : ℂ) / (Real.sqrt 3 : ℂ) := by
    field_simp; linear_combination Gamma_two_thirds_sq
  have hA : (3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π * exp (-2 / 3 * log 2) *
      (Gamma (2 / 3) / Gamma (5 / 6) * Gamma (2 / 3)) = (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [hq1, (cpow_two_three _).1, (cpow_two_three _).2, three_rpow_eq_exp, sqrt_three_eq_exp]
    field_simp
    simp only [← exp_add]; congr 1; push_cast; ring
  have hq2 : Gamma (-2 / 3) / Gamma (1 / 6) * Gamma (4 / 3) =
      -((2 : ℂ) ^ (1 / 3 : ℂ) * (Real.sqrt π : ℂ) / ((Real.sqrt 3 : ℂ) * exp (log 2))) := by
    rw [Gamma_neg_two_thirds, Gamma_four_thirds, exp_log (by norm_num)]
    field_simp; linear_combination (-1 : ℂ) * Gamma_one_third_sq
  have hB : (3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π * exp (2 / 3 * (log 2 - log 3)) *
      (Gamma (-2 / 3) / Gamma (1 / 6) * Gamma (4 / 3)) = -(((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [hq2, (cpow_two_three _).1, (cpow_two_three _).2, three_rpow_eq_exp, sqrt_three_eq_exp]
    field_simp
    simp only [← exp_add]; congr 1; push_cast; ring
  have hζ := exp_neg_mul_exp_two_div (airyZetaComplex z)
  simp only [airyAi, airyF, airyG]
  set R23 := regularizedHGFun (∅ : Multiset ℂ) {2 / 3} (z ^ 3 / 9)
  set R43 := regularizedHGFun (∅ : Multiset ℂ) {4 / 3} (z ^ 3 / 9)
  set K := (3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π
  set E := exp (2 / 3 * (log 2 - log 3))
  set W := exp (-2 / 3 * (log 2 + airyLogZeta z))
  set c1 := Gamma (-2 / 3) / Gamma (1 / 6)
  set c2 := Gamma (2 / 3) / Gamma (5 / 6)
  linear_combination
      -(K * E * c1 * Gamma (4 / 3) * z * R43 + K * E * z * W * c2 * Gamma (2 / 3) * R23) * hζ -
    R23 * hA - K * c2 * Gamma (2 / 3) * R23 * hw - z * R43 * hB

/-- `Γ(-4/3) = (9/4) Γ(2/3)`. -/
theorem Gamma_neg_four_thirds : Gamma (-4 / 3) = 9 / 4 * Gamma (2 / 3) := by
  have h1 := Complex.Gamma_add_one (-4 / 3 : ℂ) (by norm_num)
  have h2 := Complex.Gamma_add_one (-1 / 3 : ℂ) (by norm_num)
  rw [show (-4 / 3 : ℂ) + 1 = -1 / 3 by norm_num] at h1
  rw [show (-1 / 3 : ℂ) + 1 = 2 / 3 by norm_num, h1] at h2
  rw [h2]; ring

/-- `Γ(-1/6) = -6 Γ(5/6)`. -/
theorem Gamma_neg_one_sixth : Gamma (-1 / 6) = -6 * Gamma (5 / 6) := by
  have h := Complex.Gamma_add_one (-1 / 6 : ℂ) (by norm_num)
  rw [show (-1 / 6 : ℂ) + 1 = 5 / 6 by norm_num] at h
  rw [h]; ring

/-- `Γ(7/6) = Γ(1/6)/6`. -/
theorem Gamma_seven_sixths : Gamma (7 / 6) = 1 / 6 * Gamma (1 / 6) := by
  rw [show (7 / 6 : ℂ) = 1 / 6 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- Tricomi's `U` on the logarithmic plane, unfolded at `(7/6, 7/3)`. -/
theorem kummerUOnLog_seven_sixths (w : ℂ) :
    kummerUOnLog (7 / 6) (7 / 3) w = Gamma (-4 / 3) / Gamma (-1 / 6) *
        kummerM (7 / 6) (7 / 3) (exp w) +
      Gamma (4 / 3) / Gamma (7 / 6) * exp (-4 / 3 * w) * kummerM (-1 / 6) (-1 / 3) (exp w) := by
  rw [kummerUOnLog]; norm_num

/-- `Ai'(z) = -3^{1/6} π^{-1/2} ζ^{4/3} e^{-ζ} U(7/6, 7/3, 2ζ)` for `z ≠ 0`, with `U` continued
on the logarithmic plane of `2ζ` (DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_kummerU_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = -((3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π) *
      exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerUOnLog (7 / 6) (7 / 3) (log 2 + airyLogZeta z) := by
  have k1 := kummerM_two_mul_eq (ν := -2 / 3) (a := -1 / 6) (b := -1 / 3) (c := 1 / 3) (by norm_num)
    (by norm_num) (by norm_num) (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
    (by convert neg_one_third_ne_neg_nat using 2; norm_num) (2 * airyZetaComplex z)
  have k2 := kummerM_two_mul_eq (ν := 2 / 3) (a := 7 / 6) (b := 7 / 3) (c := 5 / 3) (by norm_num)
    (by norm_num) (by norm_num) (Hypergeometric.not_neg_nat_of_re_pos (by norm_num))
    (Hypergeometric.not_neg_nat_of_re_pos (by norm_num)) (2 * airyZetaComplex z)
  rw [kummerUOnLog_seven_sixths, exp_log_two_add_airyLogZeta hz, k1, k2,
    two_airyZetaComplex_sq_div, sub_eq_add_neg, exp_add, exp_mul_airyLogZeta]
  have ez : exp (3 / 2 * (4 / 3) * log z) = z ^ 2 := by
    rw [show (3 / 2 * (4 / 3) * log z) = ((2 : ℕ) : ℂ) * log z by push_cast; ring, exp_nat_mul,
      exp_log hz]
  rw [ez]
  have hΓ1 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ2 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ5 : Gamma (5 / 6) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ6 : Gamma (1 / 6) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
  have hw : exp (4 / 3 * (log 2 - log 3)) * z ^ 2 * exp (-4 / 3 * (log 2 + airyLogZeta z)) =
      exp (-4 / 3 * log 2) := by
    rw [show exp (4 / 3 * (log 2 - log 3)) * z ^ 2 =
        exp (4 / 3 * (log 2 - log 3)) * exp (2 * log z) by
      rw [show (2 : ℂ) * log z = ((2 : ℕ) : ℂ) * log z by norm_num, exp_nat_mul, exp_log hz],
      airyLogZeta, log_two_thirds]
    simp only [← exp_add]; congr 1; ring
  have hq1 : Gamma (4 / 3) / Gamma (7 / 6) * Gamma (1 / 3) =
      exp (log 2) * ((2 : ℂ) ^ (1 / 3 : ℂ) * (Real.sqrt π : ℂ) / (Real.sqrt 3 : ℂ)) := by
    rw [Gamma_four_thirds, Gamma_seven_sixths, exp_log (by norm_num)]
    field_simp; linear_combination (6 : ℂ) * Gamma_one_third_sq
  have hA : (3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π * exp (-4 / 3 * log 2) *
      (Gamma (4 / 3) / Gamma (7 / 6) * Gamma (1 / 3)) =
        exp (log 3) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [hq1, (cpow_two_three _).1, (cpow_two_three _).2, three_rpow_eq_exp, sqrt_three_eq_exp]
    field_simp
    simp only [← exp_add]; congr 1; push_cast; ring
  have hq2 : Gamma (-4 / 3) / Gamma (-1 / 6) * Gamma (5 / 3) =
      -((2 : ℂ) ^ (2 / 3 : ℂ) * (Real.sqrt π : ℂ) / ((Real.sqrt 3 : ℂ) * exp (2 * log 2))) := by
    rw [Gamma_neg_four_thirds, Gamma_neg_one_sixth, Gamma_five_thirds,
      show (2 : ℂ) * log 2 = ((2 : ℕ) : ℂ) * log 2 by norm_num, exp_nat_mul, exp_log (by norm_num)]
    field_simp; linear_combination (-72 : ℂ) * Gamma_two_thirds_sq
  have hB : (3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π * exp (4 / 3 * (log 2 - log 3)) *
      (Gamma (-4 / 3) / Gamma (-1 / 6) * Gamma (5 / 3)) =
        -((((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * exp (-log 3)) := by
    rw [hq2, (cpow_two_three _).1, (cpow_two_three _).2, three_rpow_eq_exp, sqrt_three_eq_exp]
    field_simp
    simp only [← exp_add]; congr 1; push_cast; ring
  rw [exp_log (by norm_num)] at hA
  rw [exp_neg, exp_log (by norm_num)] at hB
  have hζ := exp_neg_mul_exp_two_div (airyZetaComplex z)
  have hC := reg0F1_one_third (z ^ 3 / 9)
  simp only [airyAiDeriv, airyFDeriv, airyGDeriv]
  set R13 := regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (z ^ 3 / 9)
  set R53 := regularizedHGFun (∅ : Multiset ℂ) {5 / 3} (z ^ 3 / 9)
  set K := (3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π
  set E := exp (4 / 3 * (log 2 - log 3))
  set W := exp (-4 / 3 * (log 2 + airyLogZeta z))
  set c1 := Gamma (-4 / 3) / Gamma (-1 / 6)
  set c2 := Gamma (4 / 3) / Gamma (7 / 6)
  linear_combination (K * E * c1 * Gamma (5 / 3) * z ^ 2 * R53 + K * c2 * Gamma (1 / 3) * R13 * E *
      z ^ 2 * W) * hζ + z ^ 2 * R53 * hB + R13 * hA + K * c2 * Gamma (1 / 3) * R13 * hw +
    3 * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * hC

/-- A rational `p/3` with `3 ∤ p` is not an integer. -/
theorem div_three_ne_int {p : ℤ} (hp : p % 3 ≠ 0) : ∀ k : ℤ, ((p : ℂ) / 3) ≠ k := by
  intro k h
  have h' : (p : ℂ) = 3 * k := by rw [← h]; ring
  have : p = 3 * k := by exact_mod_cast h'
  omega

/-- Tricomi's `U` at `e^w`, with `w` in the principal strip, is its logarithmic-plane form. -/
theorem kummerU_exp_eq_onLog (a : ℂ) {b : ℂ} (hb : ∀ k : ℤ, b ≠ k) {w : ℂ} (h1 : -π < w.im)
    (h2 : w.im ≤ π) : kummerU a b (exp w) = kummerUOnLog a b w := by
  rw [kummerU_eq_connection a b _ hb, kummerUConnection, kummerUOnLog,
    cpow_def_of_ne_zero (exp_ne_zero w), log_exp h1 h2, mul_comm w]

/-- Whittaker `W` at `e^w`, with `w` in the principal strip, is its logarithmic-plane form. -/
theorem whittakerW_exp_eq_onLog (κ μ : ℂ) (hb : ∀ k : ℤ, 1 + 2 * μ ≠ k) {w : ℂ}
    (h1 : -π < w.im) (h2 : w.im ≤ π) :
    whittakerW κ μ (exp w) = airyWhittakerWOnLog κ μ w := by
  rw [whittakerW, airyWhittakerWOnLog, kummerU_exp_eq_onLog _ hb h1 h2,
    cpow_def_of_ne_zero (exp_ne_zero w), log_exp h1 h2, neg_div, ← exp_add,
    show (1 / 2 + μ - κ) = μ - κ + 1 / 2 by ring]
  ring_nf

/-- The continued Whittaker representation without reducing the argument of ζ (DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_whittakerW_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAi z = (1 / (2 * Real.sqrt π)) * z ^ (-1 / 4 : ℂ) *
      airyWhittakerWOnLog 0 (1 / 3) (log 2 + airyLogZeta z) := by
  rw [airyAi_eq_kummerU_onLog hz, airyWhittakerWOnLog, exp_log_two_add_airyLogZeta hz,
    show (1 / 3 : ℂ) - 0 + 1 / 2 = 5 / 6 by norm_num,
    show (1 : ℂ) + 2 * (1 / 3) = 5 / 3 by norm_num]
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h : (3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π * exp (2 / 3 * airyLogZeta z - airyZetaComplex z) =
      1 / (exp (log 2) * Real.sqrt π) * z ^ (-1 / 4 : ℂ) *
        exp (-(2 * airyZetaComplex z) / 2 + (1 / 3 + 1 / 2) * (log 2 + airyLogZeta z)) := by
    rw [cpow_def_of_ne_zero hz, (cpow_two_three _).2, airyLogZeta, log_two_thirds]
    field_simp
    simp only [← exp_add]; congr 1; ring
  rw [exp_log (by norm_num)] at h
  rw [h]; ring

/-- The continued Whittaker representation without reducing the argument of ζ (DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_whittakerW_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = -(1 / (2 * Real.sqrt π)) * z ^ (1 / 4 : ℂ) *
      airyWhittakerWOnLog 0 (2 / 3) (log 2 + airyLogZeta z) := by
  rw [airyAiDeriv_eq_kummerU_onLog hz, airyWhittakerWOnLog, exp_log_two_add_airyLogZeta hz,
    show (2 / 3 : ℂ) - 0 + 1 / 2 = 7 / 6 by norm_num,
    show (1 : ℂ) + 2 * (2 / 3) = 7 / 3 by norm_num]
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h : (3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π * exp (4 / 3 * airyLogZeta z - airyZetaComplex z) =
      1 / (exp (log 2) * Real.sqrt π) * z ^ (1 / 4 : ℂ) *
        exp (-(2 * airyZetaComplex z) / 2 + (2 / 3 + 1 / 2) * (log 2 + airyLogZeta z)) := by
    rw [cpow_def_of_ne_zero hz, (cpow_two_three _).2, airyLogZeta, log_two_thirds]
    field_simp
    simp only [← exp_add]; congr 1; ring
  rw [exp_log (by norm_num)] at h
  rw [neg_mul, neg_mul, h]; ring

/-- The full logarithmic-plane Whittaker M representation (DLMF 9.6.23). -/
@[dlmf 9.6.E23]
theorem airyBi_eq_whittakerM_onLog {z : ℂ} (hz : z ≠ 0) :
    airyBi z = z ^ (-1 / 4 : ℂ) *
        (airyWhittakerMOnLog 0 (-1 / 3) (log 2 + airyLogZeta z) /
            ((2 : ℂ) ^ (1 / 3 : ℂ) * Gamma (2 / 3)) +
        3 * airyWhittakerMOnLog 0 (1 / 3) (log 2 + airyLogZeta z) /
            ((2 : ℂ) ^ (5 / 3 : ℂ) * Gamma (1 / 3))) := by
  rw [airyBi_eq_kummerM hz]
  simp only [airyWhittakerMOnLog]
  rw [exp_log_two_add_airyLogZeta hz, show (-1 / 3 : ℂ) - 0 + 1 / 2 = 1 / 6 by norm_num,
    show (1 : ℂ) + 2 * (-1 / 3) = 1 / 3 by norm_num,
    show (1 / 3 : ℂ) - 0 + 1 / 2 = 5 / 6 by norm_num,
    show (1 : ℂ) + 2 * (1 / 3) = 5 / 3 by norm_num]
  have hΓ1 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ2 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have h1 : z ^ (-1 / 4 : ℂ) * exp (-(2 * airyZetaComplex z) / 2 + (-1 / 3 + 1 / 2) *
      (log 2 + airyLogZeta z)) / ((2 : ℂ) ^ (1 / 3 : ℂ) * Gamma (2 / 3)) =
      1 / ((3 : ℂ) ^ (1 / 6 : ℂ) * Gamma (2 / 3)) * exp (-airyZetaComplex z) := by
    rw [cpow_def_of_ne_zero hz, (cpow_two_three _).1, (cpow_two_three _).2, airyLogZeta,
      log_two_thirds]
    field_simp
    simp only [← exp_add]
    congr 1; ring
  have h2 : z ^ (-1 / 4 : ℂ) * (exp (log 3) * exp (-(2 * airyZetaComplex z) / 2 + (1 / 3 + 1 / 2) *
      (log 2 + airyLogZeta z))) / ((2 : ℂ) ^ (5 / 3 : ℂ) * Gamma (1 / 3)) =
      (3 : ℂ) ^ (5 / 6 : ℂ) / ((2 : ℂ) ^ (2 / 3 : ℂ) * Gamma (1 / 3)) *
        exp (2 / 3 * airyLogZeta z - airyZetaComplex z) := by
    rw [cpow_def_of_ne_zero hz, (cpow_two_three _).1, (cpow_two_three _).1, (cpow_two_three _).2,
      airyLogZeta, log_two_thirds]
    field_simp
    simp only [← exp_add]
    congr 1; ring
  rw [exp_log (by norm_num)] at h2
  linear_combination (-kummerM (1 / 6) (1 / 3) (2 * airyZetaComplex z)) * h1 -
    kummerM (5 / 6) (5 / 3) (2 * airyZetaComplex z) * h2

/-- The full logarithmic-plane Whittaker M representation (DLMF 9.6.24). -/
@[dlmf 9.6.E24]
theorem airyBiDeriv_eq_whittakerM_onLog {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = z ^ (1 / 4 : ℂ) *
        ((2 : ℂ) ^ (1 / 3 : ℂ) * airyWhittakerMOnLog 0 (-2 / 3) (log 2 + airyLogZeta z) /
            Gamma (1 / 3) +
        3 * airyWhittakerMOnLog 0 (2 / 3) (log 2 + airyLogZeta z) /
            ((2 : ℂ) ^ (10 / 3 : ℂ) * Gamma (2 / 3))) := by
  rw [airyBiDeriv_eq_kummerM hz]
  simp only [airyWhittakerMOnLog]
  rw [exp_log_two_add_airyLogZeta hz, show (-2 / 3 : ℂ) - 0 + 1 / 2 = -1 / 6 by norm_num,
    show (1 : ℂ) + 2 * (-2 / 3) = -1 / 3 by norm_num,
    show (2 / 3 : ℂ) - 0 + 1 / 2 = 7 / 6 by norm_num,
    show (1 : ℂ) + 2 * (2 / 3) = 7 / 3 by norm_num]
  have hΓ1 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hΓ2 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have h1 : z ^ (1 / 4 : ℂ) * ((2 : ℂ) ^ (1 / 3 : ℂ) * exp (-(2 * airyZetaComplex z) / 2 +
      (-2 / 3 + 1 / 2) * (log 2 + airyLogZeta z))) / Gamma (1 / 3) =
      (3 : ℂ) ^ (1 / 6 : ℂ) / Gamma (1 / 3) * exp (-airyZetaComplex z) := by
    rw [cpow_def_of_ne_zero hz, (cpow_two_three _).1, (cpow_two_three _).2, airyLogZeta,
      log_two_thirds]
    field_simp
    simp only [← exp_add]
    congr 1; ring
  have h2 : z ^ (1 / 4 : ℂ) * (exp (log 3) * exp (-(2 * airyZetaComplex z) / 2 + (2 / 3 + 1 / 2) *
      (log 2 + airyLogZeta z))) / ((2 : ℂ) ^ (10 / 3 : ℂ) * Gamma (2 / 3)) =
      (3 : ℂ) ^ (7 / 6 : ℂ) / ((2 : ℂ) ^ (7 / 3 : ℂ) * Gamma (2 / 3)) *
        exp (4 / 3 * airyLogZeta z - airyZetaComplex z) := by
    rw [cpow_def_of_ne_zero hz, (cpow_two_three _).1, (cpow_two_three _).1, (cpow_two_three _).2,
      airyLogZeta, log_two_thirds]
    field_simp
    simp only [← exp_add]
    congr 1; ring
  rw [exp_log (by norm_num)] at h2
  linear_combination (-kummerM (-1 / 6) (-1 / 3) (2 * airyZetaComplex z)) * h1 -
    kummerM (7 / 6) (7 / 3) (2 * airyZetaComplex z) * h2

/-- `Ai(z) = (2√π)⁻¹ z^{-1/4} W_{0,1/3}(2ζ)` for `|arg z| < 2π/3`, `ζ = (2/3) z^{3/2}`
(DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_whittakerW {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = (1 / (2 * Real.sqrt π)) * z ^ (-1 / 4 : ℂ) *
        whittakerW 0 (1 / 3) (2 * airyZetaComplex z) := by
  obtain ⟨h1, h2⟩ := log_two_airyZeta_bounds hz
  rw [← exp_log_two_add_airyLogZeta hz0, whittakerW_exp_eq_onLog _ _ (by
    convert div_three_ne_int (p := 5) (by norm_num) using 2; norm_num) h1 h2]
  exact airyAi_eq_whittakerW_onLog hz0

/-- `Ai(z) = 3^{-1/6} π^{-1/2} ζ^{2/3} e^{-ζ} U(5/6, 5/3, 2ζ)` for `|arg z| < 2π/3`,
`ζ = (2/3) z^{3/2}` (DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_kummerU {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π) *
      exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerU (5 / 6) (5 / 3) (2 * airyZetaComplex z) := by
  obtain ⟨h1, h2⟩ := log_two_airyZeta_bounds hz
  rw [← exp_log_two_add_airyLogZeta hz0, kummerU_exp_eq_onLog _ (by
    convert div_three_ne_int (p := 5) (by norm_num) using 2) h1 h2]
  exact airyAi_eq_kummerU_onLog hz0

/-- `Ai'(z) = -(2√π)⁻¹ z^{1/4} W_{0,2/3}(2ζ)` for `|arg z| < 2π/3`, `ζ = (2/3) z^{3/2}`
(DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_whittakerW {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAiDeriv z = -(1 / (2 * Real.sqrt π)) * z ^ (1 / 4 : ℂ) *
        whittakerW 0 (2 / 3) (2 * airyZetaComplex z) := by
  obtain ⟨h1, h2⟩ := log_two_airyZeta_bounds hz
  rw [← exp_log_two_add_airyLogZeta hz0, whittakerW_exp_eq_onLog _ _ (by
    convert div_three_ne_int (p := 7) (by norm_num) using 2; norm_num) h1 h2]
  exact airyAiDeriv_eq_whittakerW_onLog hz0

/-- `Ai'(z) = -3^{1/6} π^{-1/2} ζ^{4/3} e^{-ζ} U(7/6, 7/3, 2ζ)` for `|arg z| < 2π/3`,
`ζ = (2/3) z^{3/2}` (DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_kummerU {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAiDeriv z = -((3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π) *
      exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerU (7 / 6) (7 / 3) (2 * airyZetaComplex z) := by
  obtain ⟨h1, h2⟩ := log_two_airyZeta_bounds hz
  rw [← exp_log_two_add_airyLogZeta hz0, kummerU_exp_eq_onLog _ (by
    convert div_three_ne_int (p := 7) (by norm_num) using 2) h1 h2]
  exact airyAiDeriv_eq_kummerU_onLog hz0

/-- `Bi(z) = z^{-1/4} (M_{0,-1/3}(2ζ)/(2^{1/3} Γ(2/3)) + 3 M_{0,1/3}(2ζ)/(2^{5/3} Γ(1/3)))`
for `|arg z| < 2π/3`, `ζ = (2/3) z^{3/2}` (DLMF 9.6.23). -/
@[dlmf 9.6.E23]
theorem airyBi_eq_whittakerM {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyBi z = z ^ (-1 / 4 : ℂ) *
      (whittakerM 0 (-1 / 3) (2 * airyZetaComplex z) / ((2 : ℂ) ^ (1 / 3 : ℂ) * Gamma (2 / 3)) +
        3 * whittakerM 0 (1 / 3) (2 * airyZetaComplex z) /
            ((2 : ℂ) ^ (5 / 3 : ℂ) * Gamma (1 / 3))) := by
  obtain ⟨h1, h2⟩ := log_two_airyZeta_bounds hz
  rw [← exp_log_two_add_airyLogZeta hz0, whittakerM_exp_eq_onLog _ _ h1 h2,
    whittakerM_exp_eq_onLog _ _ h1 h2]
  exact airyBi_eq_whittakerM_onLog hz0

/-- `Bi'(z) = z^{1/4} (2^{1/3} M_{0,-2/3}(2ζ)/Γ(1/3) + 3 M_{0,2/3}(2ζ)/(2^{10/3} Γ(2/3)))`
for `|arg z| < 2π/3`, `ζ = (2/3) z^{3/2}` (DLMF 9.6.24). -/
@[dlmf 9.6.E24]
theorem airyBiDeriv_eq_whittakerM {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyBiDeriv z = z ^ (1 / 4 : ℂ) *
      ((2 : ℂ) ^ (1 / 3 : ℂ) * whittakerM 0 (-2 / 3) (2 * airyZetaComplex z) / Gamma (1 / 3) +
        3 * whittakerM 0 (2 / 3) (2 * airyZetaComplex z) /
            ((2 : ℂ) ^ (10 / 3 : ℂ) * Gamma (2 / 3))) := by
  obtain ⟨h1, h2⟩ := log_two_airyZeta_bounds hz
  rw [← exp_log_two_add_airyLogZeta hz0, whittakerM_exp_eq_onLog _ _ h1 h2,
    whittakerM_exp_eq_onLog _ _ h1 h2]
  exact airyBiDeriv_eq_whittakerM_onLog hz0

end DLMF.Airy

end
