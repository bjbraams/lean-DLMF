/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.InnerExpansions

/-!
# Scaled Struve asymptotic expansions

Normalization of the scaled Anger-Struve kernels yields the final uniform expansions.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

section StruveScaled

open scoped Interval

/-- `μ(λ)` of DLMF 11.11.12 is the phase at the saddle. -/
theorem struveSc_angerMu_eq {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    DLMF.Struve.angerMu (lam : ℂ) = ((struveSc_phiR lam (struveSc_s0 lam) : ℝ) : ℂ) := by
  have hu : 0 < Real.sqrt (1 - lam ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have e1 : (1 - (lam : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) := by
    rw [show 1 - (lam : ℂ) ^ 2 = ((1 - lam ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by nlinarith),
      Real.sqrt_eq_rpow]
  have hpos : 0 < (1 + Real.sqrt (1 - lam ^ 2)) / lam := by positivity
  rw [DLMF.Struve.angerMu, e1, show (1 + ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)) / (lam : ℂ) =
    (((1 + Real.sqrt (1 - lam ^ 2)) / lam : ℝ) : ℂ) by push_cast; ring, ← ofReal_log hpos.le,
    ← ofReal_sub]
  congr 1
  rw [struveSc_phiR, Real.arsinh, struveSc_s0, struveSc_sqrt_saddle h0 h1]
  congr 1
  · field_simp
  · congr 1; field_simp; ring

/-- The DLMF 11.11.15 right-hand side as the Laplace leading term. -/
theorem struveSc_inner_rhs {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {n θ : ℝ} (hn : 0 < n)
    (hθ : |θ| < π) :
    (2 / (π * ((n : ℂ) * exp ((θ : ℂ) * I)))) ^ (1 / 2 : ℂ) *
        exp (-((n : ℂ) * exp ((θ : ℂ) * I)) * DLMF.Struve.angerMu (lam : ℂ)) /
        (1 - (lam : ℂ) ^ 2) ^ (1 / 4 : ℂ) =
      1 / π * (exp (-((n : ℂ) * exp ((θ : ℂ) * I) *
        ((struveSc_phiR lam (struveSc_s0 lam) : ℝ) : ℂ))) *
        ((lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (struveSc_Q0 lam : ℂ))) ^ (1 / 2 : ℂ) /
          (Real.sqrt n : ℂ))) := by
  have hQ := struveSc_Q0_pos h0 h1
  have hb1 : -π < -θ := by linarith [le_abs_self θ]
  have hb2 : -θ ≤ π := by linarith [neg_abs_le θ]
  rw [struveSc_angerMu_eq h0 h1]
  have e1 : 2 / (π * ((n : ℂ) * exp ((θ : ℂ) * I))) =
      ((2 / (π * n) : ℝ) : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := by
    rw [show ((-θ : ℝ) : ℂ) * I = -((θ : ℂ) * I) by push_cast; ring, exp_neg]
    push_cast; field_simp
  have e2 : (π : ℂ) / (exp ((θ : ℂ) * I) * (struveSc_Q0 lam : ℂ)) =
      ((π / struveSc_Q0 lam : ℝ) : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := by
    rw [show ((-θ : ℝ) : ℂ) * I = -((θ : ℂ) * I) by push_cast; ring, exp_neg]
    push_cast; field_simp
  rw [e1, e2, ofReal_mul_exp_cpow (by positivity) hb1 hb2,
    ofReal_mul_exp_cpow (by positivity) hb1 hb2]
  have r1 : ((2 / (π * n) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 / (π * n)) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  have r2 : ((π / struveSc_Q0 lam : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (π / struveSc_Q0 lam) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  have hu : 0 < Real.sqrt (1 - lam ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have r3 : (1 - (lam : ℂ) ^ 2) ^ (1 / 4 : ℂ) = ((Real.sqrt (Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) := by
    rw [show 1 - (lam : ℂ) ^ 2 = ((1 - lam ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by nlinarith),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by nlinarith)]
    norm_num
  rw [r1, r2, r3]
  -- the real identity
  have hQ0 : struveSc_Q0 lam = lam ^ 2 * Real.sqrt (1 - lam ^ 2) / 2 := by
    rw [struveSc_Q0, struveSc_s0]; field_simp
  have key : Real.sqrt (2 / (π * n)) / Real.sqrt (Real.sqrt (1 - lam ^ 2)) =
      1 / π * (lam * Real.sqrt (π / struveSc_Q0 lam) / Real.sqrt n) := by
    have hL : 0 ≤ Real.sqrt (2 / (π * n)) / Real.sqrt (Real.sqrt (1 - lam ^ 2)) := by positivity
    have hR : 0 ≤ 1 / π * (lam * Real.sqrt (π / struveSc_Q0 lam) / Real.sqrt n) := by positivity
    rw [← sq_eq_sq₀ hL hR]
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hu.le, Real.sq_sqrt (by positivity),
      Real.sq_sqrt hn.le, hQ0]
    field_simp
  have hn' : (Real.sqrt n : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hn).ne'
  have hs4 : ((Real.sqrt (Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have keyC : ((Real.sqrt (2 / (π * n)) : ℝ) : ℂ) =
      1 / π * ((lam : ℂ) * ((Real.sqrt (π / struveSc_Q0 lam) : ℝ) : ℂ) / (Real.sqrt n : ℂ)) *
        ((Real.sqrt (Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) := by
    rw [div_eq_iff (Real.sqrt_pos.2 hu).ne'] at key
    rw [key]; push_cast; ring
  rw [keyC]
  field_simp

/-- Estimate under the stated parameter and domain assumptions: `|1 - (Real.sqrt (1 + s ^ 2))⁻¹| ≤
s ^ 2`. -/
theorem struveSc_one_sub_recip_sqrt (s : ℝ) : |1 - (Real.sqrt (1 + s ^ 2))⁻¹| ≤ s ^ 2 := by
  have hS := struveSc_sqrt_pos s
  have h1 := struveSc_one_le_sqrt s
  have h2 := struveSc_sqrt_sq s
  have hinv : (Real.sqrt (1 + s ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  rw [abs_of_nonneg (by linarith)]
  have : 1 - (Real.sqrt (1 + s ^ 2))⁻¹ = (Real.sqrt (1 + s ^ 2) - 1) / Real.sqrt (1 + s ^ 2) := by
    field_simp
  rw [this, div_le_iff₀ hS]
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `|struveSc_phiR 1 s - s ^ 3 / 6| ≤
3 / 10 * s ^ 5`. -/
theorem struveSc_phiR_one_sub_cube {s : ℝ} (hs : 0 ≤ s) :
    |struveSc_phiR 1 s - s ^ 3 / 6| ≤ 3 / 10 * s ^ 5 := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have h := struveSc_phase_one_sub_cube (a := 0) (K := 1) ha (fun t ht => by
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [struveSc_q_ofReal, norm_real, Real.norm_of_nonneg (inv_nonneg.2 (struveSc_sqrt_pos t).le)]
    exact inv_le_one_of_one_le₀ (struveSc_one_le_sqrt t)) hs
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one] at h
  rw [struveSc_phase_ofReal] at h
  have h' : ‖((struveSc_phiR 1 s - s ^ 3 / 6 : ℝ) : ℂ)‖ ≤ (1 / 2 + 1) / 5 * s ^ 5 := by
    push_cast; exact h
  rw [norm_real, Real.norm_eq_abs] at h'
  linarith

/-- Estimate under the stated parameter and domain assumptions: `M * u - u ^ 3 / 48 ≤ M * (48 * M
+ 1) / 2`. -/
theorem struveSc_cubic_absorb {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    M * u - u ^ 3 / 48 ≤ M * (48 * M + 1) / 2 := by
  rcases le_or_gt (48 * M) (u ^ 2) with h | h
  · have : M * u ≤ u ^ 3 / 48 := by nlinarith
    nlinarith [mul_nonneg hM (by positivity : (0 : ℝ) ≤ 48 * M + 1)]
  · have hu2 : u ≤ (48 * M + 1) / 2 := by nlinarith [sq_nonneg (u - 1)]
    have : M * u ≤ M * ((48 * M + 1) / 2) := mul_le_mul_of_nonneg_left hu2 hM
    nlinarith [pow_nonneg hu 3]

/-- Estimate under the stated parameter and domain assumptions: `Real.exp (-(ν * (s ^ 3 / (12 * (1
+ s ^ 2)))) + M * τ * s) ≤ Real.exp (M * (48 * M + 1) / 2) * Real.exp (-(ν / 48 * s ^ 3)) +
Real.exp (-(ν / 48 * s))`. -/
theorem struveSc_X_split {ν τ M s : ℝ} (hτ : 0 < τ) (hντ : ν = τ ^ 3) (hM : 0 ≤ M)
    (hτM : 48 * M ≤ τ ^ 2) (hs : 0 ≤ s) :
    Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s) ≤
      Real.exp (M * (48 * M + 1) / 2) * Real.exp (-(ν / 48 * s ^ 3)) +
        Real.exp (-(ν / 48 * s)) := by
  have hν : 0 ≤ ν := by rw [hντ]; positivity
  rcases le_total s 1 with h | h
  · have h1 : ν * (s ^ 3 / 24) ≤ ν * (s ^ 3 / (12 * (1 + s ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ hν
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [pow_nonneg hs 3, mul_le_mul_of_nonneg_left (pow_le_one₀ hs h : s ^ 2 ≤ 1)
        (pow_nonneg hs 3)]
    have h2 := struveSc_cubic_absorb hM (mul_nonneg hτ.le hs)
    have h3 : -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s ≤
        M * (48 * M + 1) / 2 + -(ν / 48 * s ^ 3) := by
      have : (τ * s) ^ 3 = ν * s ^ 3 := by rw [hντ]; ring
      nlinarith
    calc Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s)
        ≤ Real.exp (M * (48 * M + 1) / 2 + -(ν / 48 * s ^ 3)) := Real.exp_le_exp.2 h3
      _ = Real.exp (M * (48 * M + 1) / 2) * Real.exp (-(ν / 48 * s ^ 3)) := Real.exp_add _ _
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
  · have h1 : ν * (s / 24) ≤ ν * (s ^ 3 / (12 * (1 + s ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ hν
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [one_le_pow₀ h (n := 2), mul_le_mul_of_nonneg_left (one_le_pow₀ h (n := 2) :
        1 ≤ s ^ 2) hs]
    have h2 : M * τ * s ≤ ν / 48 * s := by
      have : M * τ ≤ ν / 48 := by
        rw [hντ]; nlinarith [mul_le_mul_of_nonneg_left hτM hτ.le]
      exact mul_le_mul_of_nonneg_right this hs
    have h3 : -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s ≤ -(ν / 48 * s) := by
      nlinarith
    calc Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s)
        ≤ Real.exp (-(ν / 48 * s)) := Real.exp_le_exp.2 h3
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- DLMF 11.10.4 on the real contour for `𝐀_{-ν}(z)`, `ν` real, `re z > 0`. -/
theorem struveSc_angerA_shift (ν : ℝ) {z : ℂ} (hz : 0 < z.re) :
    angerA (-(ν : ℂ)) z = 1 / π * ∫ s in Ioi (0 : ℝ),
      exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - (z - ν) * s) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have hθ : |(-(0 : ℝ))| < π / 2 := by rw [neg_zero, abs_zero]; positivity
  have hz' : 0 < (z * exp (((-(0 : ℝ) : ℝ) : ℂ) * I)).re := by
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]; exact hz
  rw [struveAs_angerA_eq_rot (-(ν : ℂ)) hθ hz', struveAs_rotInt]
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one, one_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have h := struveSc_integrand_eq 1 ha (ν : ℂ) (le_of_lt hr)
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one, ofReal_one, one_mul] at h
  rw [struveSc_phase_ofReal, struveSc_q_ofReal] at h
  have hsplit : exp (-(z * r)) = exp (-((z - ν) * r)) * exp (-((ν : ℂ) * r)) := by
    rw [← exp_add]; congr 1; ring
  rw [hsplit, mul_assoc, h, ← mul_assoc, ← exp_add]
  congr 2; ring

/-- Rescaling the cubic model integral to the Scorer integral. -/
theorem struveSc_lead_cube {τ : ℝ} (hτ : 0 < τ) (a : ℂ) :
    ∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) =
      (((2 : ℝ) ^ (1 / 3 : ℝ) / τ : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), exp (-(t : ℂ) ^ 3 / 3 + (-(((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * a) * t) := by
  set c : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ) / τ with hc
  have hc0 : 0 < c := by positivity
  have h23 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h := integral_comp_mul_left_Ioi (fun s : ℝ =>
    exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)) 0 hc0
  rw [mul_zero] at h
  have hL : (∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)) =
      (c : ℂ) * ∫ x in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * ((c * x : ℝ) : ℂ) ^ 3 / 6) -
        a * τ * ((c * x : ℝ) : ℂ)) := by
    rw [h, Complex.real_smul, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hc0.ne', ofReal_one,
      one_mul]
  rw [hL]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  congr 1
  have hτc : τ * c = (2 : ℝ) ^ (1 / 3 : ℝ) := by rw [hc]; field_simp
  have e1 : ((τ * c : ℝ) : ℂ) ^ 3 = 2 := by rw [hτc, ← ofReal_pow, h23]; norm_num
  have e2 : ((τ * c : ℝ) : ℂ) = (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by rw [hτc]
  push_cast at e1 e2 ⊢
  linear_combination (-(x : ℂ) ^ 3 / 6) * e1 + (-(a * x)) * e2

/-- Estimate under the stated parameter and domain assumptions: `s ^ 3 / (12 * (1 + s ^ 2)) ≤
struveSc_phiR 1 s`. -/
theorem struveSc_phiR_one_ge {s : ℝ} (hs : 0 ≤ s) :
    s ^ 3 / (12 * (1 + s ^ 2)) ≤ struveSc_phiR 1 s := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have h := struveSc_re_phase_one_ge ha (ρ := 1) zero_le_one hs
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one, mul_zero, Real.cos_zero,
    one_mul, ofReal_one] at h
  rwa [struveSc_phase_ofReal, ofReal_re] at h

/-- **The main estimate** behind DLMF 11.11.17. -/
theorem struveSc_turnU_est {M : ℝ} (hM : 0 ≤ M) {τ : ℝ} (hτ1 : 1 ≤ τ) (hτM : 48 * M ≤ τ ^ 2)
    {a : ℂ} (ha : ‖a‖ ≤ M) :
    ‖(∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ)) -
      ∫ s in Ioi (0 : ℝ), exp (-(((τ ^ 3 : ℝ) : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)‖ ≤
      (Real.exp (M * (48 * M + 1) / 2) * (16 + 3 / 10 * 768) + 2 * 48 ^ 3 +
        3 / 10 * 120 * 48 ^ 6) / τ ^ 3 := by
  have hτ0 : 0 < τ := by linarith
  set ν : ℝ := τ ^ 3 with hν
  have hν1 : 1 ≤ ν := one_le_pow₀ hτ1
  have hν0 : 0 < ν := by linarith
  set b : ℝ := ν / 48 with hb
  have hb0 : 0 < b := by positivity
  set Cm : ℝ := Real.exp (M * (48 * M + 1) / 2) with hCm
  have hCm0 : 0 < Cm := Real.exp_pos _
  set F : ℝ → ℂ := fun s => exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
    (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hF
  set G : ℝ → ℂ := fun s => exp (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) with hG
  set H : ℝ → ℝ := fun s => (Cm * Real.exp (-(b * s ^ 3)) + Real.exp (-(b * s))) *
    (s ^ 2 + ν * (3 / 10) * s ^ 5) with hH
  have hare : ∀ s : ℝ, 0 ≤ s → (-(a * τ * s)).re ≤ M * τ * s := by
    intro s hs
    rw [neg_re, show a * (τ : ℂ) * (s : ℂ) = ((τ * s : ℝ) : ℂ) * a by push_cast; ring,
      re_ofReal_mul]
    have := neg_le_of_abs_le (abs_re_le_norm a)
    nlinarith [mul_nonneg hτ0.le hs]
  have hbound : ∀ s : ℝ, 0 < s → ‖F s - G s‖ ≤ H s := by
    intro s hs
    set X : ℝ := Real.exp (-(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s) with hX
    have hlow := struveSc_phiR_one_ge hs.le
    have hA : (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s).re ≤
        -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s := by
      rw [sub_eq_add_neg, add_re, neg_re, ← ofReal_mul, ofReal_re]
      have := hare s hs.le
      nlinarith
    have hB : (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s).re ≤
        -(ν * (s ^ 3 / (12 * (1 + s ^ 2)))) + M * τ * s := by
      rw [sub_eq_add_neg, add_re, show -((ν : ℂ) * (s : ℂ) ^ 3 / 6) = ((-(ν * s ^ 3 / 6) : ℝ) : ℂ) by
        push_cast; ring, ofReal_re]
      have := hare s hs.le
      have h1 : s ^ 3 / (12 * (1 + s ^ 2)) ≤ s ^ 3 / 6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [pow_nonneg hs.le 3, mul_nonneg (pow_nonneg hs.le 3) (sq_nonneg s)]
      have : ν * (s ^ 3 / (12 * (1 + s ^ 2))) ≤ ν * (s ^ 3 / 6) := mul_le_mul_of_nonneg_left h1 hν0.le
      linarith
    have hsplit : F s - G s = exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
        ((((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) - 1) +
        (exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
          exp (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)) := by
      simp only [hF, hG]; ring
    have h1 : ‖exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s)‖ ≤ X := by
      rw [norm_exp]; exact Real.exp_le_exp.2 hA
    have h2 : ‖(((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) - 1‖ ≤ s ^ 2 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact struveSc_one_sub_recip_sqrt s
    have h3 : ‖(-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
        (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)‖ ≤ ν * (3 / 10 * s ^ 5) := by
      have : (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
          (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) =
          ((-(ν * (struveSc_phiR 1 s - s ^ 3 / 6)) : ℝ) : ℂ) := by push_cast; ring
      rw [this, norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hν0]
      exact mul_le_mul_of_nonneg_left (struveSc_phiR_one_sub_cube hs.le) hν0.le
    have h4 := struveSc_norm_exp_sub_exp_le hA hB
    have hXs := struveSc_X_split hτ0 hν hM hτM hs.le
    rw [hsplit]
    calc _ ≤ ‖exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s)‖ *
          ‖(((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) - 1‖ +
          ‖(-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) -
            (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s)‖ * X := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]; gcongr
      _ ≤ X * s ^ 2 + ν * (3 / 10 * s ^ 5) * X := by gcongr
      _ = X * (s ^ 2 + ν * (3 / 10) * s ^ 5) := by ring
      _ ≤ H s := by
          simp only [hH]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simpa [hX, hb, hCm] using hXs
  obtain ⟨i32, e32⟩ := struveSc_integral_pow_exp_cube 2 hb0
  obtain ⟨i35, e35⟩ := struveSc_integral_pow_exp_cube 5 hb0
  obtain ⟨i12, e12⟩ := struveSc_integral_pow_exp 2 hb0
  obtain ⟨i15, e15⟩ := struveSc_integral_pow_exp 5 hb0
  have hsplitH : ∀ s : ℝ, H s = (Cm * (Real.exp (-(b * s ^ 3)) * s ^ 2) +
      Cm * (ν * (3 / 10)) * (Real.exp (-(b * s ^ 3)) * s ^ 5)) +
      ((Real.exp (-(b * s)) * s ^ 2) + ν * (3 / 10) * (Real.exp (-(b * s)) * s ^ 5)) := by
    intro s; simp only [hH]; ring
  have j1 := (i32.const_mul Cm).add (i35.const_mul (Cm * (ν * (3 / 10))))
  have j2 := i12.add (i15.const_mul (ν * (3 / 10)))
  have hHi : IntegrableOn H (Ioi 0) := by
    refine IntegrableOn.congr_fun (j1.add j2) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; exact (hsplitH r).symm
  have k1 := integral_add (i32.const_mul Cm) (i35.const_mul (Cm * (ν * (3 / 10))))
  have k2 := integral_add i12 (i15.const_mul (ν * (3 / 10)))
  have k3 := integral_add j1 j2
  simp only [Pi.add_apply] at k3
  have hHint : ∫ s in Ioi (0 : ℝ), H s =
      (Cm * (b⁻¹ * (1 / 3)) + Cm * (ν * (3 / 10)) * (1 / b ^ 2 * (1 / 3))) +
      (2 / b ^ 3 + ν * (3 / 10) * (120 / b ^ 6)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hsplitH r), k3, k1, k2,
      integral_const_mul, integral_const_mul, integral_const_mul, e32, e35, e12, e15]
    have g1 : Real.Gamma ((((2 : ℕ) : ℝ) + 1) / 3) = 1 := by
      rw [show (((2 : ℕ) : ℝ) + 1) / 3 = 1 by norm_num, Real.Gamma_one]
    have g2 : Real.Gamma ((((5 : ℕ) : ℝ) + 1) / 3) = 1 := by
      rw [show (((5 : ℕ) : ℝ) + 1) / 3 = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero,
        Real.Gamma_one, mul_one]
    have b1 : b ^ (-(((2 : ℕ) : ℝ) + 1) / 3) = b⁻¹ := by
      rw [show (-(((2 : ℕ) : ℝ) + 1) / 3) = -1 by norm_num, Real.rpow_neg_one]
    have b2 : b ^ (-(((5 : ℕ) : ℝ) + 1) / 3) = 1 / b ^ 2 := by
      rw [show (-(((5 : ℕ) : ℝ) + 1) / 3) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hb0.le,
        Real.rpow_natCast, one_div]
    rw [g1, g2, b1, b2]
    norm_num [Nat.factorial]
  -- integrability and assembly
  have hSc : Continuous fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹ :=
    ((Real.continuous_sqrt.comp (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2)).inv₀
      fun s => (struveSc_sqrt_pos s).ne')
  have hFc : Continuous F := by
    have := struveSc_continuous_phiR 1
    simp only [hF]
    exact (continuous_exp.comp ((continuous_const.mul (continuous_ofReal.comp this)).neg.sub
      (continuous_const.mul continuous_ofReal))).mul (continuous_ofReal.comp hSc)
  have hGc : Continuous G := by simp only [hG]; fun_prop
  have hGi : IntegrableOn G (Ioi 0) := by
    obtain ⟨i30, -⟩ := struveSc_integral_pow_exp_cube 0 hb0
    obtain ⟨i10, -⟩ := struveSc_integral_pow_exp 0 hb0
    refine Integrable.mono' ((i30.const_mul Cm).add i10) hGc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    simp only [Pi.add_apply, pow_zero, mul_one]
    have hXs := struveSc_X_split hτ0 hν hM hτM hs0
    refine le_trans ?_ (by simpa [hb, hCm] using hXs)
    rw [hG, norm_exp, sub_eq_add_neg, add_re,
      show -((ν : ℂ) * (s : ℂ) ^ 3 / 6) = ((-(ν * s ^ 3 / 6) : ℝ) : ℂ) by push_cast; ring,
      ofReal_re]
    refine Real.exp_le_exp.2 ?_
    have := hare s hs0
    have h1 : s ^ 3 / (12 * (1 + s ^ 2)) ≤ s ^ 3 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_nonneg hs0 3, mul_nonneg (pow_nonneg hs0 3) (sq_nonneg s)]
    have : ν * (s ^ 3 / (12 * (1 + s ^ 2))) ≤ ν * (s ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left h1 hν0.le
    linarith
  have hdi : IntegrableOn (fun s => F s - G s) (Ioi 0) :=
    Integrable.mono' hHi ((hFc.sub hGc).aestronglyMeasurable) ((ae_restrict_iff'
      measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => hbound s hs))
  have hFi : IntegrableOn F (Ioi 0) := by
    have : IntegrableOn (fun s => (F s - G s) + G s) (Ioi 0) := hdi.add hGi
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp
  change ‖(∫ s in Ioi (0 : ℝ), F s) - ∫ s in Ioi (0 : ℝ), G s‖ ≤ _
  rw [← integral_sub hFi hGi]
  refine (norm_integral_le_of_norm_le hHi ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun s hs => hbound s hs))).trans ?_
  rw [hHint, hb]
  have hν3 : ν ≤ ν ^ 3 := le_self_pow₀ hν1 (by norm_num)
  have hν6 : ν ≤ ν ^ 5 := le_self_pow₀ hν1 (by norm_num)
  rw [le_div_iff₀ hν0]
  have e1 : (Cm * ((ν / 48)⁻¹ * (1 / 3)) + Cm * (ν * (3 / 10)) * (1 / (ν / 48) ^ 2 * (1 / 3))) * ν
      = Cm * (16 + 3 / 10 * 768) := by field_simp; ring
  have e2 : (2 / (ν / 48) ^ 3 + ν * (3 / 10) * (120 / (ν / 48) ^ 6)) * ν =
      2 * 48 ^ 3 / ν ^ 2 + 3 / 10 * 120 * 48 ^ 6 / ν ^ 4 := by field_simp
  have f1 : 2 * 48 ^ 3 / ν ^ 2 ≤ 2 * 48 ^ 3 := div_le_self (by norm_num) (one_le_pow₀ hν1)
  have f2 : 3 / 10 * 120 * 48 ^ 6 / ν ^ 4 ≤ 3 / 10 * 120 * 48 ^ 6 :=
    div_le_self (by norm_num) (one_le_pow₀ hν1)
  rw [add_mul, e1, e2]
  linarith

end StruveScaled

/-- Identity under the stated parameter and domain assumptions: `(fun ν : ℂ => angerA (-ν)
(lam*ν)) ~[sector (π-δ)] (fun ν => 1/(π*ν*(lam-1)))`. -/
@[dlmf 11.11.E14]
theorem angerA_scaled_outer_equiv {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π-δ)] (fun ν => 1/(π*ν*(lam-1))) := by
  obtain ⟨K, hK0, hK⟩ := struveSc_q_bounds hδ
  set κ0 : ℝ := (lam - 1) * Real.sin (δ / 2) with hκ0
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hκ0p : 0 < κ0 := mul_pos (by linarith) hs
  set C : ℝ := 1 / π * (K / κ0 ^ 2 + K / κ0 ^ 3) with hC
  have hmain : ∀ ν : ℂ, ν ≠ 0 → |arg ν| ≤ π - δ →
      ‖angerA (-ν) (lam * ν) - 1 / (π * ν * (lam - 1))‖ ≤ C / ‖ν‖ ^ 2 := by
    intro ν hν0 harg
    set a : ℝ := arg ν / 2 with ha
    have ha' : |a| ≤ (π - δ) / 2 := by rw [ha, abs_div, abs_two]; linarith
    have ha2 : |a| < π / 2 := by linarith
    set ρ : ℝ := ‖ν‖ with hρ
    have hρ0 : 0 < ρ := norm_pos_iff.2 hν0
    have hνe : ν = (ρ : ℂ) * exp ((2 * a : ℝ) * I) := by
      rw [ha, show 2 * (arg ν / 2) = arg ν by ring, hρ, norm_mul_exp_arg_mul_I]
    have hcos : Real.sin (δ / 2) ≤ Real.cos a := by
      rw [← Real.cos_abs, ← Real.cos_pi_div_two_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (by linarith) (by linarith)
    have hθ : |(-a)| < π / 2 := by rwa [abs_neg]
    have hz : 0 < ((lam : ℂ) * ν * exp (((-a : ℝ) : ℂ) * I)).re := by
      rw [hνe, show (lam : ℂ) * ((ρ : ℂ) * exp ((2 * a : ℝ) * I)) * exp (((-a : ℝ) : ℂ) * I) =
        ((lam * ρ : ℝ) : ℂ) * exp ((a : ℂ) * I) by
          rw [mul_assoc, mul_assoc, ← exp_add]; push_cast; ring_nf, re_ofReal_mul,
        exp_ofReal_mul_I_re]
      exact mul_pos (mul_pos (by linarith) hρ0) (struveSc_cos_pos ha2)
    have hrot := struveAs_angerA_eq_rot (-ν) hθ hz
    have hest := struveSc_integral_est hlam ha2 (fun s hs => hK a ha' s hs) hρ0
    rw [← hνe] at hest
    have hdiff : angerA (-ν) (lam * ν) - 1 / (π * ν * (lam - 1)) =
        1 / π * (exp (((-a : ℝ) : ℂ) * I) * (∫ r in Ioi (0 : ℝ),
          exp (-((lam : ℂ) * ν * exp (((-a : ℝ) : ℂ) * I) * r)) *
          struveAs_kernel (-ν) ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))) -
          1 / (ν * ((lam : ℂ) - 1))) := by
      rw [hrot, struveAs_rotInt]
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
      field_simp
    rw [hdiff, norm_mul, norm_div, norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hκa : κ0 ≤ (lam - 1) * Real.cos a := mul_le_mul_of_nonneg_left hcos (by linarith)
    calc 1 / π * ‖_‖ ≤ 1 / π * ((K / ((lam - 1) * Real.cos a) ^ 2 +
          K / ((lam - 1) * Real.cos a) ^ 3) / ρ ^ 2) :=
          mul_le_mul_of_nonneg_left hest (by positivity)
      _ ≤ 1 / π * ((K / κ0 ^ 2 + K / κ0 ^ 3) / ρ ^ 2) := by
          gcongr
      _ = C / ρ ^ 2 := by rw [hC]; ring
  rw [IsEquivalent, isLittleO_iff]
  intro ε hε
  have hl0 : (0 : ℝ) < lam - 1 := by linarith
  set R : ℝ := max 1 (C * π * (lam - 1) / ε) with hR
  have hev : ∀ᶠ ν in sector (π - δ), R ≤ ‖ν‖ ∧ ν ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ π - δ} :=
    ((tendsto_norm_sector (π - δ)).eventually (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [hev] with ν ⟨hνR, hν0, harg⟩
  have hρ1 : 1 ≤ ‖ν‖ := (le_max_left _ _).trans hνR
  have hρ0 : 0 < ‖ν‖ := by linarith
  have hv : ‖1 / (π * ν * (lam - 1))‖ = 1 / (π * ‖ν‖ * (lam - 1)) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      show (lam : ℂ) - 1 = ((lam - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg hl0.le]
  simp only [Pi.sub_apply]
  rw [hv]
  refine (hmain ν hν0 harg).trans ?_
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hRε : C * π * (lam - 1) / ε ≤ ‖ν‖ := (le_max_right _ _).trans hνR
  rw [div_le_iff₀ hε] at hRε
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [Real.pi_pos]

/-- Identity under the stated parameter and domain assumptions: `(fun ν : ℂ => angerA (-ν)
(lam*ν)) ~[sector (π/2-δ)] (fun ν => (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu
lam)/(1-lam^2:ℂ)^(1/4:ℂ))`. -/
@[dlmf 11.11.E15]
theorem angerA_scaled_inner_equiv {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π/2-δ)] (fun ν => (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)) := by
  obtain ⟨C, n₀, hn₀, hC⟩ := struveSc_inner_est h0 h1 hδ hδπ
  set φ₀ := struveSc_phiR lam (struveSc_s0 lam) with hφ₀
  set Q0 := struveSc_Q0 lam with hQ0
  have hQ := struveSc_Q0_pos h0 h1
  set K1 : ℝ := lam * Real.sqrt (π / Q0) with hK1
  have hK1p : 0 < K1 := by rw [hK1]; positivity
  have hmain : ∀ ν : ℂ, ν ≠ 0 → |arg ν| ≤ π / 2 - δ → n₀ ≤ ‖ν‖ →
      ‖angerA (-ν) (lam * ν) - (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)‖ ≤
        |C| / K1 / Real.sqrt ‖ν‖ *
          ‖(2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)‖ := by
    intro ν hν0 harg hn
    set n := ‖ν‖ with hn'
    set θ := arg ν with hθ'
    have hn0 : 0 < n := norm_pos_iff.2 hν0
    have hνe : ν = (n : ℂ) * exp ((θ : ℂ) * I) := (norm_mul_exp_arg_mul_I ν).symm
    have hθπ : |θ| < π := by linarith [Real.pi_pos]
    have hcos := struveSc_cos_ge hδ.le hδπ harg
    have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
    have hre : 0 < ν.re := by
      rw [hνe, re_ofReal_mul, exp_ofReal_mul_I_re]; nlinarith
    have hrep := struveSc_angerA_real h0 hre
    have hfac : (∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s : ℝ) : ℂ))) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ)) = exp (-(ν * (φ₀ : ℂ))) *
        ∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s - φ₀ : ℝ) : ℂ))) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [← mul_assoc, ← exp_add]; congr 2; push_cast; ring
    have hrhs := struveSc_inner_rhs h0 h1 hn0 hθπ
    rw [← hνe] at hrhs
    rw [hrhs, hrep, hfac]
    set I0 := ∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s - φ₀ : ℝ) : ℂ))) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hI0
    set L := (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (Q0 : ℂ))) ^ (1 / 2 : ℂ) with hL
    have hest := hC n θ hn harg
    rw [← hνe] at hest
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hsqc : (Real.sqrt n : ℂ) ≠ 0 := ofReal_ne_zero.2 hsq.ne'
    have hLn : ‖L‖ = K1 := by
      rw [hL, norm_mul, norm_real, Real.norm_of_nonneg h0.le,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, norm_cpow_real, norm_div,
        norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hQ.le, ← Real.sqrt_eq_rpow, hK1]
    have hdiff : 1 / π * (exp (-(ν * (φ₀ : ℂ))) * I0) - 1 / π * (exp (-(ν * (φ₀ : ℂ))) *
        (L / (Real.sqrt n : ℂ))) = 1 / π * exp (-(ν * (φ₀ : ℂ))) *
          (((Real.sqrt n : ℂ) * I0 - L) / (Real.sqrt n : ℂ)) := by
      field_simp
    rw [hdiff]
    have hE : 0 < ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ := by
      rw [norm_mul]; refine mul_pos ?_ (by rw [norm_exp]; exact Real.exp_pos _)
      rw [norm_div, norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]; positivity
    have hRn : ‖1 / (π : ℂ) * (exp (-(ν * (φ₀ : ℂ))) * (L / (Real.sqrt n : ℂ)))‖ =
        ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (K1 / Real.sqrt n) := by
      rw [← mul_assoc, norm_mul, norm_div, hLn, norm_real, Real.norm_of_nonneg hsq.le]
    have hLn' : ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ))) *
        (((Real.sqrt n : ℂ) * I0 - L) / (Real.sqrt n : ℂ))‖ =
        ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (‖(Real.sqrt n : ℂ) * I0 - L‖ / Real.sqrt n) := by
      rw [norm_mul, norm_div, norm_real, Real.norm_of_nonneg hsq.le]
    rw [hRn, hLn']
    have h2 : ‖(Real.sqrt n : ℂ) * I0 - L‖ / Real.sqrt n ≤ |C| / K1 / Real.sqrt n *
        (K1 / Real.sqrt n) := by
      rw [div_le_iff₀ hsq]
      calc ‖(Real.sqrt n : ℂ) * I0 - L‖ ≤ C / Real.sqrt n := hest
        _ ≤ |C| / Real.sqrt n := by gcongr; exact le_abs_self C
        _ = |C| / K1 / Real.sqrt n * (K1 / Real.sqrt n) * Real.sqrt n := by
          field_simp
    calc ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (‖(Real.sqrt n : ℂ) * I0 - L‖ / Real.sqrt n)
        ≤ ‖1 / (π : ℂ) * exp (-(ν * (φ₀ : ℂ)))‖ * (|C| / K1 / Real.sqrt n *
          (K1 / Real.sqrt n)) := by gcongr
      _ = _ := by ring
  rw [IsEquivalent, isLittleO_iff]
  intro ε hε
  set R : ℝ := max n₀ ((|C| / K1 / ε) ^ 2 + 1) with hR
  have hev : ∀ᶠ ν in sector (π / 2 - δ), R ≤ ‖ν‖ ∧
      ν ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ π / 2 - δ} :=
    ((tendsto_norm_sector (π / 2 - δ)).eventually (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [hev] with ν ⟨hνR, hν0, harg⟩
  have hn := (le_max_left _ _).trans hνR
  have hn2 : (|C| / K1 / ε) ^ 2 + 1 ≤ ‖ν‖ := (le_max_right _ _).trans hνR
  simp only [Pi.sub_apply]
  refine (hmain ν hν0 harg hn).trans ?_
  gcongr
  have hn0 : 0 < ‖ν‖ := norm_pos_iff.2 hν0
  have hsq : 0 < Real.sqrt ‖ν‖ := Real.sqrt_pos.2 hn0
  rw [div_le_iff₀ hsq]
  have : |C| / K1 / ε < Real.sqrt ‖ν‖ := by
    rw [show |C| / K1 / ε = Real.sqrt ((|C| / K1 / ε) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  rw [div_lt_iff₀ hε] at this
  linarith

/-- Identity under the stated parameter and domain assumptions: `(fun ν : ℂ => angerA (-ν) ν)
~[sector (π-δ)] (fun ν => 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ)))`. -/
@[dlmf 11.11.E16]
theorem angerA_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) ν) ~[sector (π-δ)] (fun ν => 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  obtain ⟨K, hK0, hK⟩ := struveSc_q_bounds hδ
  set s0 : ℝ := Real.sin (δ / 2) with hs0
  have hs : 0 < s0 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set Cst : ℝ := K * ((s0 / 24) ^ (-(2 / 3 : ℝ)) * (1 / 3) * Real.Gamma (2 / 3) +
      1 / (s0 / 24) ^ 2) + (1 / 2 + K) / 5 * (1 / (3 * (s0 / 24) ^ 2) + 120 / (s0 / 24) ^ 6)
    with hCst
  have hCst0 : 0 ≤ Cst := by
    have : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    rw [hCst]; positivity
  have hmain : ∀ ν : ℂ, ν ≠ 0 → |arg ν| ≤ π - δ → 1 ≤ ‖ν‖ →
      ‖angerA (-ν) ν - 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))‖ ≤
        1 / π * Cst * ‖ν‖ ^ (-(2 / 3 : ℝ)) := by
    intro ν hν0 harg hρ1
    set a : ℝ := arg ν / 2 with ha
    have ha' : |a| ≤ (π - δ) / 2 := by rw [ha, abs_div, abs_two]; linarith
    have ha2 : |a| < π / 2 := by linarith
    set ρ : ℝ := ‖ν‖ with hρ
    have hρ0 : 0 < ρ := norm_pos_iff.2 hν0
    have hνe : ν = (ρ : ℂ) * exp ((2 * a : ℝ) * I) := by
      rw [ha, show 2 * (arg ν / 2) = arg ν by ring, hρ, norm_mul_exp_arg_mul_I]
    have hcos : Real.sin (δ / 2) ≤ Real.cos a := by
      rw [← Real.cos_abs, ← Real.cos_pi_div_two_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (by linarith) (by linarith)
    have hθ : |(-a)| < π / 2 := by rwa [abs_neg]
    have hz : 0 < (ν * exp (((-a : ℝ) : ℂ) * I)).re := by
      rw [hνe, show (ρ : ℂ) * exp ((2 * a : ℝ) * I) * exp (((-a : ℝ) : ℂ) * I) =
        ((ρ : ℝ) : ℂ) * exp ((a : ℂ) * I) by
          rw [mul_assoc, ← exp_add]; push_cast; ring_nf, re_ofReal_mul,
        exp_ofReal_mul_I_re]
      exact mul_pos hρ0 (struveSc_cos_pos ha2)
    have hrot := struveAs_angerA_eq_rot (-ν) hθ hz
    have hest := struveSc_turning_est ha2 hK0.le hs hcos (fun s hs => hK a ha' s hs) hρ1
    have hrhs := struveSc_turning_rhs ha2 hρ0
    rw [← hνe] at hest hrhs
    set E : ℂ := exp (((-a : ℝ) : ℂ) * I) with hE
    have hint : (∫ r in Ioi (0 : ℝ), exp (-(ν * E * r)) * struveAs_kernel (-ν) ((r : ℂ) * E)) =
        ∫ r in Ioi (0 : ℝ), exp (-(ν * struveSc_phase 1 ((r : ℂ) * E))) *
          (1 + ((r : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have := struveSc_integrand_eq 1 ha2 ν (le_of_lt hr)
      rwa [ofReal_one, one_mul] at this
    have hCre : 0 < (ν * E ^ 3 / 6).re := by
      rw [hνe, hE, ← exp_nat_mul, show (ρ : ℂ) * exp ((2 * a : ℝ) * I) *
          exp (((3 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I)) / 6 =
          ((ρ / 6 : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) by
        rw [mul_assoc, ← exp_add]; push_cast; ring_nf, re_ofReal_mul, exp_ofReal_mul_I_re,
        Real.cos_neg]
      exact mul_pos (by positivity) (struveSc_cos_pos ha2)
    rw [hrot, struveAs_rotInt, hint, hrhs, ← struveSc_integral_exp_cube hCre, ← mul_sub,
      ← mul_sub, norm_mul, norm_mul, hE, norm_exp_ofReal_mul_I, one_mul, ← hE, norm_div,
      norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hest (by positivity)
  set c1 : ℝ := 2 ^ (4 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) with hc1
  have hc10 : 0 < c1 := by
    have : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    rw [hc1]; positivity
  rw [IsEquivalent, isLittleO_iff]
  intro ε hε
  set M : ℝ := 1 / π * Cst / (ε * c1) + 1 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set R : ℝ := max 1 (M ^ 3) with hR
  have hev : ∀ᶠ ν in sector (π - δ), R ≤ ‖ν‖ ∧ ν ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ π - δ} :=
    ((tendsto_norm_sector (π - δ)).eventually (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  filter_upwards [hev] with ν ⟨hνR, hν0, harg⟩
  have hρ1 : 1 ≤ ‖ν‖ := (le_max_left _ _).trans hνR
  have hρ0 : 0 < ‖ν‖ := by linarith
  simp only [Pi.sub_apply]
  rw [struveSc_norm_turning_rhs ν, ← hc1]
  refine (hmain ν hν0 harg hρ1).trans ?_
  have hM3 : M ≤ ‖ν‖ ^ (1 / 3 : ℝ) := by
    have h1 : M ^ 3 ≤ ‖ν‖ := (le_max_right _ _).trans hνR
    have h2 : (M ^ 3) ^ (1 / 3 : ℝ) = M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; norm_num
    rw [← h2]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  set t : ℝ := ‖ν‖ ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := by positivity
  have h23 : ‖ν‖ ^ (-(2 / 3 : ℝ)) = 1 / t * (1 / t) := by
    rw [ht, show (-(2 / 3 : ℝ)) = -(1 / 3) + -(1 / 3) by norm_num, Real.rpow_add hρ0,
      Real.rpow_neg hρ0.le]
    ring
  rw [h23]
  have hMε : 1 / π * Cst ≤ ε * c1 * (M - 1) := by
    rw [hM]; field_simp; linarith
  have key : 1 / π * Cst * (1 / t) ≤ ε * c1 := by
    rw [mul_one_div, div_le_iff₀ ht0]
    nlinarith [mul_pos hε hc10]
  calc 1 / π * Cst * (1 / t * (1 / t)) = 1 / π * Cst * (1 / t) * (1 / t) := by ring
    _ ≤ ε * c1 * (1 / t) := mul_le_mul_of_nonneg_right key (by positivity)
    _ = ε * (c1 / t) := by ring

/-- angerJ turning equiv, DLMF 11.11.18 for real `ν → +∞`.

DLMF 1.1.2 extended this to `ν → ∞` in `|ph ν| ≤ π - δ`; that extension fails. By 11.10.15,
`𝐉_ν(ν) = J_ν(ν) + sin(πν) 𝐀_ν(ν)` with `𝐀_ν(ν) ~ 1/(2πν)`, and off the real axis the second
term grows like `e^{π|Im ν|}/|ν|`: at `ph ν = 0.3` the ratio to the leading term is about `10⁶`,
`10¹⁴`, `10³⁰` for `|ν| = 20, 40, 80`. The original DLMF condition `ν → +∞` is kept. -/
@[dlmf 11.11.E18 "special case: ν → +∞ (the complex sector of DLMF 1.1.2 fails), DLMF erratum"]
theorem angerJ_turning_equiv :
    (fun ν : ℝ => angerJ ν ν) ~[atTop] (fun ν : ℝ => 2^(1/3:ℂ)/(3^(2/3:ℂ)*Gamma (2/3)*(ν:ℂ)^(1/3:ℂ))) := by
  have hK : (2 : ℝ) ^ (1 / 3 : ℝ) / (3 ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) ≠ 0 := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3); positivity
  have hlim : Tendsto (fun ν : ℝ => ν ^ (1 / 3 : ℝ) * ((1 / π) * (∫ x in (0 : ℝ)..π,
      exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).re)) atTop
      (𝓝 (2 ^ (1 / 3 : ℝ) / (3 ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)))) := by
    have h := ((continuous_re.tendsto _).comp struveTP_tendsto_integral).const_mul (1 / π)
    rw [← struveTP_const_J]
    convert h using 2
    · simp only [Function.comp, re_ofReal_mul]; ring
    · rw [re_ofReal_mul, re_ofReal_mul, exp_ofReal_mul_I_re]; ring
  have := struveTP_isEquivalent_of_tendsto hK hlim
  simp only [← struveTP_angerJ_eq] at this
  refine this.congr_right ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν
  have := struveTP_rhs_eq (2 / 3) hν
  push_cast at this
  rw [this]
  push_cast; ring

/-- weberE turning equiv, DLMF 11.11.19 for real `ν → +∞`.

As for 11.11.18, the complex sector `|ph ν| ≤ π - δ` of DLMF 1.1.2 fails: by 11.10.16,
`𝐄_ν(ν) = -Y_ν(ν) - cos(πν) 𝐀_ν(ν) - 𝐀_{-ν}(ν)`, and `cos(πν) 𝐀_ν(ν)` grows like
`e^{π|Im ν|}/|ν|` off the real axis. The original DLMF condition `ν → +∞` is kept. -/
@[dlmf 11.11.E19 "special case: ν → +∞ (the complex sector of DLMF 1.1.2 fails), DLMF erratum"]
theorem weberE_turning_equiv :
    (fun ν : ℝ => weberE ν ν) ~[atTop] (fun ν : ℝ => 2^(1/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*(ν:ℂ)^(1/3:ℂ))) := by
  have hK : (2 : ℝ) ^ (1 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) ≠ 0 := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3); positivity
  have hlim : Tendsto (fun ν : ℝ => ν ^ (1 / 3 : ℝ) * ((1 / π) * (∫ x in (0 : ℝ)..π,
      exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).im)) atTop
      (𝓝 (2 ^ (1 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)))) := by
    have h := ((continuous_im.tendsto _).comp struveTP_tendsto_integral).const_mul (1 / π)
    rw [← struveTP_const_E]
    convert h using 2
    · simp only [Function.comp, im_ofReal_mul]; ring
    · rw [im_ofReal_mul, im_ofReal_mul, exp_ofReal_mul_I_im]; ring
  have := struveTP_isEquivalent_of_tendsto hK hlim
  simp only [← struveTP_weberE_eq] at this
  refine this.congr_right ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν
  have := struveTP_rhs_eq (7 / 6) hν
  push_cast at this
  rw [this]
  push_cast; ring

/-- Turning-point approximation uniform on bounded complex transition parameters; positive real order. -/
@[dlmf 11.11.E17]
theorem angerA_turning_uniform (M : ℝ) (hM : 0 < M) :
    (fun p : ℝ × ℂ => angerA (-p.1) (p.1+p.2*(p.1:ℂ)^(1/3:ℂ))-2^(1/3:ℂ)*(p.1:ℂ)^(-1/3:ℂ)*scorerHi (-2^(1/3:ℂ)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℂ | ‖p.2‖ ≤ M}] (fun p : ℝ × ℂ => (p.1:ℂ)^(-1:ℤ)) := by
  set CU : ℝ := Real.exp (M * (48 * M + 1) / 2) * (16 + 3 / 10 * 768) + 2 * 48 ^ 3 +
    3 / 10 * 120 * 48 ^ 6 with hCU
  refine IsBigO.of_bound (CU / π) ?_
  set R : ℝ := max 1 ((48 * M + 1) ^ 3) with hR
  filter_upwards [mem_inf_of_left (preimage_mem_comap (Ici_mem_atTop R)),
    mem_inf_of_right (mem_principal_self _)] with p hp hpM
  obtain ⟨ν, a⟩ := p
  simp only [mem_preimage, mem_Ici] at hp
  simp only at hpM
  simp only
  have hν1 : 1 ≤ ν := (le_max_left _ _).trans hp
  have hν0 : 0 < ν := by linarith
  set τ : ℝ := ν ^ (1 / 3 : ℝ) with hτ
  have hτ0 : 0 < τ := by positivity
  have hντ : τ ^ 3 = ν := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hν0.le]; norm_num
  have hτ1 : 48 * M + 1 ≤ τ := by
    have h1 : (48 * M + 1) ^ 3 ≤ ν := (le_max_right _ _).trans hp
    have h2 : ((48 * M + 1) ^ 3) ^ (1 / 3 : ℝ) = 48 * M + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [← h2]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hτ1' : 1 ≤ τ := by linarith
  have hτM : 48 * M ≤ τ ^ 2 := by nlinarith
  have hcτ : (ν : ℂ) ^ (1 / 3 : ℂ) = (τ : ℂ) := by
    rw [hτ, ofReal_cpow hν0.le]; push_cast; rfl
  have hcτ' : (ν : ℂ) ^ (-1 / 3 : ℂ) = ((τ⁻¹ : ℝ) : ℂ) := by
    rw [hτ, ← Real.rpow_neg hν0.le, ofReal_cpow hν0.le]; push_cast; ring_nf
  have hc2 : (2 : ℂ) ^ (1 / 3 : ℂ) = (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  rw [hcτ, hcτ', hc2]
  -- representation
  have hzre : 0 < ((ν : ℂ) + a * τ).re := by
    rw [add_re, ofReal_re, show a * (τ : ℂ) = (τ : ℂ) * a by ring, re_ofReal_mul]
    have := neg_le_of_abs_le (abs_re_le_norm a)
    have hMτ : M * τ < ν := by rw [← hντ]; nlinarith
    nlinarith
  rw [struveSc_angerA_shift ν hzre]
  have hsc := (scorerHi_exp_integral (-(((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * a)).2
  rw [hsc]
  have hlead := struveSc_lead_cube hτ0 a
  have hest := struveSc_turnU_est hM.le hτ1' hτM hpM
  rw [hντ] at hlead hest
  set Fi := ∫ s in Ioi (0 : ℝ), exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) - a * τ * s) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hFi
  set Gi := ∫ s in Ioi (0 : ℝ), exp (-((ν : ℂ) * (s : ℂ) ^ 3 / 6) - a * τ * s) with hGi
  set Ti := ∫ t in Ioi (0 : ℝ), exp (-(t : ℂ) ^ 3 / 3 + (-(((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * a) * t)
    with hTi
  have hint : ∫ s in Ioi (0 : ℝ), exp (-((ν : ℂ) * ((struveSc_phiR 1 s : ℝ) : ℂ)) -
      ((ν : ℂ) + a * τ - ν) * s) * (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) = Fi := by
    rw [hFi]; congr 1; funext s; congr 3; ring
  rw [hint]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have hdiff : 1 / (π : ℂ) * Fi - (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((τ⁻¹ : ℝ) : ℂ) * (Ti / π) =
      1 / (π : ℂ) * (Fi - Gi) := by
    rw [hlead]; push_cast; field_simp
  rw [hdiff, norm_mul, norm_div, norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    norm_zpow, norm_real, Real.norm_of_nonneg hν0.le]
  calc 1 / π * ‖Fi - Gi‖ ≤ 1 / π * (CU / τ ^ 3) := by
        gcongr; rw [hντ, hCU]; exact hest
    _ = CU / π * ν ^ (-1 : ℤ) := by
        rw [hντ, zpow_neg_one]; ring

/-- The recurrence quotient of DLMF 11.11(iii) evaluated on the circle-integral form:
if `A_k = c I_n` on the disc `|λ - λ₀| < ε` (`n = 2k+1`), the quotient defining `A_{k+1}` equals
`c I_{n+2}` at every point of the disc other than `λ = 1`. -/
theorem struveLO_quotient_eq {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : StruveLOGood r ε lam₀)
    (k : ℕ) (c : ℂ)
    (hA : ∀ l ∈ Metric.ball lam₀ ε, angerScaledA k l = c * struveLO_I r (fun _ => 1) (2 * k + 1) l)
    {lam : ℂ} (hlam : lam ∈ Metric.ball lam₀ ε) (h1 : lam ≠ 1) :
    lam/(1-lam^2)*(lam*iteratedDeriv 2 (angerScaledA k) lam+deriv (angerScaledA k) lam)/
      ((2*k+1:ℂ)*(2*k+2)) = c * struveLO_I r (fun _ => 1) (2 * (k + 1) + 1) lam := by
  set n := 2 * k + 1 with hn
  have hU : IsOpen (Metric.ball lam₀ ε) := Metric.isOpen_ball
  have hd1 : ∀ l ∈ Metric.ball lam₀ ε, HasDerivAt (angerScaledA k)
      (c * (-(n : ℂ) * struveLO_I r (fun t => 1 * sinh t) (n + 1) l)) l := by
    intro l hl
    refine ((struveLO_hasDerivAt_I hr hG continuous_const n hl).const_mul c).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hl] with x hx using hA x hx
  have hd2 : HasDerivAt (fun l => c * (-(n : ℂ) * struveLO_I r (fun t => 1 * sinh t) (n + 1) l))
      (c * (-(n : ℂ) * (-((n + 1 : ℕ) : ℂ) *
        struveLO_I r (fun t => 1 * sinh t * sinh t) (n + 1 + 1) lam))) lam :=
    (((struveLO_hasDerivAt_I hr hG (g := fun t => 1 * sinh t) (by fun_prop) (n + 1)
      hlam).const_mul _).const_mul c)
  have hD : deriv (angerScaledA k) lam =
      c * (-(n : ℂ) * struveLO_I r (fun t => 1 * sinh t) (n + 1) lam) := (hd1 lam hlam).deriv
  have hD2 : iteratedDeriv 2 (angerScaledA k) lam = c * (-(n : ℂ) * (-((n + 1 : ℕ) : ℂ) *
        struveLO_I r (fun t => 1 * sinh t * sinh t) (n + 1 + 1) lam)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    refine (hd2.congr_of_eventuallyEq ?_).deriv
    filter_upwards [hU.mem_nhds hlam] with x hx using (hd1 x hx).deriv
  have hrec := struveLO_recurrence hr hG n (Metric.ball_subset_closedBall hlam)
  have hl1 : 1 + lam ≠ 0 := by
    have := hG lam (Metric.ball_subset_closedBall hlam) 0 (Metric.mem_closedBall_self hr.le)
    rwa [struveLO_dslope_zero, mul_one] at this
  have hsq : 1 - lam ^ 2 ≠ 0 := by
    rw [show 1 - lam ^ 2 = (1 - lam) * (1 + lam) by ring]
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm h1)) hl1
  have hk : ((2 * k + 1 : ℂ) * (2 * k + 2)) ≠ 0 := by
    have : ((2 * k + 1 : ℕ) : ℂ) * ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * k + 1) * (2 * k + 2) ≠ 0)
    exact_mod_cast this
  rw [show 2 * (k + 1) + 1 = n + 2 by omega, hD, hD2]
  set X2 := struveLO_I r (fun t => 1 * sinh t * sinh t) (n + 1 + 1) lam
  set X1 := struveLO_I r (fun t => 1 * sinh t) (n + 1) lam
  set X0 := struveLO_I r (fun _ => 1) (n + 2) lam
  have hnc : (n : ℂ) = 2 * k + 1 := by rw [hn]; push_cast; ring
  push_cast
  rw [hnc] at hrec ⊢
  rw [div_eq_iff hk, div_mul_eq_mul_div, div_eq_iff hsq]
  linear_combination c * hrec

/-- Under the hypothesis of `struveLO_quotient_eq`, the recurrence quotient tends to
`c I_{2k+3}(λ)` along the punctured neighbourhood of every point `λ` of the disc. -/
theorem struveLO_tendsto_quotient {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : StruveLOGood r ε lam₀)
    (k : ℕ) (c : ℂ)
    (hA : ∀ l ∈ Metric.ball lam₀ ε, angerScaledA k l = c * struveLO_I r (fun _ => 1) (2 * k + 1) l)
    {lam : ℂ} (hlam : lam ∈ Metric.ball lam₀ ε) :
    Tendsto (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/
      ((2*k+1:ℂ)*(2*k+2))) (𝓝[≠] lam)
      (𝓝 (c * struveLO_I r (fun _ => 1) (2 * (k + 1) + 1) lam)) := by
  have hc : ContinuousAt (fun l => c * struveLO_I r (fun _ => 1) (2 * (k + 1) + 1) l) lam :=
    ((struveLO_hasDerivAt_I hr hG continuous_const _ hlam).continuousAt).const_mul c
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev : ∀ᶠ l in 𝓝[≠] lam, l ∈ Metric.ball lam₀ ε ∧ l ≠ 1 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hlam)) ?_
    by_cases h1 : lam = 1
    · subst h1; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h1)
  filter_upwards [hev] with l hl
  exact (struveLO_quotient_eq hr hG k c hA hl.1 hl.2).symm

/-- On a good disc, `A_k(λ) = (2πi)⁻¹ ∮ (t + λ sinh t)^{-(2k+1)} dt` (Lagrange inversion form of
the coefficients of DLMF 11.11.8). -/
theorem struveLO_angerScaledA_eq {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : StruveLOGood r ε lam₀)
    (k : ℕ) : ∀ l ∈ Metric.ball lam₀ ε,
      angerScaledA k l = (2 * π * I)⁻¹ * struveLO_I r (fun _ => 1) (2 * k + 1) l := by
  induction k with
  | zero =>
    intro l hl
    have hl1 : 1 + l ≠ 0 := by
      have := hG l (Metric.ball_subset_closedBall hl) 0 (Metric.mem_closedBall_self hr.le)
      rwa [struveLO_dslope_zero, mul_one] at this
    have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [struveLO_I_one hr hG (Metric.ball_subset_closedBall hl)]
    simp only [angerScaledA]
    field_simp
  | succ k ih =>
    intro l hl
    exact (struveLO_tendsto_quotient hr hG k _ ih hl).limUnder_eq

/-- The recurrence in DLMF 11.11(iii) has a removable singularity at lambda=1.
Proof: `A_k(λ) = (2πi)⁻¹ ∮ (t + λ sinh t)^{-(2k+1)} dt` near every `λ ≠ -1`
(`struveLO_angerScaledA_eq`), and the circle integrals are holomorphic in `λ`. -/
theorem angerScaledA_removable (k : ℕ) {lam : ℂ} (hlam : lam ≠ -1) :
    Tendsto (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))
      (𝓝[≠] lam) (𝓝 (angerScaledA (k+1) lam)) := by
  have h1 : 1 + lam ≠ 0 := fun h => hlam (by linear_combination h)
  obtain ⟨r, hr, ε, hε, hG⟩ := struveLO_good_exists h1
  have hm : lam ∈ Metric.ball lam ε := Metric.mem_ball_self hε
  rw [struveLO_angerScaledA_eq hr hG (k + 1) lam hm]
  exact struveLO_tendsto_quotient hr hG k _ (struveLO_angerScaledA_eq hr hG k) hm

/-- The convergent defining H series is also a generalized large-order expansion, DLMF 11.6(ii). -/
theorem struveH_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveH ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (-1)^n*(z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) :=
  struve_series_tail_isBigO (slitPlane_ne_zero hz) (by simp) hδ hδπ N (fun ν => struveHCore ν z)
    (fun ν => hasSum_struveHCore ν z)

/-- The corresponding generalized L expansion in DLMF 11.6(ii). -/
theorem struveL_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveL ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) := by
  have h := struve_series_tail_isBigO (slitPlane_ne_zero hz) (ε := 1) (by simp) hδ hδπ N
    (fun ν => struveLCore ν z) (fun ν => by simpa using hasSum_struveLCore ν z)
  simpa [struveL] using h

end DLMF.Struve

end
