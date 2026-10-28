/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.TurningPointEstimates

/-!
# Inner and turning-point Struve expansions

Turning-point estimates and inner-region expansions with uniform error bounds.

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

set_option maxHeartbeats 400000 in
/-- **The main estimate** behind DLMF 11.11.16. -/
theorem struveSc_turning_est {a : ℝ} (ha : |a| < π / 2) {K c0 : ℝ} (hK0 : 0 ≤ K) (hc0 : 0 < c0)
    (hc0a : c0 ≤ Real.cos a)
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖(1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K ∧
      ‖1 - (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * s)
    {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ‖(∫ r in Ioi (0 : ℝ), exp (-((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
          struveSc_phase 1 ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)))) *
          (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))) -
      ∫ r in Ioi (0 : ℝ), exp (-(((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
          exp (((-a : ℝ) : ℂ) * I) ^ 3 / 6) * (r : ℂ) ^ 3))‖ ≤
      (K * ((c0 / 24) ^ (-(2 / 3 : ℝ)) * (1 / 3) * Real.Gamma (2 / 3) + 1 / (c0 / 24) ^ 2) +
        (1 / 2 + K) / 5 * (1 / (3 * (c0 / 24) ^ 2) + 120 / (c0 / 24) ^ 6)) *
        ρ ^ (-(2 / 3 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set E : ℂ := exp (((-a : ℝ) : ℂ) * I) with hE
  set κ : ℝ := c0 / 24 with hκ
  have hκ0 : 0 < κ := by positivity
  set K₅ : ℝ := (1 / 2 + K) / 5 with hK₅
  have hK₅0 : 0 ≤ K₅ := by positivity
  set β : ℝ := κ * ρ with hβ
  have hβ0 : 0 < β := mul_pos hκ0 hρ0
  have hc := struveSc_cos_pos ha
  set q : ℝ → ℂ := fun s => (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)) with hq
  set Ψ : ℝ → ℂ := fun s => struveSc_phase 1 ((s : ℂ) * E) with hΨ
  set F : ℝ → ℂ := fun r => exp (-(ν * Ψ r)) * q r with hF
  set C : ℂ := ν * E ^ 3 / 6 with hC
  have hνE3 : ν * E ^ 3 = ((ρ : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) := by
    rw [hν, hE, ← exp_nat_mul, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  have hCre : C.re = ρ * Real.cos a / 6 := by
    rw [hC, hνE3, show ((ρ : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) / 6 =
      ((ρ / 6 : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) by push_cast; ring, re_ofReal_mul,
      exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  have hCpos : 0 < C.re := by rw [hCre]; positivity
  set G : ℝ → ℂ := fun r => exp (-(C * (r : ℂ) ^ 3)) with hG
  have hGi : IntegrableOn G (Ioi 0) := struveSc_integrableOn_exp_cube hCpos
  set H : ℝ → ℝ := fun r => (Real.exp (-(β * r ^ 3)) + Real.exp (-(β * r))) *
    (K * r + ρ * K₅ * r ^ 5) with hH
  -- pointwise bound
  have hbound : ∀ r : ℝ, 0 < r → ‖F r - G r‖ ≤ H r := by
    intro r hr
    set X : ℝ := Real.exp (-(c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2))))) with hX
    have hhr : 0 ≤ r ^ 3 / (12 * (1 + r ^ 2)) := by positivity
    have hre := struveSc_re_phase_one_ge ha hρ0.le hr.le
    rw [← hν] at hre
    have hA : (-(ν * Ψ r)).re ≤ -(c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2)))) := by
      rw [neg_re]; simp only [hΨ, hE]
      have : c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) ≤
          Real.cos a * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) := by gcongr
      linarith
    have hB : (-(C * (r : ℂ) ^ 3)).re ≤ -(c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2)))) := by
      rw [neg_re, ← ofReal_pow, re_mul_ofReal, hCre, neg_le_neg_iff]
      have h1 : r ^ 3 / (12 * (1 + r ^ 2)) ≤ r ^ 3 / 6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [pow_nonneg hr.le 3, mul_nonneg (pow_nonneg hr.le 3) (sq_nonneg r)]
      calc c0 * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) ≤ Real.cos a * ρ * (r ^ 3 / 6) := by gcongr
        _ = _ := by ring
    have hsplit : F r - G r = exp (-(ν * Ψ r)) * (q r - 1) +
        (exp (-(ν * Ψ r)) - exp (-(C * (r : ℂ) ^ 3))) := by
      simp only [hF, hG]; ring
    have h1 : ‖exp (-(ν * Ψ r))‖ ≤ X := by
      rw [norm_exp]; exact Real.exp_le_exp.2 hA
    have h2 : ‖q r - 1‖ ≤ K * r := by rw [norm_sub_rev]; exact (hK r hr.le).2
    have hcube := struveSc_phase_one_sub_cube ha (fun s hs => (hK s hs).1) hr.le
    have h3 : ‖-(ν * Ψ r) - -(C * (r : ℂ) ^ 3)‖ ≤ ρ * (K₅ * r ^ 5) := by
      have : -(ν * Ψ r) - -(C * (r : ℂ) ^ 3) = -(ν * (struveSc_phase 1 ((r : ℂ) * E) -
          ((r : ℂ) * E) ^ 3 / 6)) := by
        simp only [hΨ, hC]; ring
      rw [this, norm_neg, norm_mul, hν, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
        Real.norm_of_nonneg hρ0.le]
      exact mul_le_mul_of_nonneg_left hcube hρ0.le
    have h4 := struveSc_norm_exp_sub_exp_le hA hB
    have hXs := struveSc_exp_split hc0.le hρ0.le hr.le
    rw [hsplit]
    calc ‖exp (-(ν * Ψ r)) * (q r - 1) + (exp (-(ν * Ψ r)) - exp (-(C * (r : ℂ) ^ 3)))‖
        ≤ ‖exp (-(ν * Ψ r))‖ * ‖q r - 1‖ + ‖-(ν * Ψ r) - -(C * (r : ℂ) ^ 3)‖ * X := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]; gcongr
      _ ≤ X * (K * r) + ρ * (K₅ * r ^ 5) * X := by gcongr
      _ = X * (K * r + ρ * K₅ * r ^ 5) := by ring
      _ ≤ H r := by
          simp only [hH]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simpa [hX, hβ, hκ, mul_assoc] using hXs
  -- integrability of the majorant
  obtain ⟨i31, e31⟩ := struveSc_integral_pow_exp_cube 1 hβ0
  obtain ⟨i35, e35⟩ := struveSc_integral_pow_exp_cube 5 hβ0
  obtain ⟨i11, e11⟩ := struveSc_integral_pow_exp 1 hβ0
  obtain ⟨i15, e15⟩ := struveSc_integral_pow_exp 5 hβ0
  have hsplitH : ∀ r : ℝ, H r = (K * (Real.exp (-(β * r ^ 3)) * r ^ 1) +
      ρ * K₅ * (Real.exp (-(β * r ^ 3)) * r ^ 5)) +
      (K * (Real.exp (-(β * r)) * r ^ 1) + ρ * K₅ * (Real.exp (-(β * r)) * r ^ 5)) := by
    intro r; simp only [hH, pow_one]; ring
  have j1 := (i31.const_mul K).add (i35.const_mul (ρ * K₅))
  have j2 := (i11.const_mul K).add (i15.const_mul (ρ * K₅))
  have hHi : IntegrableOn H (Ioi 0) := by
    refine IntegrableOn.congr_fun (j1.add j2) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; exact (hsplitH r).symm
  have k1 := integral_add (i31.const_mul K) (i35.const_mul (ρ * K₅))
  have k2 := integral_add (i11.const_mul K) (i15.const_mul (ρ * K₅))
  have k3 := integral_add j1 j2
  simp only [Pi.add_apply] at k3
  have hHint : ∫ r in Ioi (0 : ℝ), H r =
      (K * (β ^ (-(2 / 3 : ℝ)) * (1 / 3) * Real.Gamma (2 / 3)) + ρ * K₅ * (1 / (3 * β ^ 2))) +
      (K * (1 / β ^ 2) + ρ * K₅ * (120 / β ^ 6)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hsplitH r), k3, k1, k2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      e31, e35, e11, e15]
    have g2 : Real.Gamma ((((5 : ℕ) : ℝ) + 1) / 3) = 1 := by
      rw [show (((5 : ℕ) : ℝ) + 1) / 3 = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero,
        Real.Gamma_one, mul_one]
    have b2 : β ^ (-(((5 : ℕ) : ℝ) + 1) / 3) = 1 / β ^ 2 := by
      rw [show (-(((5 : ℕ) : ℝ) + 1) / 3) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hβ0.le,
        Real.rpow_natCast, one_div]
    rw [g2, b2, show (-(((1 : ℕ) : ℝ) + 1) / 3) = -(2 / 3 : ℝ) by norm_num,
      show (((1 : ℕ) : ℝ) + 1) / 3 = 2 / 3 by norm_num]
    norm_num [Nat.factorial]
  -- continuity and integrability of `F`
  have hFc : ContinuousOn F (Ioi 0) := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
    have hΨc : ContinuousAt Ψ r := (struveSc_hasDerivAt_phase_ray 1 ha hr0).continuousAt
    have hqc : ContinuousAt q r :=
      ((by fun_prop : Continuous fun s : ℝ => 1 + ((s : ℂ) * E) ^ 2).continuousAt).cpow
        continuousAt_const (struveSc_mem_slitPlane ha)
    exact ((continuous_exp.continuousAt.comp (hΨc.const_mul ν).neg).mul hqc).continuousWithinAt
  have hdm : AEStronglyMeasurable (fun r => F r - G r) (volume.restrict (Ioi 0)) :=
    (hFc.sub (by fun_prop : Continuous G).continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hdi : IntegrableOn (fun r => F r - G r) (Ioi 0) :=
    Integrable.mono' hHi hdm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => hbound r hr))
  have hFi : IntegrableOn F (Ioi 0) := by
    have : IntegrableOn (fun r => (F r - G r) + G r) (Ioi 0) := hdi.add hGi
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp
  -- assemble
  change ‖(∫ r in Ioi (0 : ℝ), F r) - ∫ r in Ioi (0 : ℝ), G r‖ ≤ _
  rw [← integral_sub hFi hGi]
  refine (norm_integral_le_of_norm_le hHi ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun r hr => hbound r hr))).trans ?_
  rw [hHint]
  -- comparison of powers of `ρ`
  have hm1 : ρ ^ (-(1 : ℝ)) ≤ ρ ^ (-(2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  rw [Real.rpow_neg_one] at hm1
  have hinv : 0 < ρ⁻¹ := inv_pos.2 hρ0
  have hinv1 : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
  have hp2 : 1 / β ^ 2 = 1 / κ ^ 2 * ρ⁻¹ * ρ⁻¹ := by rw [hβ]; field_simp
  have hp6 : 1 / β ^ 6 = 1 / κ ^ 6 * ρ⁻¹ ^ 6 := by rw [hβ]; field_simp
  have hp23 : β ^ (-(2 / 3 : ℝ)) = κ ^ (-(2 / 3 : ℝ)) * ρ ^ (-(2 / 3 : ℝ)) := by
    rw [hβ, Real.mul_rpow hκ0.le hρ0.le]
  have hρρ : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
  have hr5 : ρ⁻¹ ^ 5 ≤ ρ⁻¹ := by
    calc ρ⁻¹ ^ 5 ≤ ρ⁻¹ ^ 1 := pow_le_pow_of_le_one hinv.le hinv1 (by norm_num)
      _ = ρ⁻¹ := pow_one _
  have hr2 : ρ⁻¹ * ρ⁻¹ ≤ ρ⁻¹ := by nlinarith
  set t : ℝ := ρ ^ (-(2 / 3 : ℝ)) with ht
  have hG23 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hk23 : 0 < κ ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hκ0 _
  have e1 : ρ * K₅ * (1 / (3 * β ^ 2)) = K₅ * (1 / (3 * κ ^ 2)) * ρ⁻¹ := by
    rw [hβ]; field_simp
  have e2 : ρ * K₅ * (120 / β ^ 6) = K₅ * (120 / κ ^ 6) * ρ⁻¹ ^ 5 := by
    rw [hβ]; field_simp
  rw [hp23, e1, e2, hp2]
  have hk2 : 0 ≤ 1 / κ ^ 2 := by positivity
  have hk6 : 0 ≤ 120 / κ ^ 6 := by positivity
  have hk32 : 0 ≤ 1 / (3 * κ ^ 2) := by positivity
  have a1 : K * (1 / κ ^ 2 * ρ⁻¹ * ρ⁻¹) ≤ K * (1 / κ ^ 2) * t := by
    rw [mul_assoc (1 / κ ^ 2)]
    have := mul_le_mul_of_nonneg_left (hr2.trans hm1) (mul_nonneg hK0 hk2)
    linarith [this]
  have a2 : K₅ * (1 / (3 * κ ^ 2)) * ρ⁻¹ ≤ K₅ * (1 / (3 * κ ^ 2)) * t :=
    mul_le_mul_of_nonneg_left hm1 (mul_nonneg hK₅0 hk32)
  have a3 : K₅ * (120 / κ ^ 6) * ρ⁻¹ ^ 5 ≤ K₅ * (120 / κ ^ 6) * t :=
    mul_le_mul_of_nonneg_left (hr5.trans hm1) (mul_nonneg hK₅0 hk6)
  nlinarith [a1, a2, a3]

/-- `π⁻¹ Γ(4/3) 6^{1/3} = 2^{4/3}/(3^{7/6} Γ(2/3))`. -/
theorem struveSc_const_turn :
    1 / π * Real.Gamma (4 / 3) * (1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) =
      2 ^ (4 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) := by
  have h := struveTP_const_E
  rw [Real.sin_pi_div_six] at h
  have h2 : (2 : ℝ) ^ (4 / 3 : ℝ) = 2 * 2 ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [h2, mul_div_assoc, ← h]
  ring

/-- The DLMF 11.11.16 right-hand side as the Gamma-integral leading term. -/
theorem struveSc_turning_rhs {a : ℝ} (ha : |a| < π / 2) {ρ : ℝ} (hρ : 0 < ρ) :
    (2 : ℂ) ^ (4 / 3 : ℂ) / ((3 : ℂ) ^ (7 / 6 : ℂ) * Gamma (2 / 3) *
        ((ρ : ℂ) * exp ((2 * a : ℝ) * I)) ^ (1 / 3 : ℂ)) =
      1 / π * (exp (((-a : ℝ) : ℂ) * I) * (Gamma (4 / 3) *
        ((ρ : ℂ) * exp ((2 * a : ℝ) * I) * exp (((-a : ℝ) : ℂ) * I) ^ 3 / 6) ^
          (-(1 / 3 : ℂ)))) := by
  have hb1 : -π < a := by linarith [neg_abs_le a, Real.pi_pos]
  have hb2 : a < π := by linarith [le_abs_self a, Real.pi_pos]
  have hc1 : -π < 2 * a := by linarith [neg_abs_le a]
  have hc2 : 2 * a ≤ π := by linarith [le_abs_self a]
  have hνE3 : (ρ : ℂ) * exp ((2 * a : ℝ) * I) * exp (((-a : ℝ) : ℂ) * I) ^ 3 / 6 =
      ((ρ / 6 : ℝ) : ℂ) * exp (((-a : ℝ) : ℂ) * I) := by
    rw [← exp_nat_mul, mul_assoc, ← exp_add]; push_cast; ring_nf
  rw [hνE3, ofReal_mul_exp_cpow (r := ρ / 6) (by positivity) (θ := -a) (by linarith)
    (by linarith), ofReal_mul_exp_cpow hρ hc1 hc2]
  have e1 : ((ρ / 6 : ℝ) : ℂ) ^ (-(1 / 3 : ℂ)) = (((ρ / 6) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; rfl
  have e2 : (ρ : ℂ) ^ (1 / 3 : ℂ) = ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow hρ.le]; push_cast; rfl
  have e3 : (2 : ℂ) ^ (4 / 3 : ℂ) = ((2 ^ (4 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  have e4 : (3 : ℂ) ^ (7 / 6 : ℂ) = ((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  have e5 : Gamma (2 / 3 : ℂ) = ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have e6 : Gamma (4 / 3 : ℂ) = ((Real.Gamma (4 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hx1 : exp (((-a : ℝ) : ℂ) * I * -(1 / 3 : ℂ)) = exp (((a / 3 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have hx2 : exp (((2 * a : ℝ) : ℂ) * I * (1 / 3 : ℂ)) = exp (((2 * a / 3 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, hx1, hx2]
  have hρ6 : (ρ / 6) ^ (-(1 / 3 : ℝ)) * ρ ^ (1 / 3 : ℝ) = (1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [show ρ / 6 = 1 / 6 * ρ by ring, Real.mul_rpow (by norm_num) hρ.le, mul_assoc,
      ← Real.rpow_add hρ, show -(1 / 3 : ℝ) + 1 / 3 = 0 by ring, Real.rpow_zero, mul_one]
  have hk := struveSc_const_turn
  have hexp : exp (((-a : ℝ) : ℂ) * I) * exp (((a / 3 : ℝ) : ℂ) * I) *
      exp (((2 * a / 3 : ℝ) : ℂ) * I) = 1 := by
    rw [← exp_add, ← exp_add]; push_cast; ring_nf; exact exp_zero
  have hG : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : 0 < (3 : ℝ) ^ (7 / 6 : ℝ) := by positivity
  have hr3 : 0 < ρ ^ (1 / 3 : ℝ) := by positivity
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have hne : ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) * exp (((2 * a / 3 : ℝ) : ℂ) * I) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.2 hr3.ne') (exp_ne_zero _)
  have h3c : ((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h3.ne'
  have hGc : ((Real.Gamma (2 / 3) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hG.ne'
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero h3c hGc) hne)]
  have hk' : ((2 ^ (4 / 3 : ℝ) : ℝ) : ℂ) = 1 / π * ((Real.Gamma (4 / 3) : ℝ) : ℂ) *
      (((ρ / 6) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) * ((Real.Gamma (2 / 3) : ℝ) : ℂ)) := by
    have : 2 ^ (4 / 3 : ℝ) = 1 / π * Real.Gamma (4 / 3) * ((ρ / 6) ^ (-(1 / 3 : ℝ)) *
        ρ ^ (1 / 3 : ℝ)) * (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) := by
      rw [hρ6, hk]; field_simp
    rw [this]; push_cast; ring
  rw [hk']
  linear_combination (-1 / π * ((Real.Gamma (4 / 3) : ℝ) : ℂ) *
      (((ρ / 6) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ((ρ ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (((3 ^ (7 / 6 : ℝ) : ℝ) : ℂ) * ((Real.Gamma (2 / 3) : ℝ) : ℂ))) * hexp

/-- The norm of the DLMF 11.11.16 right-hand side. -/
theorem struveSc_norm_turning_rhs (ν : ℂ) :
    ‖(2 : ℂ) ^ (4 / 3 : ℂ) / ((3 : ℂ) ^ (7 / 6 : ℂ) * Gamma (2 / 3) * ν ^ (1 / 3 : ℂ))‖ =
      2 ^ (4 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) / ‖ν‖ ^ (1 / 3 : ℝ) := by
  have e5 : Gamma (2 / 3 : ℂ) = ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hG : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  rw [e5, norm_div, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hG.le,
    show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl,
    show (7 / 6 : ℂ) = ((7 / 6 : ℝ) : ℂ) by push_cast; rfl,
    show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_real, norm_cpow_real, norm_cpow_real]
  simp only [Complex.norm_ofNat]
  ring

/-- The real phase `φ(s) = λ s - arsinh s` of `𝐀_{-ν}(λν)` on the positive axis. -/
noncomputable def struveSc_phiR (lam s : ℝ) : ℝ := lam * s - Real.arsinh s

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.sqrt (1 + s ^ 2)`. -/
theorem struveSc_sqrt_pos (s : ℝ) : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s
^ 2`. -/
theorem struveSc_sqrt_sq (s : ℝ) : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Estimate under the stated parameter and domain assumptions: `1 ≤ Real.sqrt (1 + s ^ 2)`. -/
theorem struveSc_one_le_sqrt (s : ℝ) : 1 ≤ Real.sqrt (1 + s ^ 2) := by
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + s ^ 2 by nlinarith)
  rwa [Real.sqrt_one] at this

/-- Estimate under the stated parameter and domain assumptions: `|s| ≤ Real.sqrt (1 + s ^ 2)`. -/
theorem struveSc_abs_le_sqrt (s : ℝ) : |s| ≤ Real.sqrt (1 + s ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)

/-- At `s`, the function `(fun s : ℝ => Real.sqrt (1 + s ^ 2))` has derivative `(s / Real.sqrt (1
+ s ^ 2))`. -/
theorem struveSc_hasDerivAt_sqrt (s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2)) (s / Real.sqrt (1 + s ^ 2)) s := by
  have h := ((hasDerivAt_pow 2 s).const_add 1).sqrt (by positivity)
  convert h using 1
  have := struveSc_sqrt_pos s
  field_simp
  push_cast; ring

/-- At `s`, the function `(struveSc_phiR lam)` has derivative `(lam - (Real.sqrt (1 + s ^ 2))⁻¹)`. -/
theorem struveSc_hasDerivAt_phiR (lam s : ℝ) :
    HasDerivAt (struveSc_phiR lam) (lam - (Real.sqrt (1 + s ^ 2))⁻¹) s := by
  have h := ((hasDerivAt_id s).const_mul lam).sub (Real.hasDerivAt_arsinh s)
  exact h.congr_deriv (by simp)

/-- At `s`, the function `(fun s : ℝ => lam - (Real.sqrt (1 + s ^ 2))⁻¹)` has derivative `(s /
Real.sqrt (1 + s ^ 2) ^ 3)`. -/
theorem struveSc_hasDerivAt_phiR' (lam s : ℝ) :
    HasDerivAt (fun s : ℝ => lam - (Real.sqrt (1 + s ^ 2))⁻¹)
      (s / Real.sqrt (1 + s ^ 2) ^ 3) s := by
  have hS := struveSc_sqrt_pos s
  have h := ((struveSc_hasDerivAt_sqrt s).inv hS.ne').const_sub lam
  convert h using 1
  field_simp

/-- At `s`, the function `(fun s : ℝ => s / Real.sqrt (1 + s ^ 2) ^ 3)` has derivative `((1 - 2 *
s ^ 2) / Real.sqrt (1 + s ^ 2) ^ 5)`. -/
theorem struveSc_hasDerivAt_phiR'' (s : ℝ) :
    HasDerivAt (fun s : ℝ => s / Real.sqrt (1 + s ^ 2) ^ 3)
      ((1 - 2 * s ^ 2) / Real.sqrt (1 + s ^ 2) ^ 5) s := by
  have hS := struveSc_sqrt_pos s
  have h := (hasDerivAt_id s).div ((struveSc_hasDerivAt_sqrt s).pow 3) (pow_pos hS 3).ne'
  refine h.congr_deriv ?_
  have h2 := struveSc_sqrt_sq s
  simp only [id, Pi.pow_apply]
  field_simp
  norm_num
  rw [show Real.sqrt (1 + s ^ 2) ^ 4 = (Real.sqrt (1 + s ^ 2) ^ 2) ^ 2 by ring, h2]
  ring

/-- Estimate under the stated parameter and domain assumptions: `|(1 - 2 * s ^ 2) / Real.sqrt (1 +
s ^ 2) ^ 5| ≤ 1`. -/
theorem struveSc_abs_phiR''' (s : ℝ) : |(1 - 2 * s ^ 2) / Real.sqrt (1 + s ^ 2) ^ 5| ≤ 1 := by
  have hS := struveSc_sqrt_pos s
  have h1 := struveSc_one_le_sqrt s
  have h2 := struveSc_sqrt_sq s
  rw [abs_div, abs_of_pos (pow_pos hS 5), div_le_one (pow_pos hS 5)]
  have h4 : Real.sqrt (1 + s ^ 2) ^ 4 ≤ Real.sqrt (1 + s ^ 2) ^ 5 :=
    pow_le_pow_right₀ h1 (by norm_num)
  have h5 : Real.sqrt (1 + s ^ 2) ^ 4 = (1 + s ^ 2) ^ 2 := by
    rw [show Real.sqrt (1 + s ^ 2) ^ 4 = (Real.sqrt (1 + s ^ 2) ^ 2) ^ 2 by ring, h2]
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg s, pow_nonneg (sq_nonneg s) 2]

/-- `φ''` is `1`-Lipschitz. -/
theorem struveSc_phiR''_lip (u v : ℝ) :
    |u / Real.sqrt (1 + u ^ 2) ^ 3 - v / Real.sqrt (1 + v ^ 2) ^ 3| ≤ |u - v| := by
  have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => s / Real.sqrt (1 + s ^ 2) ^ 3)
    (f' := fun s => (1 - 2 * s ^ 2) / Real.sqrt (1 + s ^ 2) ^ 5) (C := 1)
    (fun x _ => (struveSc_hasDerivAt_phiR'' x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact struveSc_abs_phiR''' x)
    (mem_univ v) (mem_univ u)
  simpa [Real.norm_eq_abs] using this

/-- Quadratic Taylor bound for `φ` at a critical point. -/
theorem struveSc_phiR_taylor {lam s₀ : ℝ} (hcrit : lam = (Real.sqrt (1 + s₀ ^ 2))⁻¹) (t : ℝ) :
    |struveSc_phiR lam (s₀ + t) - struveSc_phiR lam s₀ -
      s₀ / Real.sqrt (1 + s₀ ^ 2) ^ 3 / 2 * t ^ 2| ≤ |t| ^ 3 := by
  set c₂ := s₀ / Real.sqrt (1 + s₀ ^ 2) ^ 3 with hc₂
  -- first derivative bound
  have h1 : ∀ x : ℝ, |lam - (Real.sqrt (1 + (s₀ + x) ^ 2))⁻¹ - c₂ * x| ≤ x ^ 2 := by
    intro x
    have := (convex_uIcc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y : ℝ => lam - (Real.sqrt (1 + (s₀ + y) ^ 2))⁻¹ - c₂ * y)
      (f' := fun y => (s₀ + y) / Real.sqrt (1 + (s₀ + y) ^ 2) ^ 3 - c₂) (C := |x|)
      (fun y _ => by
        have h := (struveSc_hasDerivAt_phiR' lam (s₀ + y)).comp y ((hasDerivAt_id y).const_add s₀)
        have h2 := h.sub ((hasDerivAt_id y).const_mul c₂)
        exact (h2.congr_deriv (by simp)).hasDerivWithinAt)
      (fun y hy => by
        rw [Real.norm_eq_abs]
        have := struveSc_phiR''_lip (s₀ + y) s₀
        rw [show s₀ + y - s₀ = y by ring] at this
        have hy' := abs_sub_left_of_mem_uIcc hy
        simp only [sub_zero] at hy'
        exact this.trans hy')
      (left_mem_uIcc) (right_mem_uIcc)
    simp only [add_zero, mul_zero, sub_zero, Real.norm_eq_abs] at this
    rw [← hcrit, sub_self, sub_zero] at this
    calc _ ≤ |x| * |x| := this
      _ = x ^ 2 := by rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg x)]
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => struveSc_phiR lam (s₀ + y) - struveSc_phiR lam s₀ - c₂ / 2 * y ^ 2)
    (f' := fun y => lam - (Real.sqrt (1 + (s₀ + y) ^ 2))⁻¹ - c₂ * y) (C := t ^ 2)
    (fun y _ => by
      have h := (struveSc_hasDerivAt_phiR lam (s₀ + y)).comp y ((hasDerivAt_id y).const_add s₀)
      have h2 := (h.sub_const (struveSc_phiR lam s₀)).sub ((hasDerivAt_pow 2 y).const_mul (c₂ / 2))
      exact (h2.congr_deriv (by simp; ring)).hasDerivWithinAt)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      have hy' := abs_sub_left_of_mem_uIcc hy
      simp only [sub_zero] at hy'
      refine (h1 y).trans ?_
      rw [← sq_abs y, ← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg _) hy' 2)
    (left_mem_uIcc) (right_mem_uIcc)
  simp only [add_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sub_zero, Real.norm_eq_abs] at this
  calc _ ≤ t ^ 2 * |t| := this
    _ = |t| ^ 3 := by rw [← sq_abs t]; ring

/-- The saddle `s₀ = √(1-λ²)/λ` satisfies `√(1+s₀²) = 1/λ`. -/
theorem struveSc_sqrt_saddle {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    Real.sqrt (1 + (Real.sqrt (1 - lam ^ 2) / lam) ^ 2) = lam⁻¹ := by
  have hs : Real.sqrt (1 - lam ^ 2) ^ 2 = 1 - lam ^ 2 := Real.sq_sqrt (by nlinarith)
  rw [div_pow, hs, show 1 + (1 - lam ^ 2) / lam ^ 2 = lam⁻¹ ^ 2 by field_simp; ring,
    Real.sqrt_sq (inv_pos.2 h0).le]

/-- Monotonicity of `φ` on both sides of the critical point. -/
theorem struveSc_phiR_mono {lam s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hcrit : lam = (Real.sqrt (1 + s₀ ^ 2))⁻¹) :
    MonotoneOn (struveSc_phiR lam) (Ici s₀) ∧ AntitoneOn (struveSc_phiR lam) (Icc 0 s₀) := by
  have hS : ∀ s, 0 < Real.sqrt (1 + s ^ 2) := struveSc_sqrt_pos
  constructor
  · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici s₀)
      (f' := fun s => lam - (Real.sqrt (1 + s ^ 2))⁻¹)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).continuousAt.continuousWithinAt)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).hasDerivWithinAt) ?_
    intro s hs
    rw [interior_Ici] at hs
    have hss : s₀ ≤ s := le_of_lt hs
    have : Real.sqrt (1 + s₀ ^ 2) ≤ Real.sqrt (1 + s ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [hcrit, sub_nonneg]
    exact inv_anti₀ (hS s₀) this
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 s₀)
      (f' := fun s => lam - (Real.sqrt (1 + s ^ 2))⁻¹)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).continuousAt.continuousWithinAt)
      (fun s _ => (struveSc_hasDerivAt_phiR lam s).hasDerivWithinAt) ?_
    intro s hs
    rw [interior_Icc] at hs
    have : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt (1 + s₀ ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hs.1, hs.2])
    rw [hcrit, sub_nonpos]
    exact inv_anti₀ (hS s) this

/-- Identity under the stated parameter and domain assumptions: `(1 + (s : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
((Real.sqrt (1 + s ^ 2) : ℝ) : ℂ)`. -/
theorem struveSc_cpow_half_ofReal (s : ℝ) :
    (1 + (s : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 + s ^ 2) : ℝ) : ℂ) := by
  rw [show 1 + (s : ℂ) ^ 2 = ((1 + s ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow (by positivity),
    Real.sqrt_eq_rpow]

/-- Identity under the stated parameter and domain assumptions: `(1 + (s : ℂ) ^ 2) ^ (-(1 / 2 :
ℂ)) = (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ)`. -/
theorem struveSc_q_ofReal (s : ℝ) :
    (1 + (s : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
  rw [cpow_neg, struveSc_cpow_half_ofReal, ofReal_inv]

/-- Identity under the stated parameter and domain assumptions: `struveSc_phase lam (s : ℂ) =
((struveSc_phiR lam s : ℝ) : ℂ)`. -/
theorem struveSc_phase_ofReal (lam s : ℝ) :
    struveSc_phase lam (s : ℂ) = ((struveSc_phiR lam s : ℝ) : ℂ) := by
  have hpos : 0 < s + Real.sqrt (1 + s ^ 2) := by
    have := struveSc_abs_le_sqrt s
    have h2 : Real.sqrt (1 + s ^ 2) ≠ |s| := by
      intro h
      have := struveSc_sqrt_sq s
      rw [h, sq_abs] at this; linarith
    have := lt_of_le_of_ne this h2.symm
    linarith [neg_abs_le s]
  rw [struveSc_phase, struveSc_cpow_half_ofReal, ← ofReal_add, ← ofReal_log hpos.le,
    struveSc_phiR, Real.arsinh]
  push_cast; ring

/-- DLMF 11.10.4 on the real contour, written with the real phase. -/
theorem struveSc_angerA_real {lam : ℝ} (hlam : 0 < lam) {ν : ℂ} (hν : 0 < ν.re) :
    angerA (-ν) (lam * ν) = 1 / π * ∫ s in Ioi (0 : ℝ),
      exp (-(ν * ((struveSc_phiR lam s : ℝ) : ℂ))) * (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
  have ha : |(0 : ℝ)| < π / 2 := by rw [abs_zero]; positivity
  have hθ : |(-(0 : ℝ))| < π / 2 := by rw [neg_zero, abs_zero]; positivity
  have hz : 0 < ((lam : ℂ) * ν * exp (((-(0 : ℝ) : ℝ) : ℂ) * I)).re := by
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [re_ofReal_mul]; exact mul_pos hlam hν
  rw [struveAs_angerA_eq_rot (-ν) hθ hz, struveAs_rotInt]
  have hint : (∫ r in Ioi (0 : ℝ), exp (-((lam : ℂ) * ν * exp (((-(0 : ℝ) : ℝ) : ℂ) * I) * r)) *
      struveAs_kernel (-ν) ((r : ℂ) * exp (((-(0 : ℝ) : ℝ) : ℂ) * I))) =
      ∫ s in Ioi (0 : ℝ), exp (-(ν * ((struveSc_phiR lam s : ℝ) : ℂ))) *
        (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [struveSc_integrand_eq lam ha ν (le_of_lt hr)]
    simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, mul_one]
    rw [struveSc_phase_ofReal, struveSc_q_ofReal]
  rw [hint]
  simp only [neg_zero, ofReal_zero, zero_mul, exp_zero, one_mul]

/-- The saddle point `s₀ = √(1-λ²)/λ` of the real phase. -/
noncomputable def struveSc_s0 (lam : ℝ) : ℝ := Real.sqrt (1 - lam ^ 2) / lam

/-- Half the second derivative of the phase at the saddle, `φ''(s₀)/2 = s₀ λ³/2`. -/
noncomputable def struveSc_Q0 (lam : ℝ) : ℝ := struveSc_s0 lam * lam ^ 3 / 2

/-- The quadratic phase coefficient `(φ(s₀+t) - φ(s₀))/t²`, extended by `Q₀` at `0`. -/
noncomputable def struveSc_Qf (lam t : ℝ) : ℝ :=
  if t = 0 then struveSc_Q0 lam else
    (struveSc_phiR lam (struveSc_s0 lam + t) - struveSc_phiR lam (struveSc_s0 lam)) / t ^ 2

/-- Estimate under the stated parameter and domain assumptions: `0 < struveSc_s0 lam`. -/
theorem struveSc_s0_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : 0 < struveSc_s0 lam :=
  div_pos (Real.sqrt_pos.2 (by nlinarith)) h0

/-- Identity under the stated parameter and domain assumptions: `lam = (Real.sqrt (1 + struveSc_s0
lam ^ 2))⁻¹`. -/
theorem struveSc_crit {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    lam = (Real.sqrt (1 + struveSc_s0 lam ^ 2))⁻¹ := by
  rw [struveSc_s0, struveSc_sqrt_saddle h0 h1, inv_inv]

/-- Identity under the stated parameter and domain assumptions: `struveSc_s0 lam / Real.sqrt (1 +
struveSc_s0 lam ^ 2) ^ 3 / 2 = struveSc_Q0 lam`. -/
theorem struveSc_c2 {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    struveSc_s0 lam / Real.sqrt (1 + struveSc_s0 lam ^ 2) ^ 3 / 2 = struveSc_Q0 lam := by
  rw [struveSc_Q0, struveSc_s0, struveSc_sqrt_saddle h0 h1]
  field_simp

/-- Estimate under the stated parameter and domain assumptions: `0 < struveSc_Q0 lam`. -/
theorem struveSc_Q0_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : 0 < struveSc_Q0 lam := by
  have := struveSc_s0_pos h0 h1
  rw [struveSc_Q0]; positivity

/-- Estimate under the stated parameter and domain assumptions: `struveSc_Q0 lam < struveSc_s0
lam`. -/
theorem struveSc_Q0_lt {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    struveSc_Q0 lam < struveSc_s0 lam := by
  have := struveSc_s0_pos h0 h1
  have h3 : lam ^ 3 < 1 := pow_lt_one₀ h0.le h1 (by norm_num)
  rw [struveSc_Q0]; nlinarith

/-- Identity under the stated parameter and domain assumptions: `struveSc_phiR lam (struveSc_s0
lam + t) - struveSc_phiR lam (struveSc_s0 lam) = t ^ 2 * struveSc_Qf lam t`. -/
theorem struveSc_D_eq {lam : ℝ} (t : ℝ) :
    struveSc_phiR lam (struveSc_s0 lam + t) - struveSc_phiR lam (struveSc_s0 lam) =
      t ^ 2 * struveSc_Qf lam t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · simp only [struveSc_Qf, ht, ↓reduceIte]; field_simp

/-- Estimate under the stated parameter and domain assumptions: `|struveSc_phiR lam (struveSc_s0
lam + t) - struveSc_phiR lam (struveSc_s0 lam) - struveSc_Q0 lam * t ^ 2| ≤ |t| ^ 3`. -/
theorem struveSc_D_taylor {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (t : ℝ) :
    |struveSc_phiR lam (struveSc_s0 lam + t) - struveSc_phiR lam (struveSc_s0 lam) -
      struveSc_Q0 lam * t ^ 2| ≤ |t| ^ 3 := by
  have := struveSc_phiR_taylor (struveSc_crit h0 h1) t
  rwa [struveSc_c2 h0 h1] at this

/-- Estimate under the stated parameter and domain assumptions: `|struveSc_Qf lam t - struveSc_Q0
lam| ≤ |t|`. -/
theorem struveSc_Qf_lip {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (t : ℝ) :
    |struveSc_Qf lam t - struveSc_Q0 lam| ≤ |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [struveSc_Qf]
  · have h := struveSc_D_taylor h0 h1 t
    rw [struveSc_D_eq] at h
    have ht2 : 0 < t ^ 2 := by positivity
    rw [show t ^ 2 * struveSc_Qf lam t - struveSc_Q0 lam * t ^ 2 =
      t ^ 2 * (struveSc_Qf lam t - struveSc_Q0 lam) by ring, abs_mul,
      abs_of_pos ht2, show |t| ^ 3 = t ^ 2 * |t| by rw [← sq_abs t]; ring] at h
    exact le_of_mul_le_mul_left h ht2

/-- Estimate under the stated parameter and domain assumptions: `|(Real.sqrt (1 + (struveSc_s0 lam
+ t) ^ 2))⁻¹ - lam| ≤ |t|`. -/
theorem struveSc_amp_lip {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (t : ℝ) :
    |(Real.sqrt (1 + (struveSc_s0 lam + t) ^ 2))⁻¹ - lam| ≤ |t| := by
  have hcrit := struveSc_crit h0 h1
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => lam - (Real.sqrt (1 + (struveSc_s0 lam + y) ^ 2))⁻¹)
    (f' := fun y => (struveSc_s0 lam + y) / Real.sqrt (1 + (struveSc_s0 lam + y) ^ 2) ^ 3)
    (C := 1)
    (fun y _ => by
      have h := (struveSc_hasDerivAt_phiR' lam (struveSc_s0 lam + y)).comp y
        ((hasDerivAt_id y).const_add (struveSc_s0 lam))
      exact (h.congr_deriv (by simp)).hasDerivWithinAt)
    (fun y _ => by
      set u := struveSc_s0 lam + y
      have hS := struveSc_sqrt_pos u
      have hle := struveSc_abs_le_sqrt u
      have h1' := struveSc_one_le_sqrt u
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hS 3), div_le_one (pow_pos hS 3)]
      calc |u| ≤ Real.sqrt (1 + u ^ 2) := hle
        _ ≤ Real.sqrt (1 + u ^ 2) ^ 3 := by
          calc Real.sqrt (1 + u ^ 2) = Real.sqrt (1 + u ^ 2) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ h1' (by norm_num))
    (left_mem_uIcc) (right_mem_uIcc)
  simp only [add_zero, sub_zero, Real.norm_eq_abs] at this
  rw [← hcrit, sub_self, sub_zero, abs_sub_comm] at this
  simpa [abs_sub_comm] using this

/-- Estimate under the stated parameter and domain assumptions: `struveSc_phiR lam (struveSc_s0
lam) ≤ struveSc_phiR lam s`. -/
theorem struveSc_phiR_ge {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {s : ℝ} (hs : 0 ≤ s) :
    struveSc_phiR lam (struveSc_s0 lam) ≤ struveSc_phiR lam s := by
  have hs0 := struveSc_s0_pos h0 h1
  obtain ⟨hm, ha⟩ := struveSc_phiR_mono hs0.le (struveSc_crit h0 h1)
  rcases le_total s (struveSc_s0 lam) with h | h
  · exact ha ⟨hs, h⟩ ⟨hs0.le, le_rfl⟩ h
  · exact hm (mem_Ici.2 le_rfl) (mem_Ici.2 h) h

/-- The phase gap away from the saddle. -/
theorem struveSc_phiR_gap {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {s : ℝ} (hs : 0 ≤ s)
    (hout : s ∉ Icc (struveSc_s0 lam - struveSc_Q0 lam / 2) (struveSc_s0 lam + struveSc_Q0 lam / 2)) :
    struveSc_phiR lam (struveSc_s0 lam) + struveSc_Q0 lam * (struveSc_Q0 lam / 2) ^ 2 / 2 ≤
      struveSc_phiR lam s := by
  set s₀ := struveSc_s0 lam with hs₀
  set Q0 := struveSc_Q0 lam with hQ0
  have hs0 := struveSc_s0_pos h0 h1
  have hQ := struveSc_Q0_pos h0 h1
  have hQs := struveSc_Q0_lt h0 h1
  obtain ⟨hm, ha⟩ := struveSc_phiR_mono hs0.le (struveSc_crit h0 h1)
  have key : ∀ t : ℝ, |t| = Q0 / 2 → struveSc_phiR lam s₀ + Q0 * (Q0 / 2) ^ 2 / 2 ≤
      struveSc_phiR lam (s₀ + t) := by
    intro t ht
    have h := struveSc_D_taylor h0 h1 t
    rw [← hs₀, ← hQ0, ht] at h
    have ht2 : t ^ 2 = (Q0 / 2) ^ 2 := by rw [← sq_abs, ht]
    rw [ht2] at h
    have := (abs_le.1 h).1
    nlinarith
  rw [mem_Icc, not_and_or, not_le, not_le] at hout
  rcases hout with h | h
  · have hk := key (-(Q0 / 2)) (by rw [abs_neg, abs_of_pos (by positivity)])
    have := ha ⟨hs, by linarith⟩ ⟨by linarith, by linarith⟩ (show s ≤ s₀ + -(Q0 / 2) by linarith)
    linarith
  · have hk := key (Q0 / 2) (abs_of_pos (by positivity))
    have := hm (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith))
      (show s₀ + Q0 / 2 ≤ s by linarith)
    linarith

/-- An integrable majorant for `e^{-(φ - φ₀)} (1+s²)^{-1/2}`. -/
theorem struveSc_W_le {lam : ℝ} {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    Real.exp (-(struveSc_phiR lam s - c)) * (Real.sqrt (1 + s ^ 2))⁻¹ ≤
      Real.exp c * (Real.exp (-(lam * s)) * (1 + 2 * s)) := by
  have hS := struveSc_sqrt_pos s
  have h1 := struveSc_one_le_sqrt s
  have hS1 : Real.sqrt (1 + s ^ 2) ≤ 1 + s := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have he : Real.exp (-(struveSc_phiR lam s - c)) =
      Real.exp c * (Real.exp (-(lam * s)) * (s + Real.sqrt (1 + s ^ 2))) := by
    rw [struveSc_phiR, ← Real.exp_arsinh, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hk : (s + Real.sqrt (1 + s ^ 2)) * (Real.sqrt (1 + s ^ 2))⁻¹ ≤ 1 + 2 * s := by
    calc (s + Real.sqrt (1 + s ^ 2)) * (Real.sqrt (1 + s ^ 2))⁻¹ ≤
          (s + Real.sqrt (1 + s ^ 2)) * 1 := by
          gcongr; exact inv_le_one_of_one_le₀ h1
      _ ≤ 1 + 2 * s := by linarith
  rw [he]
  calc Real.exp c * (Real.exp (-(lam * s)) * (s + Real.sqrt (1 + s ^ 2))) *
        (Real.sqrt (1 + s ^ 2))⁻¹ = Real.exp c * (Real.exp (-(lam * s)) *
          ((s + Real.sqrt (1 + s ^ 2)) * (Real.sqrt (1 + s ^ 2))⁻¹)) := by ring
    _ ≤ _ := by gcongr

/-- The kernel `(fun s : ℝ => Real.exp c * (Real.exp (-(lam * s)) * (1 + 2 * s)))` is integrable
on `(Ioi 0)`. -/
theorem struveSc_integrableOn_maj {lam : ℝ} (h0 : 0 < lam) (c : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp c * (Real.exp (-(lam * s)) * (1 + 2 * s))) (Ioi 0) := by
  obtain ⟨i0, -⟩ := struveSc_integral_pow_exp 0 h0
  obtain ⟨i1, -⟩ := struveSc_integral_pow_exp 1 h0
  refine IntegrableOn.congr_fun ((i0.add (i1.const_mul 2)).const_mul (Real.exp c))
    (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, pow_zero, pow_one]; ring

/-- The function `(struveSc_phiR lam)` is continuous. -/
theorem struveSc_continuous_phiR (lam : ℝ) : Continuous (struveSc_phiR lam) :=
  (continuous_const.mul continuous_id).sub Real.continuous_arsinh

/-- Estimate under the stated parameter and domain assumptions: `Real.exp (-y) ≤ 1 / y`. -/
theorem struveSc_exp_neg_le_recip {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hy (by linarith [Real.add_one_le_exp y])

/-- Estimate under the stated parameter and domain assumptions: `Real.sin δ ≤ Real.cos θ`. -/
theorem struveSc_cos_ge {δ θ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ < π / 2) (hθ : |θ| ≤ π / 2 - δ) :
    Real.sin δ ≤ Real.cos θ := by
  rw [← Real.cos_abs, ← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [Real.pi_pos]) hθ

/-- **The main Laplace estimate** behind DLMF 11.11.15, uniform in `ph ν`. -/
theorem struveSc_inner_est {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ)
    (hδπ : δ < π / 2) : ∃ C n₀ : ℝ, 0 < n₀ ∧ ∀ n θ : ℝ, n₀ ≤ n → |θ| ≤ π / 2 - δ →
      ‖(Real.sqrt n : ℂ) * (∫ s in Ioi (0 : ℝ), exp (-((n : ℂ) * exp ((θ : ℂ) * I) *
          ((struveSc_phiR lam s - struveSc_phiR lam (struveSc_s0 lam) : ℝ) : ℂ))) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ)) -
        (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (struveSc_Q0 lam : ℂ))) ^ (1 / 2 : ℂ)‖ ≤
        C / Real.sqrt n := by
  set s₀ := struveSc_s0 lam with hs₀
  set φ₀ := struveSc_phiR lam s₀ with hφ₀
  set Q0 := struveSc_Q0 lam with hQ0
  have hs0 := struveSc_s0_pos h0 h1
  have hQ := struveSc_Q0_pos h0 h1
  have hQs := struveSc_Q0_lt h0 h1
  set δ' := Q0 / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  set η := Q0 * δ' ^ 2 / 2 with hη
  have hη0 : 0 < η := by positivity
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set c := Real.sin δ * Q0 / 2 with hc
  have hc0 : 0 < c := by positivity
  set maj : ℝ → ℝ := fun s => Real.exp φ₀ * (Real.exp (-(lam * s)) * (1 + 2 * s)) with hmaj
  have hmi : IntegrableOn maj (Ioi 0) := struveSc_integrableOn_maj h0 φ₀
  set T0 := ∫ s in Ioi (0 : ℝ), maj s with hT0
  have hmaj0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ maj s := fun s hs => by simp only [hmaj]; positivity
  have hT00 : 0 ≤ T0 := setIntegral_nonneg measurableSet_Ioi fun s hs => hmaj0 s (le_of_lt hs)
  refine ⟨((1 + 1 / δ') / c + 1 * 1 / c ^ 2) + 2 * T0 / (Real.sin δ * η), 2 / Real.sin δ,
    by positivity, fun n θ hn hθ => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hcos := struveSc_cos_ge hδ.le hδπ hθ
  set x := n * Real.cos θ with hx
  have hx2 : 2 ≤ x := by
    have : 2 ≤ n * Real.sin δ := by rwa [div_le_iff₀ hsδ] at hn
    calc 2 ≤ n * Real.sin δ := this
      _ ≤ x := by rw [hx]; gcongr
  set ν : ℂ := (n : ℂ) * exp ((θ : ℂ) * I) with hν
  have hνre : ∀ d : ℝ, (-(ν * (d : ℂ))).re = -(x * d) := by
    intro d
    rw [hν, neg_re, show (n : ℂ) * exp ((θ : ℂ) * I) * (d : ℂ) = ((n * d : ℝ) : ℂ) *
      exp ((θ : ℂ) * I) by push_cast; ring, re_ofReal_mul, exp_ofReal_mul_I_re, hx]
    ring
  set f : ℝ → ℂ := fun s => exp (-(ν * ((struveSc_phiR lam s - φ₀ : ℝ) : ℂ))) *
    (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) with hf
  have hfn : ∀ s : ℝ, ‖f s‖ = Real.exp (-(x * (struveSc_phiR lam s - φ₀))) *
      (Real.sqrt (1 + s ^ 2))⁻¹ := by
    intro s
    rw [hf, norm_mul, norm_exp, hνre, norm_real, Real.norm_of_nonneg
      (inv_nonneg.2 (struveSc_sqrt_pos s).le)]
  have hSc : Continuous fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹ :=
    ((Real.continuous_sqrt.comp (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2)).inv₀
      fun s => (struveSc_sqrt_pos s).ne')
  have hfc : Continuous f := by
    have := struveSc_continuous_phiR lam
    simp only [hf]
    exact (continuous_exp.comp ((continuous_const.mul (continuous_ofReal.comp
      (this.sub continuous_const))).neg)).mul (continuous_ofReal.comp hSc)
  -- global bound
  have hb1 : ∀ s : ℝ, 0 ≤ s → ‖f s‖ ≤ maj s := by
    intro s hs
    have hd := struveSc_phiR_ge h0 h1 hs
    rw [hfn]
    refine le_trans ?_ (struveSc_W_le hs φ₀)
    gcongr
    nlinarith
  -- tail bound
  have hb2 : ∀ s : ℝ, 0 ≤ s → s ∉ Icc (s₀ - δ') (s₀ + δ') →
      ‖f s‖ ≤ Real.exp (-((x - 1) * η)) * maj s := by
    intro s hs hout
    have hd := struveSc_phiR_gap h0 h1 hs hout
    rw [← hs₀, ← hQ0, ← hφ₀] at hd
    have hd' : η ≤ struveSc_phiR lam s - φ₀ := by rw [hη, hδ']; linarith
    rw [hfn]
    have : Real.exp (-(x * (struveSc_phiR lam s - φ₀))) ≤
        Real.exp (-((x - 1) * η)) * Real.exp (-(struveSc_phiR lam s - φ₀)) := by
      rw [← Real.exp_add]; gcongr
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - 1 by linarith) (sub_nonneg.2 hd')]
    calc Real.exp (-(x * (struveSc_phiR lam s - φ₀))) * (Real.sqrt (1 + s ^ 2))⁻¹
        ≤ Real.exp (-((x - 1) * η)) * Real.exp (-(struveSc_phiR lam s - φ₀)) *
          (Real.sqrt (1 + s ^ 2))⁻¹ := by
          gcongr
      _ = Real.exp (-((x - 1) * η)) * (Real.exp (-(struveSc_phiR lam s - φ₀)) *
          (Real.sqrt (1 + s ^ 2))⁻¹) := by ring
      _ ≤ _ := by gcongr; exact struveSc_W_le hs φ₀
  have hfi : IntegrableOn f (Ioi 0) :=
    Integrable.mono' hmi hfc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs => hb1 s (le_of_lt hs)))
  -- split
  have hsplit := integral_inter_add_sdiff (f := f) (μ := volume) (s := Ioi 0)
    (t := Icc (s₀ - δ') (s₀ + δ')) measurableSet_Icc hfi
  have hinter : Ioi (0 : ℝ) ∩ Icc (s₀ - δ') (s₀ + δ') = Icc (s₀ - δ') (s₀ + δ') := by
    refine inter_eq_right.2 fun s hs => ?_
    exact mem_Ioi.2 (by linarith [hs.1])
  rw [hinter] at hsplit
  -- core via the Laplace estimate
  set A : ℝ → ℂ := fun t => (((Real.sqrt (1 + (s₀ + t) ^ 2))⁻¹ : ℝ) : ℂ) with hA
  set q : ℝ → ℂ := fun t => exp ((θ : ℂ) * I) * ((struveSc_Qf lam t : ℝ) : ℂ) with hq
  have hcore : ∫ s in Icc (s₀ - δ') (s₀ + δ'), f s =
      ∫ t in Icc (-δ') δ', A t * exp (-(n : ℂ) * (t : ℂ) ^ 2 * q t) := by
    have hpre := (measurePreserving_add_right volume s₀).setIntegral_preimage_emb
      (measurableEmbedding_addRight s₀) f (Icc (s₀ - δ') (s₀ + δ'))
    rw [Set.preimage_add_const_Icc, show s₀ - δ' - s₀ = -δ' by ring,
      show s₀ + δ' - s₀ = δ' by ring] at hpre
    rw [← hpre]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    have hD := struveSc_D_eq (lam := lam) t
    rw [← hs₀, ← hφ₀] at hD
    simp only [hf, hA, hq]
    rw [add_comm t s₀, hD, mul_comm]
    congr 2
    rw [hν]; push_cast; ring
  have hAc : Measurable A := by
    simp only [hA]; fun_prop
  have hQm : Measurable (struveSc_Qf lam) := by
    have hDc : Continuous fun t : ℝ => struveSc_phiR lam (struveSc_s0 lam + t) -
        struveSc_phiR lam (struveSc_s0 lam) :=
      ((struveSc_continuous_phiR lam).comp (continuous_const.add continuous_id)).sub
        continuous_const
    unfold struveSc_Qf
    exact Measurable.ite measurableSet_eq measurable_const
      (hDc.measurable.div (continuous_pow 2).measurable)
  have hqc : Measurable q := by
    simp only [hq]
    exact measurable_const.mul (Complex.measurable_ofReal.comp hQm)
  have hQ0f : struveSc_Qf lam 0 = Q0 := by simp [struveSc_Qf, hQ0]
  have hqre : ∀ t ∈ Icc (-δ') δ', c ≤ (q t).re := by
    intro t ht
    have hl := struveSc_Qf_lip h0 h1 t
    rw [← hQ0] at hl
    have hta : |t| ≤ δ' := abs_le.2 ⟨ht.1, ht.2⟩
    have hQt : Q0 / 2 ≤ struveSc_Qf lam t := by
      have := (abs_le.1 hl).1; linarith
    simp only [hq]
    rw [mul_comm, re_ofReal_mul, exp_ofReal_mul_I_re, hc]
    calc Real.sin δ * Q0 / 2 = Real.sin δ * (Q0 / 2) := by ring
      _ ≤ Real.cos θ * struveSc_Qf lam t := by
        have : 0 ≤ Real.cos θ := by linarith
        gcongr
      _ = struveSc_Qf lam t * Real.cos θ := by ring
  have hA0 : ‖A 0‖ ≤ 1 := by
    simp only [hA, add_zero]
    rw [← struveSc_crit h0 h1, norm_real, Real.norm_of_nonneg h0.le]; exact h1.le
  have hAl : ∀ t ∈ Icc (-δ') δ', ‖A t - A 0‖ ≤ 1 * |t| := by
    intro t _
    simp only [hA, add_zero]
    rw [← struveSc_crit h0 h1, ← ofReal_sub, norm_real, Real.norm_eq_abs, one_mul]
    exact struveSc_amp_lip h0 h1 t
  have hql : ∀ t ∈ Icc (-δ') δ', ‖q t - q 0‖ ≤ 1 * |t| := by
    intro t _
    simp only [hq]
    rw [← mul_sub, norm_mul, norm_exp_ofReal_mul_I, one_mul, one_mul, ← ofReal_sub, norm_real,
      Real.norm_eq_abs, hQ0f]
    exact struveSc_Qf_lip h0 h1 t
  have hlap := Complex.norm_sqrt_mul_integral_laplace_Icc_sub_le hc0 hδ'0 hn0 hAc hqc hqre hA0
    hAl hql
  have hA0' : A 0 = (lam : ℂ) := by
    simp only [hA, add_zero]; rw [← struveSc_crit h0 h1]
  have hq0' : q 0 = exp ((θ : ℂ) * I) * (Q0 : ℂ) := by simp only [hq]; rw [hQ0f]
  rw [hA0', hq0', ← hcore] at hlap
  -- tail
  set Tl := ∫ s in Ioi (0 : ℝ) \ Icc (s₀ - δ') (s₀ + δ'), f s with hTl
  have htail : ‖Tl‖ ≤ Real.exp (-((x - 1) * η)) * T0 := by
    have hmi' : IntegrableOn maj (Ioi 0 \ Icc (s₀ - δ') (s₀ + δ')) := hmi.mono_set sdiff_subset
    calc ‖Tl‖ ≤ ∫ s in Ioi (0 : ℝ) \ Icc (s₀ - δ') (s₀ + δ'), Real.exp (-((x - 1) * η)) * maj s :=
          norm_integral_le_of_norm_le (hmi'.const_mul _) ((ae_restrict_iff'
            (measurableSet_Ioi.diff measurableSet_Icc)).mpr (Eventually.of_forall fun s hs =>
              hb2 s (le_of_lt hs.1) hs.2))
      _ = Real.exp (-((x - 1) * η)) * ∫ s in Ioi (0 : ℝ) \ Icc (s₀ - δ') (s₀ + δ'), maj s :=
          integral_const_mul _ _
      _ ≤ Real.exp (-((x - 1) * η)) * T0 := by
          gcongr
          exact setIntegral_mono_set hmi ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun s hs => hmaj0 s (le_of_lt hs)))
            (Eventually.of_forall fun s hs => hs.1)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have htail' : Real.sqrt n * ‖Tl‖ ≤ 2 * T0 / (Real.sin δ * η) / Real.sqrt n := by
    have hy : 0 < (x - 1) * η := mul_pos (by linarith) hη0
    have he := struveSc_exp_neg_le_recip hy
    have hxs : n * Real.sin δ ≤ x := by rw [hx]; gcongr
    have hx1 : x ≤ 2 * (x - 1) := by linarith
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    calc Real.sqrt n * ‖Tl‖ ≤ Real.sqrt n * (1 / ((x - 1) * η) * T0) := by
          gcongr; exact htail.trans (by gcongr)
      _ ≤ Real.sqrt n * (2 / (n * Real.sin δ * η) * T0) := by
          have key : 1 / ((x - 1) * η) ≤ 2 / (n * Real.sin δ * η) := by
            rw [div_le_div_iff₀ hy (by positivity)]
            nlinarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right key hT00) hsq.le
      _ = 2 * T0 / (Real.sin δ * η) / Real.sqrt n := by
          rw [eq_div_iff hsq.ne', mul_comm, ← mul_assoc, hsn]
          field_simp
  -- assemble
  rw [← hsplit, mul_add]
  calc ‖(Real.sqrt n : ℂ) * (∫ s in Icc (s₀ - δ') (s₀ + δ'), f s) + (Real.sqrt n : ℂ) * Tl -
        (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (Q0 : ℂ))) ^ (1 / 2 : ℂ)‖
      ≤ ‖(Real.sqrt n : ℂ) * (∫ s in Icc (s₀ - δ') (s₀ + δ'), f s) -
        (lam : ℂ) * ((π : ℂ) / (exp ((θ : ℂ) * I) * (Q0 : ℂ))) ^ (1 / 2 : ℂ)‖ +
        ‖(Real.sqrt n : ℂ) * Tl‖ := by
        rw [show ∀ a b d : ℂ, a + b - d = (a - d) + b from fun a b d => by ring]
        exact norm_add_le _ _
    _ ≤ ((1 + 1 / δ') / c + 1 * 1 / c ^ 2) / Real.sqrt n +
        2 * T0 / (Real.sin δ * η) / Real.sqrt n := by
        gcongr
        rw [norm_mul, norm_real, Real.norm_of_nonneg hsq.le]; exact htail'
    _ = _ := by ring

end StruveScaled
end DLMF.Struve
end
