/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.AngerWeber
public import DLMFMathlib.Analysis.Asymptotics.StationaryPhase

/-!
# Turning-point tools for the Anger–Weber functions

For real `ν`, DLMF 11.10.1–11.10.2 at `z = ν` read

`𝐉_ν(ν) = π⁻¹ Re ∫₀^π e^{iν(θ - sin θ)} dθ`,  `𝐄_ν(ν) = π⁻¹ Im ∫₀^π e^{iν(θ - sin θ)} dθ`

(`struveTP_angerJ_eq`, `struveTP_weberE_eq`). The phase `θ - sin θ = θ³/6 + O(θ⁴)` has a cubic
stationary point at `θ = 0`, so the stationary-phase lemma
`Complex.statPh_tendsto_cubic` gives `ν^{1/3} ∫₀^π e^{iν(θ - sin θ)} dθ → 6^{1/3} Γ(4/3) e^{iπ/6}`
(`struveTP_tendsto_integral`). The constants are reduced to the DLMF form with
`Γ(4/3) Γ(2/3) = 2π/(3√3)` (`struveTP_const_J`, `struveTP_const_E`); these are the inputs of
DLMF 11.11.18 and 11.11.19 in `DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology Interval
namespace DLMF.Struve

/-- `|x - sin x - x³/6| ≤ 3 x⁴` for `x ≥ 0`. -/
lemma struveTP_sub_sin_bound {x : ℝ} (hx : 0 ≤ x) : |x - Real.sin x - x ^ 3 / 6| ≤ 3 * x ^ 4 := by
  rcases le_or_gt x 1 with h1 | h1
  · have h := Real.sin_bound (x := x) (by rw [abs_of_nonneg hx]; exact h1)
    rw [abs_of_nonneg hx] at h
    rw [show x - Real.sin x - x ^ 3 / 6 = -(Real.sin x - (x - x ^ 3 / 6)) by ring, abs_neg]
    nlinarith [pow_nonneg hx 4]
  · have hs1 := Real.sin_le_one x
    have hs2 := Real.neg_one_le_sin x
    have h2 : x ≤ x ^ 4 := by
      have : 1 ≤ x ^ 3 := one_le_pow₀ h1.le
      nlinarith
    have h3 : x ^ 3 ≤ x ^ 4 := by nlinarith [pow_nonneg hx 3]
    have h4 : 1 ≤ x ^ 4 := one_le_pow₀ h1.le
    rw [abs_le]; constructor <;> nlinarith [pow_nonneg hx 3]

/-- `(2/π²) x² ≤ 1 - cos x` on `[0, π]`. -/
lemma struveTP_one_sub_cos_ge {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π) :
    2 / π ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
  have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub]; ring_nf
  have hs := Real.mul_le_sin (x := x / 2) (by linarith) (by linarith)
  have hπ := Real.pi_pos
  have h0 : 0 ≤ 2 / π * (x / 2) := by positivity
  have hsq : (2 / π * (x / 2)) ^ 2 ≤ Real.sin (x / 2) ^ 2 := pow_le_pow_left₀ h0 hs 2
  rw [hc]
  have : (2 / π * (x / 2)) ^ 2 = x ^ 2 / π ^ 2 := by field_simp
  rw [this] at hsq
  have : 2 / π ^ 2 * x ^ 2 = 2 * (x ^ 2 / π ^ 2) := by ring
  linarith

/-- The Anger–Weber turning-point integral:
`ν^{1/3} ∫₀^π e^{iν(θ - sin θ)} dθ → 6^{1/3} Γ(4/3) e^{iπ/6}`. -/
lemma struveTP_tendsto_integral :
    Tendsto (fun ν : ℝ => ((ν ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        ∫ x in (0 : ℝ)..π, exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)) atTop
      (𝓝 ((((1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
        ((Real.Gamma (4 / 3) : ℂ) * exp ((π / 6 : ℝ) * I)))) := by
  have hd1 : ∀ x ∈ Icc 0 π, HasDerivAt (fun x => x - Real.sin x) (1 - Real.cos x) x :=
    fun x _ => (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  have hd2 : ∀ x ∈ Icc 0 π, HasDerivAt (fun x => 1 - Real.cos x) (Real.sin x) x :=
    fun x _ => by simpa using (Real.hasDerivAt_cos x).const_sub 1
  have hK : ∀ x ∈ Icc 0 π, |(x - Real.sin x) - 1 / 6 * x ^ 3| ≤ 3 * x ^ 4 := fun x hx => by
    have := struveTP_sub_sin_bound hx.1
    rwa [show x ^ 3 / 6 = 1 / 6 * x ^ 3 by ring] at this
  exact Complex.statPh_tendsto_cubic Real.pi_pos (by norm_num) (by positivity) hd1 hd2
    Real.continuous_sin.continuousOn
    (fun x hx => Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)
    (fun x hx => struveTP_one_sub_cos_ge hx.1 hx.2) hK

/-- `Γ(4/3) Γ(2/3) = 2π/(3√3)`. -/
lemma struveTP_Gamma_four_thirds_mul :
    Real.Gamma (4 / 3) * Real.Gamma (2 / 3) = 2 * π / (3 * Real.sqrt 3) := by
  have h1 : Real.Gamma (4 / 3) = 1 / 3 * Real.Gamma (1 / 3) := by
    rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h2 := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show π * (1 / 3) = π / 3 by ring,
    Real.sin_pi_div_three] at h2
  rw [h1, mul_assoc, h2]
  have : 0 < Real.sqrt 3 := by positivity
  field_simp

/-- `(1/6)^{-1/3} = 2^{1/3} 3^{1/3}`. -/
lemma struveTP_sixth_rpow : (1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) = 2 ^ (1 / 3 : ℝ) * 3 ^ (1 / 3 : ℝ) := by
  rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv,
    show (6 : ℝ) = 2 * 3 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]

/-- DLMF 11.10.1 at `z = ν` for real `ν`: `𝐉_ν(ν)` as the real part of
`π⁻¹ ∫₀^π e^{iν(θ - sin θ)} dθ`. -/
lemma struveTP_angerJ_eq (ν : ℝ) :
    angerJ ν ν = (((1 / π) * (∫ x in (0 : ℝ)..π,
      exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).re : ℝ) : ℂ) := by
  have hint : IntervalIntegrable (fun x : ℝ => exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I))
      volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).intervalIntegrable _ _
  have hpt : ∀ x : ℝ, cos ((ν : ℂ) * x - ν * (Real.sin x : ℝ)) =
      (((exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).re : ℝ) : ℂ) := fun x => by
    rw [exp_ofReal_mul_I_re]; push_cast; ring_nf
  have hr := intervalIntegral.intervalIntegral_re hint
  simp only [RCLike.re_to_complex] at hr
  rw [angerJ, intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_ofReal, hr]
  push_cast; ring

/-- DLMF 11.10.2 at `z = ν` for real `ν`: `𝐄_ν(ν)` as the imaginary part of
`π⁻¹ ∫₀^π e^{iν(θ - sin θ)} dθ`. -/
lemma struveTP_weberE_eq (ν : ℝ) :
    weberE ν ν = (((1 / π) * (∫ x in (0 : ℝ)..π,
      exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).im : ℝ) : ℂ) := by
  have hint : IntervalIntegrable (fun x : ℝ => exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I))
      volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).intervalIntegrable _ _
  have hpt : ∀ x : ℝ, sin ((ν : ℂ) * x - ν * (Real.sin x : ℝ)) =
      (((exp (((ν * (x - Real.sin x) : ℝ) : ℂ) * I)).im : ℝ) : ℂ) := fun x => by
    rw [exp_ofReal_mul_I_im]; push_cast; ring_nf
  have hr := intervalIntegral.intervalIntegral_im hint
  simp only [RCLike.im_to_complex] at hr
  rw [weberE, intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_ofReal, hr]
  push_cast; ring

/-- Equivalence from a real limit: if `ν^{1/3} f(ν) → K` (real, `K ≠ 0`) then
`f(ν) ~ K ν^{-1/3}`, stated for the complex casts used in DLMF 11.11.18–19. -/
lemma struveTP_isEquivalent_of_tendsto {f : ℝ → ℝ} {K : ℝ} (hK : K ≠ 0)
    (h : Tendsto (fun ν : ℝ => ν ^ (1 / 3 : ℝ) * f ν) atTop (𝓝 K)) :
    (fun ν : ℝ => (f ν : ℂ)) ~[atTop] (fun ν : ℝ => ((K / ν ^ (1 / 3 : ℝ) : ℝ) : ℂ)) := by
  refine isEquivalent_of_tendsto_one ?_
  have h1 : Tendsto (fun ν : ℝ => ((ν ^ (1 / 3 : ℝ) * f ν / K : ℝ) : ℂ)) atTop (𝓝 ((K / K : ℝ) : ℂ)) :=
    (continuous_ofReal.tendsto _).comp (h.div_const K)
  rw [div_self hK, ofReal_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν
  have : 0 < ν ^ (1 / 3 : ℝ) := by positivity
  simp only [Pi.div_apply]
  rw [← ofReal_div]
  congr 1
  field_simp

/-- `π⁻¹ 6^{1/3} Γ(4/3) cos(π/6) = 2^{1/3}/(3^{2/3} Γ(2/3))`. -/
lemma struveTP_const_J :
    1 / π * ((1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.Gamma (4 / 3) * Real.cos (π / 6)) =
      2 ^ (1 / 3 : ℝ) / (3 ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) := by
  have hG := struveTP_Gamma_four_thirds_mul
  have hG23 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : (3 : ℝ) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ) = 3 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have hs : 0 < Real.sqrt 3 := by positivity
  have hss : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [struveTP_sixth_rpow, Real.cos_pi_div_six,
    show Real.Gamma (4 / 3) = 2 * π / (3 * Real.sqrt 3) / Real.Gamma (2 / 3) by
      rw [← hG]; field_simp]
  have h23 : 0 < (3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  field_simp
  linear_combination h3

/-- `π⁻¹ 6^{1/3} Γ(4/3) sin(π/6) = 2^{1/3}/(3^{7/6} Γ(2/3))`. -/
lemma struveTP_const_E :
    1 / π * ((1 / 6 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.Gamma (4 / 3) * Real.sin (π / 6)) =
      2 ^ (1 / 3 : ℝ) / (3 ^ (7 / 6 : ℝ) * Real.Gamma (2 / 3)) := by
  have hG := struveTP_Gamma_four_thirds_mul
  have hG23 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : (3 : ℝ) ^ (1 / 3 : ℝ) * 3 ^ (7 / 6 : ℝ) = 3 * Real.sqrt 3 := by
    rw [← Real.rpow_add (by norm_num), Real.sqrt_eq_rpow,
      show (1 / 3 : ℝ) + 7 / 6 = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one]
  have hs : 0 < Real.sqrt 3 := by positivity
  rw [struveTP_sixth_rpow, Real.sin_pi_div_six,
    show Real.Gamma (4 / 3) = 2 * π / (3 * Real.sqrt 3) / Real.Gamma (2 / 3) by
      rw [← hG]; field_simp]
  have h76 : 0 < (3 : ℝ) ^ (7 / 6 : ℝ) := by positivity
  field_simp
  linear_combination h3

/-- The DLMF right-hand side `2^{1/3}/(3^a Γ(2/3) ν^{1/3})` as a real cast for `ν > 0`. -/
lemma struveTP_rhs_eq (a : ℝ) {ν : ℝ} (hν : 0 < ν) :
    (2 : ℂ) ^ (1 / 3 : ℂ) / ((3 : ℂ) ^ (a : ℂ) * Gamma (2 / 3) * (ν : ℂ) ^ (1 / 3 : ℂ)) =
      (((2 ^ (1 / 3 : ℝ) / (3 ^ a * Real.Gamma (2 / 3))) / ν ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
  have e2 : (2 : ℂ) ^ (1 / 3 : ℂ) = ((2 ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  have e3 : (3 : ℂ) ^ (a : ℂ) = ((3 ^ a : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  have eν : (ν : ℂ) ^ (1 / 3 : ℂ) = ((ν ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow hν.le]; push_cast; rfl
  have eG : Gamma (2 / 3 : ℂ) = ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  rw [e2, e3, eν, eG]
  push_cast
  ring

end DLMF.Struve
