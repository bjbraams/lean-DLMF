/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Modified
public import DLMF.Gamma.IntegralRepresentations

/-!
# Bessel functions of large order

All results come from the series `Γ(ν+1) ₀F̃₁(;ν+1;v) = ∑ v^n / (n! (ν+1)_n)` by dominated
convergence (Tannery's theorem) as `ν → +∞` along the reals.

* `tendsto_Gamma_mul_regularized0F1_mul`: `Γ(ν+1) ₀F̃₁(;ν+1;ν w) → e^w`.
* `tendsto_Gamma_mul_besselJ_sqrt_mul` (Beals–Wong (9.1.16)):
  `Γ(ν+1) J_ν(√ν x) / (√ν x/2)^ν → e^{-x²/4}`, and the companion
  `tendsto_Gamma_mul_besselI_sqrt_mul` for `I_ν` with limit `e^{x²/4}`.
* `norm_besselJ_le`: `|J_ν(z)| ≤ |(z/2)^ν| e^{|z|²/4} / Γ(ν+1)` for real `ν ≥ 0`.
* `besselJ_isEquivalent_large_order` (DLMF 10.19.1): `J_ν(z) ∼ (ez/(2ν))^ν / √(2πν)` for fixed
  `z ≠ 0`, using Binet's form of Stirling's formula.
-/

@[expose] public section

open Complex Filter Asymptotics
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Bessel

section LargeOrder

/-- The ratio `Γ(ν+1)/Γ(ν+1+n) = 1/(ν+1)_n`. -/
def gammaShiftRatio (ν : ℝ) (n : ℕ) : ℝ := Real.Gamma (ν + 1) / Real.Gamma (ν + 1 + n)

/-- Identity under the stated parameter and domain assumptions: `gammaShiftRatio ν 0 = 1`. -/
theorem gammaShiftRatio_zero (ν : ℝ) (hν : -1 < ν) : gammaShiftRatio ν 0 = 1 := by
  have h : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  simp [gammaShiftRatio, h]

/-- Identity under the stated parameter and domain assumptions: `gammaShiftRatio ν (n + 1) =
gammaShiftRatio ν n / (ν + 1 + n)`. -/
theorem gammaShiftRatio_succ {ν : ℝ} (hν : -1 < ν) (n : ℕ) :
    gammaShiftRatio ν (n + 1) = gammaShiftRatio ν n / (ν + 1 + n) := by
  have h1 : 0 < ν + 1 := by linarith
  have h : 0 < ν + 1 + n := by positivity
  have hG : Real.Gamma (ν + 1 + n) ≠ 0 := (Real.Gamma_pos_of_pos h).ne'
  unfold gammaShiftRatio
  rw [show ν + 1 + ((n + 1 : ℕ) : ℝ) = (ν + 1 + n) + 1 by push_cast; ring,
    Real.Gamma_add_one h.ne']
  field_simp

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ gammaShiftRatio ν n`. -/
theorem gammaShiftRatio_nonneg {ν : ℝ} (hν : -1 < ν) (n : ℕ) : 0 ≤ gammaShiftRatio ν n := by
  have h1 : 0 < ν + 1 := by linarith
  exact div_nonneg (Real.Gamma_pos_of_pos h1).le (Real.Gamma_pos_of_pos (by positivity)).le

/-- Estimate under the stated parameter and domain assumptions: `gammaShiftRatio ν n ≤ 1`. -/
theorem gammaShiftRatio_le_one {ν : ℝ} (hν : 0 ≤ ν) (n : ℕ) : gammaShiftRatio ν n ≤ 1 := by
  induction n with
  | zero => rw [gammaShiftRatio_zero ν (by linarith)]
  | succ n ih =>
    rw [gammaShiftRatio_succ (by linarith)]
    have h1 : 1 ≤ ν + 1 + n := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    exact (div_le_self (gammaShiftRatio_nonneg (by linarith) n) h1).trans ih

/-- Estimate under the stated parameter and domain assumptions: `gammaShiftRatio ν n * ν ^ n ≤ 1`. -/
theorem gammaShiftRatio_mul_pow_le_one {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    gammaShiftRatio ν n * ν ^ n ≤ 1 := by
  induction n with
  | zero => simp [gammaShiftRatio_zero ν (by linarith)]
  | succ n ih =>
    have h1 : 0 < ν + 1 + n := by positivity
    rw [gammaShiftRatio_succ (by linarith), pow_succ,
      show gammaShiftRatio ν n / (ν + 1 + n) * (ν ^ n * ν) =
        (gammaShiftRatio ν n * ν ^ n) * (ν / (ν + 1 + n)) by field_simp]
    have h2 : ν / (ν + 1 + n) ≤ 1 := (div_le_one h1).2 (by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith)
    calc _ ≤ 1 * 1 := mul_le_mul ih h2 (div_nonneg hν.le h1.le) zero_le_one
      _ = 1 := one_mul 1

/-- The map `(fun ν : ℝ => ν / (ν + c))` tends to `(𝓝 1)` along `atTop`. -/
theorem tendsto_div_add_const (c : ℝ) :
    Tendsto (fun ν : ℝ => ν / (ν + c)) atTop (𝓝 1) := by
  have h : Tendsto (fun ν : ℝ => (1 + c * ν⁻¹)⁻¹) atTop (𝓝 ((1 + c * 0)⁻¹)) :=
    (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul c)).inv₀ (by simp)
  rw [mul_zero, add_zero, inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  field_simp

/-- The map `(fun ν : ℝ => gammaShiftRatio ν n * ν ^ n)` tends to `(𝓝 1)` along `atTop`. -/
theorem tendsto_gammaShiftRatio_mul_pow (n : ℕ) :
    Tendsto (fun ν : ℝ => gammaShiftRatio ν n * ν ^ n) atTop (𝓝 1) := by
  induction n with
  | zero =>
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
    simp [gammaShiftRatio_zero ν (by linarith)]
  | succ n ih =>
    have h := ih.mul (tendsto_div_add_const (1 + n))
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
    have h1 : 0 < ν + 1 + n := by positivity
    rw [gammaShiftRatio_succ (by linarith), pow_succ, ← add_assoc]
    field_simp

/-- The map `(fun ν : ℝ => gammaShiftRatio ν (n + 1))` tends to `(𝓝 0)` along `atTop`. -/
theorem tendsto_gammaShiftRatio_succ (n : ℕ) :
    Tendsto (fun ν : ℝ => gammaShiftRatio ν (n + 1)) atTop (𝓝 0) := by
  have hb : Tendsto (fun ν : ℝ => 1 / (ν + 1 + n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_id))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ν hν
    exact gammaShiftRatio_nonneg (by linarith) _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ν hν
    have h1 : 0 < ν + 1 + n := by positivity
    rw [gammaShiftRatio_succ (by linarith)]
    exact div_le_div_of_nonneg_right (gammaShiftRatio_le_one hν n) h1.le

/-- `Γ(ν+1) ₀F̃₁(;ν+1;v) = ∑ v^n Γ(ν+1)/(n! Γ(ν+1+n))` for real `ν > -1`. -/
theorem Gamma_mul_regularized0F1_eq_tsum {ν : ℝ} (hν : -1 < ν) (v : ℂ) :
    Complex.Gamma ((ν : ℂ) + 1) * regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} v =
      ∑' n : ℕ, (gammaShiftRatio ν n : ℂ) * (v ^ n / n !) := by
  have hs := (hasFPowerSeriesOnBall_regularized0F1 ((ν : ℂ) + 1)).hasSum_mul_pow
    (z := v) (by simp)
  rw [← (hs.mul_left (Complex.Gamma ((ν : ℂ) + 1))).tsum_eq]
  congr 1
  funext n
  have h0 : 0 < ν + 1 := by linarith
  have h1 : 0 < ν + 1 + n := by positivity
  have hG1 : Complex.Gamma ((ν : ℂ) + 1) = (Real.Gamma (ν + 1) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hG2 : Complex.Gamma ((ν : ℂ) + 1 + n) = (Real.Gamma (ν + 1 + n) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hne : (Real.Gamma (ν + 1 + n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos h1).ne'
  rw [regularizedHGFunCoeff_empty, hG1, hG2, gammaShiftRatio]
  push_cast
  field_simp

/-- Tannery: `Γ(ν+1) ₀F̃₁(;ν+1;ν w) → e^w` as `ν → +∞`. -/
theorem tendsto_Gamma_mul_regularized0F1_mul (w : ℂ) :
    Tendsto (fun ν : ℝ => Complex.Gamma ((ν : ℂ) + 1) *
      regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} (ν * w)) atTop (𝓝 (exp w)) := by
  have hlim : Tendsto
      (fun ν : ℝ => ∑' n : ℕ, ((gammaShiftRatio ν n * ν ^ n : ℝ) : ℂ) * (w ^ n / n !))
      atTop (𝓝 (∑' n : ℕ, ((1 : ℝ) : ℂ) * (w ^ n / n !))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖w‖ ^ n / n !)
      (Real.summable_pow_div_factorial ‖w‖) (fun n => ?_) ?_
    · exact ((continuous_ofReal.tendsto _).comp (tendsto_gammaShiftRatio_mul_pow n)).mul_const _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν n
      have hq0 : 0 ≤ gammaShiftRatio ν n * ν ^ n :=
        mul_nonneg (gammaShiftRatio_nonneg (by linarith) n) (by positivity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0, norm_div,
        norm_pow, Complex.norm_natCast]
      exact mul_le_of_le_one_left (by positivity) (gammaShiftRatio_mul_pow_le_one hν n)
  have hexp : ∑' n : ℕ, ((1 : ℝ) : ℂ) * (w ^ n / n !) = exp w := by
    simp only [ofReal_one, one_mul]
    rw [Complex.exp_eq_exp_ℂ, (NormedSpace.expSeries_div_hasSum_exp w).tsum_eq]
  rw [hexp] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  rw [Gamma_mul_regularized0F1_eq_tsum (by linarith)]
  congr 1
  funext n
  push_cast
  rw [mul_pow]
  ring

/-- `Γ(ν+1) ₀F̃₁(;ν+1;u) → 1` as `ν → +∞`, for fixed `u`. -/
theorem tendsto_Gamma_mul_regularized0F1 (u : ℂ) :
    Tendsto (fun ν : ℝ => Complex.Gamma ((ν : ℂ) + 1) *
      regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} u) atTop (𝓝 1) := by
  have hlim : Tendsto (fun ν : ℝ => ∑' n : ℕ, (gammaShiftRatio ν n : ℂ) * (u ^ n / n !))
      atTop (𝓝 (∑' n : ℕ, ((if n = 0 then 1 else 0 : ℝ) : ℂ) * (u ^ n / n !))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖u‖ ^ n / n !)
      (Real.summable_pow_div_factorial ‖u‖) (fun n => ?_) ?_
    · refine ((continuous_ofReal.tendsto _).comp ?_).mul_const _
      rcases n with _ | n
      · simp only [↓reduceIte]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
        exact (gammaShiftRatio_zero ν (by linarith)).symm
      · simpa using tendsto_gammaShiftRatio_succ n
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ν hν n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gammaShiftRatio_nonneg (by linarith) n), norm_div, norm_pow,
        Complex.norm_natCast]
      exact mul_le_of_le_one_left (by positivity) (gammaShiftRatio_le_one hν n)
  have h1 : ∑' n : ℕ, ((if n = 0 then 1 else 0 : ℝ) : ℂ) * (u ^ n / n !) = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp
  rw [h1] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  rw [Gamma_mul_regularized0F1_eq_tsum (by linarith)]

/-- The large-order limit of Beals–Wong (9.1.16): for fixed `x ≠ 0`,
`Γ(ν+1) J_ν(√ν x) / (√ν x/2)^ν → e^{-x²/4}` as `ν → +∞`. -/
theorem tendsto_Gamma_mul_besselJ_sqrt_mul {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun ν : ℝ => Complex.Gamma ((ν : ℂ) + 1) *
      besselJ ν ((Real.sqrt ν : ℂ) * x) / ((Real.sqrt ν : ℂ) * x / 2) ^ (ν : ℂ))
      atTop (𝓝 (exp (-(x ^ 2 / 4)))) := by
  refine (tendsto_Gamma_mul_regularized0F1_mul (-(x ^ 2 / 4))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  have hz : (Real.sqrt ν : ℂ) * x ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hν).ne') hx
  have hp : ((Real.sqrt ν : ℂ) * x / 2) ^ (ν : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => div_ne_zero hz two_ne_zero h.1
  have hsq : -(((Real.sqrt ν : ℂ) * x) ^ 2 / 4) = (ν : ℂ) * -(x ^ 2 / 4) := by
    rw [mul_pow, ← ofReal_pow, Real.sq_sqrt hν.le]
    ring
  rw [besselJ_eq_regularized, hsq, mul_div_assoc, mul_div_cancel_left₀ _ hp]

/-- The companion of Beals–Wong (9.1.16) for `I_ν`:
`Γ(ν+1) I_ν(√ν x) / (√ν x/2)^ν → e^{x²/4}` as `ν → +∞`. -/
theorem tendsto_Gamma_mul_besselI_sqrt_mul {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun ν : ℝ => Complex.Gamma ((ν : ℂ) + 1) *
      besselI ν ((Real.sqrt ν : ℂ) * x) / ((Real.sqrt ν : ℂ) * x / 2) ^ (ν : ℂ))
      atTop (𝓝 (exp (x ^ 2 / 4))) := by
  refine (tendsto_Gamma_mul_regularized0F1_mul (x ^ 2 / 4)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  have hz : (Real.sqrt ν : ℂ) * x ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hν).ne') hx
  have hp : ((Real.sqrt ν : ℂ) * x / 2) ^ (ν : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => div_ne_zero hz two_ne_zero h.1
  have hsq : ((Real.sqrt ν : ℂ) * x) ^ 2 / 4 = (ν : ℂ) * (x ^ 2 / 4) := by
    rw [mul_pow, ← ofReal_pow, Real.sq_sqrt hν.le]
    ring
  rw [besselI, hsq, mul_div_assoc, mul_div_cancel_left₀ _ hp]

/-- Estimate under the stated parameter and domain assumptions: `‖Complex.Gamma ((ν : ℂ) + 1) *
regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} v‖ ≤ Real.exp ‖v‖`. -/
theorem norm_Gamma_mul_regularized0F1_le {ν : ℝ} (hν : 0 ≤ ν) (v : ℂ) :
    ‖Complex.Gamma ((ν : ℂ) + 1) * regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} v‖ ≤
      Real.exp ‖v‖ := by
  rw [Gamma_mul_regularized0F1_eq_tsum (by linarith)]
  have hb (n : ℕ) : ‖(gammaShiftRatio ν n : ℂ) * (v ^ n / n !)‖ ≤ ‖v‖ ^ n / n ! := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gammaShiftRatio_nonneg (by linarith) n), norm_div, norm_pow,
      Complex.norm_natCast]
    exact mul_le_of_le_one_left (by positivity) (gammaShiftRatio_le_one hν n)
  refine (tsum_of_norm_bounded (Real.summable_pow_div_factorial ‖v‖).hasSum hb).trans ?_
  rw [Real.exp_eq_exp_ℝ, (NormedSpace.expSeries_div_hasSum_exp ‖v‖).tsum_eq]

/-- An elementary bound from the series: `|J_ν(z)| ≤ |(z/2)^ν| e^{|z|²/4} / Γ(ν+1)` for real
`ν ≥ 0`. -/
theorem norm_besselJ_le {ν : ℝ} (hν : 0 ≤ ν) (z : ℂ) :
    ‖besselJ ν z‖ ≤ ‖(z / 2) ^ (ν : ℂ)‖ * Real.exp (‖z‖ ^ 2 / 4) / Real.Gamma (ν + 1) := by
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < ν + 1)
  have hG1 : Complex.Gamma ((ν : ℂ) + 1) = (Real.Gamma (ν + 1) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have h := norm_Gamma_mul_regularized0F1_le hν (-(z ^ 2 / 4))
  rw [hG1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hG] at h
  have hv : ‖-(z ^ 2 / 4)‖ = ‖z‖ ^ 2 / 4 := by
    rw [norm_neg, norm_div, norm_pow]; norm_num
  rw [hv] at h
  rw [besselJ_eq_regularized, norm_mul, le_div_iff₀ hG, mul_assoc, mul_comm _ (Real.Gamma _)]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- Stirling's formula with Binet's remainder: `Γ(ν+1) = √(2πν) (ν/e)^ν e^{β(ν)}`. -/
theorem Gamma_add_one_eq_stirling {ν : ℝ} (hν : 0 < ν) :
    Real.Gamma (ν + 1) = Real.sqrt (2 * π * ν) * (ν / Real.exp 1) ^ ν *
      Real.exp (DLMF.Gamma.binetIntegral ν) := by
  have hG := Real.Gamma_pos_of_pos hν
  have hL : ν * Real.Gamma ν = Real.exp (Real.log ν + Real.log (Real.Gamma ν)) := by
    rw [Real.exp_add, Real.exp_log hν, Real.exp_log hG]
  rw [Real.Gamma_add_one hν.ne', hL, DLMF.Gamma.log_Gamma_eq_add_binetIntegral hν,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity),
    Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add,
    Real.log_mul (by positivity) hν.ne', Real.log_div hν.ne' (Real.exp_pos 1).ne',
    Real.log_exp]
  congr 1
  ring

/-- Identity under the stated parameter and domain assumptions: `(w * a) ^ s = w ^ s * (a : ℂ) ^
s`. -/
theorem mul_ofReal_cpow {w : ℂ} (hw : w ≠ 0) {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (w * a) ^ s = w ^ s * (a : ℂ) ^ s := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hw ha'), cpow_def_of_ne_zero hw,
    cpow_def_of_ne_zero ha', log_mul_ofReal a ha w hw, ← exp_add, ofReal_log ha.le]
  ring_nf

/-- The comparison function `(ez/(2ν))^ν / √(2πν)` of DLMF 10.19.1. -/
def besselLargeOrderMain (z : ℂ) (ν : ℝ) : ℂ :=
  ((Real.exp 1 : ℂ) * z / (2 * ν)) ^ (ν : ℂ) / (Real.sqrt (2 * π * ν) : ℂ)

/-- The correction factor `e^{-β(ν)} Γ(ν+1) ₀F̃₁(;ν+1;-z²/4)` in DLMF 10.19.1. -/
def besselLargeOrderCorr (z : ℂ) (ν : ℝ) : ℂ :=
  cexp (-(DLMF.Gamma.binetIntegral ν : ℂ)) * (Complex.Gamma ((ν : ℂ) + 1) *
    regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} (-(z ^ 2 / 4)))

/-- The map `(besselLargeOrderCorr z)` tends to `(𝓝 1)` along `atTop`. -/
theorem tendsto_besselLargeOrderCorr (z : ℂ) :
    Tendsto (besselLargeOrderCorr z) atTop (𝓝 1) := by
  have hβ0 : Tendsto (fun ν : ℝ => DLMF.Gamma.binetIntegral ν) atTop (𝓝 0) := by
    have hb : Tendsto (fun ν : ℝ => 1 / (12 * ν)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
      exact (DLMF.Gamma.binetIntegral_mem hν).1
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
      exact (DLMF.Gamma.binetIntegral_mem hν).2
  have hE : Tendsto (fun ν : ℝ => cexp (-(DLMF.Gamma.binetIntegral ν : ℂ))) atTop (𝓝 1) := by
    have h := (Complex.continuous_exp.tendsto _).comp
      (((continuous_ofReal.tendsto _).comp hβ0).neg)
    simpa [Function.comp_def] using h
  have h := hE.mul (tendsto_Gamma_mul_regularized0F1 (-(z ^ 2 / 4)))
  rw [one_mul] at h
  exact h

/-- Identity under the stated parameter and domain assumptions: `besselJ ν z =
besselLargeOrderMain z ν * besselLargeOrderCorr z ν`. -/
theorem besselJ_eq_main_mul_corr {z : ℂ} (hz : z ≠ 0) {ν : ℝ} (hν : 0 < ν) :
    besselJ ν z = besselLargeOrderMain z ν * besselLargeOrderCorr z ν := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hA : 0 < Real.exp 1 / ν := div_pos (Real.exp_pos 1) hν
  have hB : 0 < ν / Real.exp 1 := div_pos hν (Real.exp_pos 1)
  have hsplit : (Real.exp 1 : ℂ) * z / (2 * ν) = z / 2 * ((Real.exp 1 / ν : ℝ) : ℂ) := by
    have : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    push_cast
    field_simp
  have hAB : (Real.exp 1 / ν) ^ ν * (ν / Real.exp 1) ^ ν = 1 := by
    rw [← Real.mul_rpow hA.le hB.le,
      show Real.exp 1 / ν * (ν / Real.exp 1) = 1 by field_simp, Real.one_rpow]
  have hAB' : (((Real.exp 1 / ν) ^ ν : ℝ) : ℂ) * (((ν / Real.exp 1) ^ ν : ℝ) : ℂ) = 1 := by
    exact_mod_cast hAB
  have hs : (Real.sqrt (2 * π * ν) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have he : cexp (-(DLMF.Gamma.binetIntegral ν : ℂ)) *
      (Real.exp (DLMF.Gamma.binetIntegral ν) : ℂ) = 1 := by
    rw [ofReal_exp, ← Complex.exp_add]
    simp
  have hG1 : Complex.Gamma ((ν : ℂ) + 1) = (Real.Gamma (ν + 1) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have key : ∀ P F a b s E e : ℂ, s ≠ 0 → a * b = 1 → e * E = 1 →
      P * F = P * a / s * (e * (s * b * E * F)) := by
    intro P F a b s E e hs hab he
    rw [show P * a / s * (e * (s * b * E * F)) = P * F * (a * b) * (e * E) by
      field_simp, hab, he]
    ring
  rw [besselLargeOrderMain, besselLargeOrderCorr, hsplit, mul_ofReal_cpow hz2 hA,
    ← ofReal_cpow hA.le, besselJ_eq_regularized, hG1, Gamma_add_one_eq_stirling hν,
    ofReal_mul, ofReal_mul]
  exact key _ _ _ _ _ _ _ hs hAB' he

/-- DLMF 10.19.1: `J_ν(z) ∼ (ez/(2ν))^ν / √(2πν)` as `ν → +∞` along the reals, for fixed
`z ≠ 0`. -/
@[dlmf 10.19.E1]
theorem besselJ_isEquivalent_large_order {z : ℂ} (hz : z ≠ 0) :
    (fun ν : ℝ => besselJ ν z) ~[atTop]
      fun ν : ℝ => ((Real.exp 1 : ℂ) * z / (2 * ν)) ^ (ν : ℂ) /
        (Real.sqrt (2 * π * ν) : ℂ) := by
  have hlo : (fun ν : ℝ => besselLargeOrderCorr z ν - 1) =o[atTop] (fun _ => (1 : ℂ)) :=
    (Asymptotics.isLittleO_one_iff ℂ).2 (by
      simpa using (tendsto_besselLargeOrderCorr z).sub_const 1)
  refine (hlo.mul_isBigO (Asymptotics.isBigO_refl (besselLargeOrderMain z) atTop)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
    simp only [Pi.sub_apply]
    rw [besselJ_eq_main_mul_corr hz hν, besselLargeOrderMain]
    ring
  · exact Eventually.of_forall fun ν => one_mul _

end LargeOrder

end DLMF.Bessel
