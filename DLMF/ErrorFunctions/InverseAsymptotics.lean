/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic.Inverse
public import DLMF.ErrorFunctions.BoundsAsymptotics.GaussianRemainders

/-!
# Leading logarithmic asymptotics of the inverse complementary error function

The positive-axis error estimate in DLMF 7.12.1 yields
`√π x exp(x²) erfc(x) → 1` and hence `-log(erfc x) / x² → 1`.
Inverting with TauCeti's inverse error function gives
`inverfc(x) / √(log(1/x)) → 1` as `x → 0+`, the leading scale of DLMF 7.17.3.

These estimates use the first Gaussian remainder and the inverse identities, with no dependence
on the all-order inverse expansion.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology
namespace DLMF.Confluent


/-- The normalized real complementary error function differs from one by at most `1/(2x²)`
for `x > 0`, from the first remainder in DLMF 7.12.1. -/
theorem Real.abs_normalized_erfc_sub_one_le {x : ℝ} (hx : 0 < x) :
    |Real.sqrt π*x*Real.exp (x^2)*TauCeti.Real.erfc x-1| ≤ 1/(2*x^2) := by
  have h := erfc_remainder_bound (z := (x:ℂ)) (by exact_mod_cast hx.ne')
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; simp; positivity) 1
  simp only [erfcAsymptoticRemainder, Finset.sum_range_one, pow_zero, one_mul,
    DLMF.Hypergeometric.pochhammer_zero, Nat.mul_zero, zero_add, pow_one,
    Nat.mul_one, Nat.reduceAdd, DLMF.Hypergeometric.pochhammer_one,
    Complex.arg_ofReal_of_nonneg hx.le, abs_zero,
    ite_eq_left (by positivity : (0:ℝ) ≤ π/4)] at h
  have he : exp (-(x:ℂ)^2) = (Real.exp (-x^2) : ℂ) := by
    rw [← ofReal_pow, ← ofReal_neg, ← ofReal_exp]
  rw [he, erfc_ofReal] at h
  have hleftCast : (TauCeti.Real.erfc x : ℂ) - (Real.exp (-x^2) : ℂ) /
      (Real.sqrt π : ℂ) * (1/(x:ℂ)) =
      ((TauCeti.Real.erfc x - Real.exp (-x^2)/Real.sqrt π*(1/x) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hrightCast : (Real.exp (-x^2) : ℂ)/(Real.sqrt π : ℂ)*(1/2)/(x:ℂ)^3 =
      ((Real.exp (-x^2)/Real.sqrt π*(1/2)/x^3 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hleftCast, hrightCast, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hr := h
  rw [abs_of_pos (show 0 < Real.exp (-x^2)/Real.sqrt π*(1/2)/x^3 by positivity)] at hr
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hprod : Real.exp (x^2)*Real.exp (-x^2) = 1 := by
    rw [← Real.exp_add]; simp
  have hleft : (Real.sqrt π*x*Real.exp (x^2)) *
      (TauCeti.Real.erfc x - Real.exp (-x^2)/Real.sqrt π*(1/x)) =
      Real.sqrt π*x*Real.exp (x^2)*TauCeti.Real.erfc x-1 := by
    calc
      _ = Real.sqrt π*x*Real.exp (x^2)*TauCeti.Real.erfc x-
          Real.exp (x^2)*Real.exp (-x^2) := by field_simp [hx.ne', hπ]
      _ = _ := by rw [hprod]
  have hright : (Real.sqrt π*x*Real.exp (x^2)) *
      (Real.exp (-x^2)/Real.sqrt π*(1/2)/x^3) = 1/(2*x^2) := by
    calc
      _ = (Real.exp (x^2)*Real.exp (-x^2))/(2*x^2) := by
        field_simp [hx.ne', hπ]
      _ = _ := by rw [hprod]
  calc
    _ = |(Real.sqrt π*x*Real.exp (x^2)) *
        (TauCeti.Real.erfc x - Real.exp (-x^2)/Real.sqrt π*(1/x))| := congrArg abs hleft.symm
    _ = (Real.sqrt π*x*Real.exp (x^2)) *
        |TauCeti.Real.erfc x - Real.exp (-x^2)/Real.sqrt π*(1/x)| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (Real.sqrt π*x*Real.exp (x^2)) *
        (Real.exp (-x^2)/Real.sqrt π*(1/2)/x^3) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := hright

/-- The leading positive-axis asymptotic `√π x exp(x²) erfc(x) → 1`. -/
theorem Real.tendsto_normalized_erfc_atTop :
    Tendsto (fun x : ℝ => Real.sqrt π*x*Real.exp (x^2)*TauCeti.Real.erfc x)
      atTop (𝓝 1) := by
  have hb : Tendsto (fun x : ℝ => 1/(2*x^2)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).div_atTop
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hz : Tendsto (fun x : ℝ => Real.sqrt π*x*Real.exp (x^2)*TauCeti.Real.erfc x-1)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simpa only [Real.norm_eq_abs] using Real.abs_normalized_erfc_sub_one_le hx
  simpa using hz.add_const 1

/-- The logarithm of the complementary error function satisfies `-log(erfc x) / x² → 1`. -/
theorem Real.tendsto_neg_log_erfc_div_sq_atTop :
    Tendsto (fun x : ℝ => -Real.log (TauCeti.Real.erfc x)/x^2) atTop (𝓝 1) := by
  have hsq : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have ha : Tendsto (fun x : ℝ =>
      Real.log (Real.sqrt π*x*Real.exp (x^2)*TauCeti.Real.erfc x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_normalized_erfc_atTop.log (by norm_num : (1:ℝ) ≠ 0)
  have hA := ha.div_atTop hsq
  have hc := (tendsto_const_nhds (x := Real.log (Real.sqrt π))).div_atTop hsq
  have hl1 : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hl : Tendsto (fun x : ℝ => Real.log x/x^2) atTop (𝓝 0) := by
    simpa only [zero_div, div_div, Function.id_def, ← pow_two] using hl1.div_atTop tendsto_id
  have H := (((tendsto_const_nhds (x := (1:ℝ))).add hl).add hc).sub hA
  simp only [add_zero, sub_zero] at H
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hid : Real.log (Real.sqrt π*x*Real.exp (x^2)*TauCeti.Real.erfc x) =
      Real.log (Real.sqrt π) + Real.log x + x^2 + Real.log (TauCeti.Real.erfc x) := by
    rw [Real.log_mul (by positivity) (TauCeti.Real.erfc_pos x).ne',
      Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul hπ hx.ne', Real.log_exp]
  rw [hid]
  field_simp [hx.ne']
  ring

/-- The square of the inverse complementary error function is asymptotic to `-log x`
as `x` tends to zero from above. -/
theorem Real.tendsto_invErfc_sq_div_neg_log :
    Tendsto (fun x : ℝ => Real.invErfc x^2/(-Real.log x))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h := Real.tendsto_neg_log_erfc_div_sq_atTop.comp Real.tendsto_invErfc_nhdsGT_zero
  have he : (fun x : ℝ => -Real.log (TauCeti.Real.erfc (Real.invErfc x))/Real.invErfc x^2)
      =ᶠ[𝓝[>] (0:ℝ)] fun x => -Real.log x/Real.invErfc x^2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<2))] with x hx hx2
    have hs : TauCeti.Real.erfc (Real.invErfc x) = x := by
      simpa only [erfc_ofReal, ofReal_re] using Real.invErfc_spec hx hx2
    rw [hs]
  have h' := (h.congr' he).inv₀ (by norm_num : (1:ℝ) ≠ 0)
  simpa only [inv_one, inv_div] using h'

/-- The leading inverse complementary error asymptotic is `inverfc(x) / √(log(1/x)) → 1`
as `x` tends to zero from above. -/
theorem Real.tendsto_invErfc_div_sqrt_log :
    Tendsto (fun x : ℝ => Real.invErfc x/Real.sqrt (Real.log (1/x)))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h := Real.tendsto_invErfc_sq_div_neg_log.sqrt
  simp only [Real.sqrt_one] at h
  refine h.congr' ?_
  filter_upwards [Real.tendsto_invErfc_nhdsGT_zero.eventually (eventually_ge_atTop (0:ℝ))] with x hx
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hx, one_div, Real.log_inv]

end DLMF.Confluent
