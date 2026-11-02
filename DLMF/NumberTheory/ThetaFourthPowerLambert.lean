/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Identities
public import DLMF.NumberTheory.Basic.GeneratingFunctions
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# The fourth power of `ϑ` as a Lambert series (DLMF §27.13(iv))

This file proves Jacobi's Lambert series for the fourth power of the theta constant,
`θ₃(0|τ)⁴ = 1 + 8 ∑_{n≥1} n qⁿ/(1 + (-q)ⁿ)`, in the form
`ϑ(x)⁴ = 1 + 8 ∑_{n≥1} σ₁(n) xⁿ - 32 ∑_{n≥1} σ₁(n) x^{4n}`, `|x| < 1`. It is the analytic input
for Jacobi's four-square formula (§27.13(iv)) in `DLMF.NumberTheory.Additive`.

The route: differentiating DLMF 20.7.3, `θ₂²(0) θ₄²(z) = θ₃²(0) θ₁²(z) + θ₄²(0) θ₂²(z)`, twice at
`z = 0` and using Jacobi's derivative formula `θ₁'(0) = θ₂ θ₃ θ₄` (20.4.6) gives
`θ₃(0)⁴ = θ₄''(0)/θ₄(0) - θ₂''(0)/θ₂(0)`; the two quotients are the derivatives at `0` of the
logarithmic derivatives, whose Lambert series are DLMF 20.5.11 and 20.5.13.

## Main results

* `jacobiThetaThreeNullTau_pow_four_eq_lambert`: `θ₃(0|τ)⁴` by Lambert series in `q = e^{iπτ}`.
* `hasSum_jacobiThetaSeries_pow_four`: `ϑ(x)⁴ = ∑ (δ_{n0} + 8σ₁(n) - 32 σ₁(n/4)[4 ∣ n]) xⁿ`.
-/

@[expose] public noncomputable section

open Complex Filter Topology DLMF.Elliptic DLMF.Theta
open scoped Real ArithmeticFunction.sigma

namespace DLMF.NumberTheory

/-- For an entire `f` with `f(0) ≠ 0` and `f'(0) = 0`, `(f'/f)(x)/x → f''(0)/f(0)` as real
`x → 0`. -/
private lemma tendsto_logDeriv_div {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (h1 : deriv f 0 = 0) :
    Tendsto (fun x : ℝ => deriv f x / f x / x) (𝓝[≠] 0)
      (𝓝 (deriv (deriv f) 0 / f 0)) := by
  have hf' : DifferentiableAt ℂ (deriv f) 0 := ((hf.analyticAt 0).deriv).differentiableAt
  have hS := hf'.hasDerivAt.div (hf 0).hasDerivAt h0
  rw [h1] at hS
  have hS' : HasDerivAt (fun z => deriv f z / f z) (deriv (deriv f) 0 / f 0) 0 := by
    convert hS using 1; field_simp; ring
  have ht := hS'.tendsto_slope_zero
  have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have := ht.comp hmap
  refine this.congr fun x => ?_
  simp [h1, div_eq_inv_mul, mul_comm]

/-- Termwise limit `∑ c_k sin(2(k+1)x)/x → ∑ 2(k+1) c_k` as real `x → 0`, under the dominating
bound `∑ ‖c_k‖ 2(k+1) < ∞`. -/
private lemma tendsto_tsum_sin_div {c : ℕ → ℂ} (hc : Summable fun k : ℕ => ‖c k‖ * (2 * (k + 1))) :
    Tendsto (fun x : ℝ => (∑' k : ℕ, c k * sin (2 * ((k : ℂ) + 1) * x)) / x) (𝓝[≠] 0)
      (𝓝 (∑' k : ℕ, c k * (2 * ((k : ℂ) + 1)))) := by
  have hpt : ∀ k : ℕ, Tendsto (fun x : ℝ => c k * sin (2 * ((k : ℂ) + 1) * x) / x) (𝓝[≠] 0)
      (𝓝 (c k * (2 * ((k : ℂ) + 1)))) := by
    intro k
    set a : ℝ := 2 * ((k : ℝ) + 1)
    have hd : HasDerivAt (fun x : ℝ => Real.sin (a * x)) a 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul a).sin
      simpa using this
    have ht := hd.tendsto_slope_zero
    have ht' := (Complex.continuous_ofReal.tendsto a).comp ht
    have := ht'.const_mul (c k)
    refine (this.congr fun x => ?_).trans (by push_cast [a]; exact le_rfl)
    simp only [Function.comp_apply, zero_add, mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
    push_cast [a]
    field_simp
  have hb : ∀ᶠ x : ℝ in 𝓝[≠] 0, ∀ k : ℕ,
      ‖c k * sin (2 * ((k : ℂ) + 1) * x) / x‖ ≤ ‖c k‖ * (2 * (k + 1)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx k
    have hx0 : x ≠ 0 := hx
    rw [show (2 * ((k : ℂ) + 1) * x) = ((2 * ((k : ℝ) + 1) * x : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_sin, norm_div, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_div_assoc]
    gcongr
    rw [div_le_iff₀ (abs_pos.mpr hx0)]
    refine (Real.abs_sin_le_abs).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((k : ℝ) + 1))]
  have := tendsto_tsum_of_dominated_convergence hc hpt hb
  refine this.congr fun x => ?_
  rw [tsum_div_const]


/-- The dominating bound for the Lambert-type coefficients of the log-derivatives of `θ₂`, `θ₄`. -/
private lemma summable_lambert_bound {E : ℂ} (hE : ‖E‖ < 1) {m : ℕ} (hm : 1 ≤ m) (s : ℕ → ℂ)
    (hs : ∀ k, ‖s k‖ ≤ 1) :
    Summable fun k : ℕ =>
      ‖4 * s k * (E ^ (m * (k + 1)) / (1 - E ^ (2 * (k + 1))))‖ * (2 * (k + 1)) := by
  set r := ‖E‖
  have hr0 : 0 ≤ r := norm_nonneg E
  have hr1 : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hg0 : Summable fun k : ℕ => ((k : ℕ) : ℝ) ^ 1 * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr1
  have hg1 : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 1 * r ^ (k + 1) :=
    (summable_nat_add_iff 1).mpr hg0
  have hg : Summable fun k : ℕ => 8 / (1 - r) * (((k + 1 : ℕ) : ℝ) ^ 1 * r ^ (k + 1)) :=
    hg1.mul_left _
  refine hg.of_nonneg_of_le (fun k => by positivity) fun k => ?_
  have hpow : ‖E ^ (m * (k + 1))‖ ≤ r ^ (k + 1) := by
    rw [norm_pow]
    exact pow_le_pow_of_le_one hr0 hE.le (by nlinarith)
  have hden : 1 - r ≤ ‖1 - E ^ (2 * (k + 1))‖ := by
    have h1 : ‖E ^ (2 * (k + 1))‖ ≤ r := by
      rw [norm_pow]; exact pow_le_of_le_one hr0 hE.le (by omega)
    have := norm_sub_norm_le (1 : ℂ) (E ^ (2 * (k + 1)))
    rw [norm_one] at this
    linarith
  have h1r : 0 < 1 - r := by linarith
  rw [norm_mul, norm_mul, norm_div]
  push_cast
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  calc 4 * ‖s k‖ * (‖E ^ (m * (k + 1))‖ / ‖1 - E ^ (2 * (k + 1))‖) * (2 * ((k : ℝ) + 1))
      ≤ 4 * 1 * (r ^ (k + 1) / (1 - r)) * (2 * ((k : ℝ) + 1)) := by
        gcongr
        · exact hs k
    _ = 8 / (1 - r) * (((k : ℝ) + 1) ^ 1 * r ^ (k + 1)) := by
        field_simp; ring

/-- Jacobi: `θ₃(0|τ)⁴ = (log θ₄)''(0) - (log θ₂)''(0)` written with the Lambert series of
DLMF 20.5.11 and 20.5.13 differentiated at `z = 0`:
`θ₃⁴ = 8 ∑ n qⁿ/(1 - q^{2n}) - (8 ∑ (-1)ⁿ n q^{2n}/(1 - q^{2n}) - 1)`, `q = e^{iπτ}`. -/
theorem jacobiThetaThreeNullTau_pow_four_eq_lambert {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ ^ 4 =
      (∑' k : ℕ, 4 * (cexp (π * I * τ) ^ (k + 1) / (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) *
        (2 * ((k : ℂ) + 1))) -
      ((∑' k : ℕ, 4 * (-1 : ℂ) ^ (k + 1) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * (2 * ((k : ℂ) + 1))) - 1) := by
  set E := cexp (π * I * τ) with hE
  set f1 := fun z => jacobiThetaOneTau z τ
  set f2 := fun z => jacobiThetaTwoTau z τ
  set f4 := fun z => jacobiThetaFourTau z τ
  have d1 : Differentiable ℂ f1 := differentiable_jacobiThetaTau 1 hτ
  have d2 : Differentiable ℂ f2 := differentiable_jacobiThetaTau 2 hτ
  have d4 : Differentiable ℂ f4 := differentiable_jacobiThetaTau 4 hτ
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero hτ
  have hE1 := norm_nome_lt_one hτ
  -- first derivatives vanish at 0
  have h4' : deriv f4 0 = 0 := by
    have := (jacobiThetaFourTau_logDeriv (z := 0) hτ (by simp; positivity)).2
    simp only [mul_zero, Complex.sin_zero] at this
    have h := this.unique hasSum_zero
    rwa [div_eq_zero_iff, or_iff_left n4] at h
  have h2' : deriv f2 0 = 0 := by
    have := (jacobiThetaTwoTau_logDeriv (z := 0) hτ (by simp; positivity)).2
    simp only [mul_zero, Complex.sin_zero, Complex.tan_zero, add_zero] at this
    have h := this.unique hasSum_zero
    rwa [div_eq_zero_iff, or_iff_left n2] at h
  have hb4 := summable_lambert_bound hE1 le_rfl (fun _ => 1) (fun _ => by simp)
  have hb2 := summable_lambert_bound hE1 (by norm_num : 1 ≤ 2) (fun k => (-1 : ℂ) ^ (k + 1))
    (fun _ => by simp)
  simp only [one_mul, mul_one] at hb4
  -- second derivative of θ₄ at 0
  have L4 : deriv (deriv f4) 0 / f4 0 = ∑' k : ℕ, 4 * (E ^ (k + 1) / (1 - E ^ (2 * (k + 1)))) *
      (2 * ((k : ℂ) + 1)) := by
    refine tendsto_nhds_unique (tendsto_logDeriv_div d4 n4 h4') ?_
    refine (tendsto_tsum_sin_div hb4).congr fun x => ?_
    rw [((jacobiThetaFourTau_logDeriv (z := x) hτ (by simp; positivity)).2).tsum_eq]
  have htan : Tendsto (fun x : ℝ => Complex.tan x / x) (𝓝[≠] 0) (𝓝 1) := by
    have hd : HasDerivAt Complex.tan 1 0 := by
      simpa using Complex.hasDerivAt_tan (x := 0) (by simp)
    have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    refine (hd.tendsto_slope_zero.comp hmap).congr fun x => ?_
    simp [div_eq_inv_mul]
  have L2 : deriv (deriv f2) 0 / f2 0 = (∑' k : ℕ, 4 * (-1 : ℂ) ^ (k + 1) *
      (E ^ (2 * (k + 1)) / (1 - E ^ (2 * (k + 1)))) * (2 * ((k : ℂ) + 1))) - 1 := by
    refine tendsto_nhds_unique (tendsto_logDeriv_div d2 n2 h2') ?_
    refine ((tendsto_tsum_sin_div hb2).sub htan).congr fun x => ?_
    rw [((jacobiThetaTwoTau_logDeriv (z := x) hτ (by simp; positivity)).2).tsum_eq, add_div,
      add_sub_cancel_right]
  -- differentiate the identity 20.7.3 twice
  have hid : ∀ z, jacobiThetaTwoNullTau τ ^ 2 * f4 z ^ 2 =
      jacobiThetaThreeNullTau τ ^ 2 * f1 z ^ 2 + jacobiThetaFourNullTau τ ^ 2 * f2 z ^ 2 :=
    fun z => jacobiTheta_sq_two_four z τ hτ
  have hsq : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → ∀ z,
      HasDerivAt (fun w => f w ^ 2) (2 * f z * deriv f z) z := fun hf z => by
    convert (hf z).hasDerivAt.pow 2 using 1; push_cast; ring
  have hd1 : ∀ z, jacobiThetaTwoNullTau τ ^ 2 * (2 * f4 z * deriv f4 z) =
      jacobiThetaThreeNullTau τ ^ 2 * (2 * f1 z * deriv f1 z) +
        jacobiThetaFourNullTau τ ^ 2 * (2 * f2 z * deriv f2 z) := by
    intro z
    have hl := (hsq d4 z).const_mul (jacobiThetaTwoNullTau τ ^ 2)
    have hr := ((hsq d1 z).const_mul (jacobiThetaThreeNullTau τ ^ 2)).add
      ((hsq d2 z).const_mul (jacobiThetaFourNullTau τ ^ 2))
    rw [show (fun w => jacobiThetaTwoNullTau τ ^ 2 * f4 w ^ 2) =
      (fun w => jacobiThetaThreeNullTau τ ^ 2 * f1 w ^ 2 +
        jacobiThetaFourNullTau τ ^ 2 * f2 w ^ 2) from funext hid] at hl
    exact hl.unique hr
  have hdd : ∀ {f : ℂ → ℂ}, Differentiable ℂ f →
      HasDerivAt (fun w => 2 * f w * deriv f w)
        (2 * deriv f 0 * deriv f 0 + 2 * f 0 * deriv (deriv f) 0) 0 := fun hf =>
    ((hf 0).hasDerivAt.const_mul 2).mul (((hf.analyticAt 0).deriv).differentiableAt.hasDerivAt)
  have hd2 := ((hdd d4).const_mul (jacobiThetaTwoNullTau τ ^ 2))
  have hr2 := ((hdd d1).const_mul (jacobiThetaThreeNullTau τ ^ 2)).add
      ((hdd d2).const_mul (jacobiThetaFourNullTau τ ^ 2))
  rw [show (fun w => jacobiThetaTwoNullTau τ ^ 2 * (2 * f4 w * deriv f4 w)) =
      (fun w => jacobiThetaThreeNullTau τ ^ 2 * (2 * f1 w * deriv f1 w) +
        jacobiThetaFourNullTau τ ^ 2 * (2 * f2 w * deriv f2 w)) from funext hd1] at hd2
  have key := hd2.unique hr2
  have hf10 : f1 0 = 0 := DLMF.JacobiElliptic.jacobiThetaOneTau_zero τ
  have hf1' : deriv f1 0 = jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ *
      jacobiThetaFourNullTau τ := jacobiThetaOneDerivNullTau_eq_mul hτ
  rw [h4', h2', hf10, hf1'] at key
  rw [← L4, ← L2]
  have e4 : f4 0 = jacobiThetaFourNullTau τ := rfl
  have e2 : f2 0 = jacobiThetaTwoNullTau τ := rfl
  rw [e4, e2]
  rw [e4, e2] at key
  rw [div_sub_div _ _ n4 n2, eq_div_iff (mul_ne_zero n4 n2)]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero n2) n4)
  linear_combination -key

/-! ### Power series in `x` -/

/-- `θ₃(0|τ) = ϑ(e^{iπτ})` for `Im τ > 0`. -/
private lemma jacobiThetaThreeNullTau_eq_jacobiThetaSeries {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ = jacobiThetaSeries (cexp (π * I * τ)) := by
  rw [jacobiThetaThreeNullTau, jacobiThetaThreeTau, zero_div, ← jacobiTheta_eq_jacobiTheta₂]
  exact jacobiTheta_eq_jacobiThetaSeries hτ

/-- The divisor-sum power series `∑ σ₁(n) yⁿ`, `‖y‖ < 1`. -/
private lemma summable_sigma_mul_pow {y : ℂ} (hy : ‖y‖ < 1) :
    Summable fun n : ℕ => (σ 1 n : ℂ) * y ^ n := by
  refine (summable_norm_pow_mul_geometric_of_norm_lt_one 2 hy).of_norm_bounded fun n => ?_
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n

/-- Lambert series: `∑_{n≥1} n yⁿ/(1 - yⁿ) = ∑_{n≥1} σ₁(n) yⁿ`, `‖y‖ < 1`. -/
private lemma hasSum_lambert_sigma {y : ℂ} (hy : ‖y‖ < 1) :
    HasSum (fun k : ℕ => ((k : ℂ) + 1) * y ^ (k + 1) / (1 - y ^ (k + 1)))
      (∑' n : ℕ, (σ 1 n : ℂ) * y ^ n) := by
  have hs0 := summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℂ) 1 hy
  have hs : Summable fun k : ℕ => ((k + 1 : ℕ) : ℂ) ^ 1 * y ^ (k + 1) / (1 - y ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr hs0
  have he := tsum_pow_div_one_sub_eq_tsum_sigma hy 1
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℂ) ^ 1 * y ^ n / (1 - y ^ n)),
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (σ 1 n : ℂ) * y ^ n)] at he
  rw [(summable_sigma_mul_pow hy).tsum_eq_zero_add]
  simp only [ArithmeticFunction.map_zero, Nat.cast_zero, zero_mul, zero_add]
  rw [← he]
  convert hs.hasSum using 2 with k
  push_cast; ring

/-- `ϑ(x)⁴ = 1 + 8 ∑ σ₁(n) xⁿ - 32 ∑ σ₁(n) x^{4n}` for `0 < ‖x‖ < 1`. -/
private lemma jacobiThetaSeries_pow_four_eq {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    jacobiThetaSeries x ^ 4 = 1 + 8 * ∑' n : ℕ, (σ 1 n : ℂ) * x ^ n -
      32 * ∑' n : ℕ, (σ 1 n : ℂ) * (x ^ 4) ^ n := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set τ := Complex.log x / (π * I) with hτdef
  have hπI : (π : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  have hE : cexp (π * I * τ) = x := by
    rw [hτdef, mul_div_cancel₀ _ hπI, Complex.exp_log hx0]
  have hτ : 0 < τ.im := by
    have : τ = -(I * Complex.log x) / π := by
      rw [hτdef]; field_simp; rw [I_sq]; ring
    rw [this, neg_div, neg_im, div_ofReal_im, mul_im, I_re, I_im, Complex.log_re]
    have : Real.log ‖x‖ < 0 := Real.log_neg hpos hx
    have hπ := Real.pi_pos
    simp only [zero_mul, one_mul, zero_add]
    rw [neg_pos]
    exact div_neg_of_neg_of_pos this hπ
  have hA := jacobiThetaThreeNullTau_pow_four_eq_lambert hτ
  rw [jacobiThetaThreeNullTau_eq_jacobiThetaSeries hτ, hE] at hA
  rw [hA]
  have h2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)
  have h4 : ‖(x ^ 2) ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h2 (by norm_num)
  set P := fun y : ℂ => ∑' n : ℕ, (σ 1 n : ℂ) * y ^ n with hPdef
  have hne : ∀ {y : ℂ}, ‖y‖ < 1 → ∀ k : ℕ, 1 - y ^ (k + 1) ≠ 0 := by
    intro y hy k h
    have : ‖y ^ (k + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hy (by omega)
    rw [← sub_eq_zero.mp h, norm_one] at this
    exact lt_irrefl _ this
  -- the first Lambert series
  have hL4 : HasSum (fun k : ℕ => 4 * (x ^ (k + 1) / (1 - x ^ (2 * (k + 1)))) *
      (2 * ((k : ℂ) + 1))) (8 * P x - 8 * P (x ^ 2)) := by
    convert ((hasSum_lambert_sigma hx).mul_left 8).sub
      ((hasSum_lambert_sigma h2).mul_left 8) using 1
    funext k
    have e1 := hne hx k
    have e2 := hne h2 k
    have e3 : 1 + x ^ (k + 1) ≠ 0 := by
      intro h
      have : ‖x ^ (k + 1)‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by omega)
      rw [show x ^ (k + 1) = -1 by linear_combination h, norm_neg, norm_one] at this
      exact lt_irrefl _ this
    rw [← pow_mul, mul_comm 2 (k + 1), pow_mul] at e2 ⊢
    rw [show 1 - (x ^ (k + 1)) ^ 2 = (1 - x ^ (k + 1)) * (1 + x ^ (k + 1)) by ring] at e2 ⊢
    field_simp
    ring
  -- the second Lambert series, split into even and odd indices
  set y := x ^ 2 with hy
  set b : ℕ → ℂ := fun k => ((k : ℂ) + 1) * y ^ (k + 1) / (1 - y ^ (k + 1)) with hb
  have hbs : HasSum b (P y) := hasSum_lambert_sigma h2
  have hodd : HasSum (fun j : ℕ => b (2 * j + 1)) (2 * P (y ^ 2)) := by
    convert (hasSum_lambert_sigma h4).mul_left 2 using 1
    funext j
    simp only [hb]
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]
    push_cast
    ring
  have heven : HasSum (fun j : ℕ => b (2 * j)) (P y - 2 * P (y ^ 2)) := by
    have hs : Summable fun j : ℕ => b (2 * j) :=
      hbs.summable.comp_injective (mul_right_injective₀ two_ne_zero)
    have := hs.hasSum.even_add_odd hodd
    rw [hbs.unique this, add_sub_cancel_right]
    exact hs.hasSum
  have hL2 : HasSum (fun k : ℕ => 4 * (-1 : ℂ) ^ (k + 1) * (x ^ (2 * (k + 1)) /
      (1 - x ^ (2 * (k + 1)))) * (2 * ((k : ℂ) + 1))) (8 * (4 * P (y ^ 2) - P y)) := by
    have hsplit : HasSum (fun k : ℕ => (-1 : ℂ) ^ (k + 1) * b k)
        (-(P y - 2 * P (y ^ 2)) + 2 * P (y ^ 2)) := by
      refine HasSum.even_add_odd ?_ ?_
      · convert heven.neg using 1
        funext j
        rw [pow_succ, pow_mul]; simp
      · convert hodd using 1
        funext j
        rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]; simp
    convert hsplit.mul_left 8 using 1
    · funext k
      simp only [hb, hy]
      rw [← pow_mul]
      ring
    · ring
  rw [hL4.tsum_eq, hL2.tsum_eq]
  simp only [hPdef, hy, ← pow_mul]
  ring

/-- DLMF §27.13(iv) (Jacobi): `ϑ(x)⁴ = ∑ (δ_{n0} + 8σ₁(n) - 32 σ₁(n/4)[4 ∣ n]) xⁿ`, `|x| < 1`;
equivalently `r₄(n) = 8 ∑_{d ∣ n, 4 ∤ d} d` for `n ≥ 1`. -/
theorem hasSum_jacobiThetaSeries_pow_four {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ((if n = 0 then 1 else 0) + 8 * (σ 1 n : ℂ) -
        32 * (if 4 ∣ n then (σ 1 (n / 4) : ℂ) else 0)) * x ^ n)
      (jacobiThetaSeries x ^ 4) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have h0 : jacobiThetaSeries 0 = 1 := by simp [jacobiThetaSeries]
    rw [h0]
    convert hasSum_single (f := fun n : ℕ => ((if n = 0 then 1 else 0) + 8 * (σ 1 n : ℂ) -
        32 * (if 4 ∣ n then (σ 1 (n / 4) : ℂ) else 0)) * (0 : ℂ) ^ n) 0 (fun n hn => by
      simp [hn]) using 1
    simp
  have h4 : ‖x ^ 4‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)
  have hP := (summable_sigma_mul_pow hx).hasSum
  have hP4 : HasSum (fun n : ℕ => (if 4 ∣ n then (σ 1 (n / 4) : ℂ) else 0) * x ^ n)
      (∑' n : ℕ, (σ 1 n : ℂ) * (x ^ 4) ^ n) := by
    have hinj : Function.Injective fun n : ℕ => 4 * n := fun a b h => by simpa using h
    rw [← hinj.hasSum_iff]
    · convert (summable_sigma_mul_pow h4).hasSum using 1
      funext n
      simp [← pow_mul]
    · intro N hN
      have : ¬ 4 ∣ N := by rintro ⟨n, rfl⟩; exact hN ⟨n, rfl⟩
      simp [this]
  have hδ : HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ) else 0) * x ^ n) 1 := by
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    funext n
    split_ifs with h <;> simp [h]
  rw [jacobiThetaSeries_pow_four_eq hx0 hx]
  convert (hδ.add (hP.mul_left 8)).sub (hP4.mul_left 32) using 1
  funext n
  ring

end DLMF.NumberTheory
